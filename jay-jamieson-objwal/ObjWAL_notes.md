# Objwal: Single-writer, epoch-fenced WAL protocol

This document accompanies [ObjWAL.tla](./ObjWAL.tla), a simplified specification of a stateful application built on [objwal](https://github.com/JayJamieson/objwal).

The specification focuses on the safety mechanics of publishing, recovering, and snapshotting a write-ahead log in object storage. It is not a line-by-line model of the Go implementation. In particular, it combines objwal's low-level primitives with the application-owned state machine and snapshot orchestration needed to build a complete stateful service.

## Replica model

In this specification, a **replica** is a complete stateful application instance. It is not merely an instance of objwal's `wal.Replica` reader type.

Every replica has three logical components:

- The **producer** claims the manifest epoch and, while it remains the current writer, buffers values, uploads segments, and appends segment references to the manifest.
- The **application state machine** restores a snapshot, replays the WAL, and maintains the replica's local materialized state.
- The **snapshotter** writes a checkpoint of the local state, publishes its reference in the manifest, and trims manifest entries covered by it.

These components are separated into actions so that their responsibilities and interleavings are visible. They may all run in the same process and share the same replica-local state. A replica first acts as a producer to fence other replica, then as a reader while recovering, then acts as the producer again once reached `READY`, and can snapshot its own state while it owns the current epoch.

The model permits several replica processes to overlap during failover, but only the replica holding the current manifest epoch may successfully modify the committed log. Older replicas can continue far enough to upload unreferenced objects, but they are fenced before they can publish them in the manifest.

## Durable state in S3

The system stores three kinds of durable data in object storage:

- A mutable **manifest** defines the committed WAL and current writer epoch.
- Immutable **segments** contain sequences of application values.
- Immutable **snapshots** contain complete materialized application state through a particular sequence number.

The manifest is the source of truth. A segment or snapshot object that exists in storage but is not referenced by the manifest is not part of the recoverable committed state.

### Manifest

The manifest contains:

- `epoch`: the fencing generation of the current producer;
- `version`: the revision used for compare-and-swap updates;
- `nextSeq`: the sequence number that will be assigned to the next committed value;
- `snapshotSeq`: the inclusive upper sequence represented by the current snapshot, or zero when there is no snapshot;
- `entries`: an ordered sequence of segment references.

Each manifest entry contains:

- `seq`: the first sequence number represented by the segment;
- `count`: the number of values in the segment;
- `id`: the physical segment identifier.

An entry therefore owns the inclusive sequence range:

```text
entry.seq .. entry.seq + entry.count - 1
```

The specification uses one-based WAL sequence numbers. The real objwal implementation uses zero-based record sequences, but the offset does not affect the protocol.

### Segments

A segment contains only a sequence of values. Sequence numbers are not embedded in the segment. The manifest entry assigns the segment its logical position in the WAL.

Segment addresses are modeled as:

```text
<<replica, ordinal>>
```

This represents objwal's physical key scheme: `<segment-prefix>/<producer-run-id>/<ordinal>`, e.g.

```text
wal/seg/jhgdfg/000000000001
wal/seg/jhgdfg/000000000002
wal/seg/jhgdfg/000000000003
```

The ordinal starts at zero and advances after each successful segment commit. It is local to one producer run and is not the segment's first WAL sequence number. Namespacing the ordinal by replica/run lets an old and a new producer upload concurrently without contending for the same object address.

### Snapshots

Snapshots are addressed by their inclusive `snapshotSeq` in this model. A snapshot at sequence `n` contains exactly the committed history through `n`.

The concrete objwal manifest stores an explicit snapshot location as well as its through-sequence and creation time. The model omits the separate location and treats the sequence as the address.

## State progress and liveness

The spec has two terminal states for each replica: READY (for writes) and PREEMPTED (after a replica sees that its epoch is stale).

During the initialization phase, any conflict will cause the replica to restart where it can try to initialize again. After an epoch has been claimed, any conflict will cause it to transition to PREEMPTED, where it will stay forever. So, replicas can battle it out for control, but once a writer with an established epoch has lost control, it stops. This allows us to model competing replicas and keep liveness checks simple.

## Transitions

### Producer initialization and recovery

`InitializeProducer` reads the current manifest and moves a replica from `[IDLE]` to `[CLAIM_MANIFEST]`.

`ClaimManifest` tries to CAS a manifest whose epoch and version are each one greater than the cached values:

- If the cached version is stale, the claim fails and the replica returns to `[IDLE]` to retry initialization.
- If the CAS succeeds, the replica owns the new epoch and the app can begin recovery.

Unlike `wal.NewProducer` by itself, the modeled stateful application does not accept writes immediately after claiming. It first restores the application state represented by the manifest it claimed.

```text
[IDLE]
   |
InitializeProducer
   v
[CLAIM_MANIFEST]
   |          |
(conflict)  (success)
   |          | 
   v          v
[IDLE]     [SNAPSHOT_RECOVERY]
                     |
              SnapshotRecovery
                     |
                     v
                [REPLAY_WAL]
                     |
            ReplayWAL (repeat)
                     |
                     v
                  [READY]
```

`SnapshotRecovery` replaces local machine state with the referenced snapshot when one exists and sets `rReplaySeq` to the first sequence after it. With no snapshot, recovery starts from sequence one.

`ReplayWAL` finds the manifest entry beginning at `rReplaySeq`, reads its segment, appends the segment values to local machine state, and advances by the entry's `count`. Once `rReplaySeq = manifest.nextSeq`, recovery is complete and the replica becomes `[READY]`.

A competing replica may claim a newer epoch while recovery is running. Recovery may finish against the older cached manifest, leaving a stale replica whose state is a committed prefix. Before that replica can append or snapshot, the corresponding validation action detects the epoch change and moves it permanently to `[PREEMPTED]`.

### Appending values

Appending is split into buffering, segment upload, epoch validation, and manifest publication.

`AppendValueLocally` accepts one previously unused model value and appends it to `rPendingSeg`. Repeated invocations allow several values to accumulate in one pending segment.

The finite set of unique `Values` is a state-space simplification. Real objwal accepts duplicate byte payloads and identifies operations independently of their contents.

`WriteSegment` uploads the buffered values at the replica's current segment ordinal. The segment is not yet committed and its values do not yet have durable WAL positions.

The replica then enters `[PREAPPEND_VALIDATE]`. `PreAppendValidate` refreshes the manifest and ...:

- If the cached epoch differs from the stored epoch, the replica becomes `[PREEMPTED]`.
- If the epoch is unchanged, it adopts the latest manifest version and proceeds to `[APPEND_TO_MANIFEST]`.

`AppendToManifest` constructs one entry using the current manifest `nextSeq`, the number of pending values, and the uploaded segment identifier. It then performs a version-based CAS.

On success, the action atomically:

- appends the segment reference;
- advances `nextSeq` by the segment count;
- increments the manifest version;
- applies the pending values to local machine state;
- records them in the auxiliary committed history;
- clears the pending segment;
- advances the replica's segment ordinal;
- returns the replica to `[READY]`.

On a version conflict, the uploaded segment remains in storage and the replica returns to `[PREAPPEND_VALIDATE]`. It refreshes the manifest and either retries under the same epoch or becomes fenced by a newer one.

```text
                  AppendValueLocally
                +--------------------+
                |                    |
                v                    |
             [READY]-----------------+
                |
          WriteSegment
                |
                v
      [PREAPPEND_VALIDATE]
          |             |
 (epoch changed)   (epoch current)
          |             |
          v             |
    [PREEMPTED]         |
      ^                 |
      |                 |
  (invalid)             |
      |                 v
      +--(valid)-->[APPEND_TO_MANIFEST]
      |              |            |
      |          (conflict)    (success)
      |              |            |
      |              v            v
      +---[PREAPPEND_VALIDATE]  [READY]
```

The successful manifest CAS is the commit and ordering point. Upload completion order and segment ordinals do not define logical WAL order.

## Snapshotting

Snapshotting is performed by the same stateful replica that currently owns the producer epoch.

`PrepareSnapshot` is enabled in `[READY]` when the committed head is ahead of the current manifest snapshot and no snapshot object already occupies the chosen address. It chooses:

```text
snapshotSeq = manifest.nextSeq - 1
```

Thus this model snapshots the complete committed state at the current head. Snapshotting and appending by the same replica do not overlap because both are represented through `rState`. This is a simplifying choice; a concrete application could take an MVCC checkpoint while continuing to append.

`PreSnapshotValidate` refreshes the manifest and performs the same epoch check as append validation. A stale snapshotter becomes `[PREEMPTED]` before it can publish obsolete state.

`WriteSnapshot` uses put-if-absent semantics at the address determined by `snapshotSeq`:

- If the address is free, it stores `rMachineData` and proceeds to `[COMMIT_SNAPSHOT]`.
- If an object already exists there, it abandons this attempt and returns to `[READY]`.

`CommitSnapshot` constructs a manifest that:

- points `snapshotSeq` at the new snapshot;
- removes manifest entries covered by that snapshot;
- preserves the producer epoch and `nextSeq`;
- increments the manifest version.

The manifest CAS atomically publishes the snapshot and truncation. Until it succeeds, the uploaded snapshot is merely an unreferenced object.

On a CAS conflict, the replica returns to `[PRESNAPSHOT_VALIDATE]` to refresh and recheck its epoch. In the current state machine, revisiting `WriteSnapshot` finds the already-written snapshot address occupied and returns to `[READY]`; the object remains unreferenced. If the conflict was caused by a newer epoch, validation instead moves the replica to `[PREEMPTED]`.

```text
              [READY]
                 |
          PrepareSnapshot
                 |
                 v
      [PRESNAPSHOT_VALIDATE]
          |              |
  (epoch changed)   (epoch current)
          |              |
          v              v
    [PREEMPTED]   [WRITE_SNAPSHOT]
        |           |         |
        |   (address used) (write succeeds_
        |           |         |
        |           v         |
        |        [READY]      |
(epoch changed)               |
        |                     |
        |       +------->[COMMIT_SNAPSHOT]
        |       |            |          |
        |       |       (conflict)   (success)
        | (current epoch)    |          |
        |       |            v          v
        +---[PRESNAPSHOT_VALIDATE]   [READY]
```

## Garbage collection

Garbage collection is not modeled, matching objwal's current lack of an automatic retention implementation.

Manifest truncation removes references but does not delete segment objects. A correct external collector could delete:

- segments removed by a successfully committed snapshot;
- snapshots older than the currently referenced snapshot;
- uploaded segments and snapshots that were never referenced (somehow).

GC shouldn't involve any landmines as the live segments are defined by the manifest (not a numbered address space such as with SlateDB). So deleting an unreferenced segment file **should not cause** any correctness issue.

## Invariants

* `ValidWriters`: At least one modeled replica has not reached `[PREEMPTED]`. This is verifies that two or more writers can't preempt each other leaving no replica standing.
* `ConsistentMachineData`: Every `[READY]` replica has application state consistent with committed history
* `UniqueEpochs`: No two established replicas hold the same epoch. A successful claim always derives a fresh epoch from the current manifest.
* `ValidSnapshots`: Every stored snapshot is exactly a prefix of the auxiliary committed history through the snapshot's sequence number. This applies even to an uploaded snapshot that was never successfully referenced by the manifest.
* `ManifestRepresentsCommittedLog`: The manifest, referenced snapshot, and referenced segments are sufficient to reconstruct the complete committed history.