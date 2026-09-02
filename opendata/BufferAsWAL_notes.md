# Buffer modified to be a single-writer WAL

Two types of process:
* Writer (which writes to the WAL and maintains WAL-derived state)
* Garbage Collector, which can read the manifest but never updates it

Because only writers can modify the manifest and we only want one active writer, the manifest epoch is not required, just the manifest version.

Buffer relies on batch objects ids being ULIDs, for the GC algorithm to work. This spec simply models them as monotonic integers.

A writer must first initialize, where it tries to claim the manifest by bumping its version (fencing other existing writers), then loads the latest snapshot and replays the manifest entries until it is up to date. Then it transitions to READY and starts appending entries and writing snapshots.

## State progress and liveness

The spec has two terminal states for each writer: READY (for writes) and PREEMPTED (after a write conflict). During the initialization phase, any conflict will cause the writer to restart where it can try to initialize again. After initialization (once it has reached READY), any conflict will cause it to transition to PREEMPTED, where it will stay forever. So, writers can battle it out for control, but once an established writer has lost control, it stops. This allows us to model competing writers and keep liveness checks simple.

## Transitions

### Writer initialization and recovery

```text
  [IDLE] --Initialize --> [CLAIM_MANIFEST]
     ^                           |
     |                   ClaimManifest (CAS)
     |                           |
     |                    +----------+
     |                    |          |
     +--(stale manifest)--+      (succeeds)
                                     |
                                     v
                            [SNAPSHOT_RECOVERY]
                                 |    |
            (snapshot missing)---+    +--(snapshot read)--+
                     |                                    |
                     v                                    v
                   [IDLE]                       [CATCHUP_RECOVERY]<---------+
                                                    |  |    |               |
                                                    |  |    |               |
                            (batch missing)---------+  |    +--(batch read)-+
                                     |                 |         
                                     v             (caught up)
                                   [IDLE]              |
                                                       v
                                                     [READY]
```

`Initialize` reads the current manifest. A successful conditional write in `ClaimManifest` fences older writers and starts recovery. Missing recovery artifacts or a stale manifest restart the whole flow; catch-up reads manifest entries one at a time until the writer reaches `READY`.

If either the manifest or a batch is missing during initialization phase, the wrier restarts (as GC must have deleted old artifacts).

### Writer steady state

```text
  [READY] --WriteBatch--> [APPEND_TO_MANIFEST]
                                 |
                            AppendToManifest
                    (succeeds) |        | (conflict)
                               v        v
                            [READY]   [PREEMPTED]

  [READY] --WriteSnapshot--> [COMMIT_SNAPSHOT]
                                    |
                              CommitSnapshot
                      (succeeds) |      | (conflict)
                                 v      v
                             [READY]  [PREEMPTED]
```

From `READY`, a writer can append a batch or write a snapshot. The following manifest update is conditional: success returns the writer to `READY`, while a conflict permanently fences it in `PREEMPTED`.

### Garbage collection

```text
  [IDLE] --GcStart (read manifest)--> [DELETE]

  [DELETE] --DeleteBatch --> [DELETE]
  [DELETE] --DeleteSnapshot --> [DELETE]
  [DELETE] --GcStart --> [DELETE]
```

The collector remains in `DELETE`. It removes batches below `tsFloor` and
snapshots below `snapshotSeq`; once neither kind is eligible, `GcStart`
refreshes its local manifest and begins another pass.