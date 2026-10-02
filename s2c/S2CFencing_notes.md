# S2C with log fencing

This document accompanies [S2CFencing.tla](./S2CFencing.tla). It describes the motivation for the fencing variant and how it prevents the GC consistency violation in [S2C.tla](./S2C.tla). The underlying leadership, write, snapshot, and replication protocol is described in [S2C_notes.md](./S2C_notes.md).

## Motivation

In the original protocol, a leader reserves a batch index by updating `leaderState`, then creates the batch at that index using put-if-absent. A leadership change can occur between these two writes, leaving the old leader with a pending write at the reserved address.

The new leader is allowed to fill that reservation with its own data batch. While the batch exists, it blocks the old leader's write. But after snapshotting and GC, the address becomes free again. The old leader can then successfully write behind the snapshot boundary, apply its values locally, and report success even though snapshot-based recovery will omit those values.

The missing protection is a lasting barrier at the address where the old leader can still write. Updating the leader epoch alone cannot provide that barrier: the old leader has already passed its metadata CAS, and its pending log creation does not check the current epoch.

## Fence the outstanding reservation

The variant introduces two log record kinds:

- `DATA` contains application values.
- `FENCE` contains no application values and occupies a log index to block a stale write.

When a new leader finishes recovery exactly one index behind `commitIndex`, it enters `[FENCE_FIRST_INDEX]`. Instead of reusing the outstanding reservation for its first application batch, `FenceFirstIndex` attempts to create:

```text
log[commitIndex] = [kind        |-> FENCE,
                    entries     |-> <<>>,
                    commitIndex |-> commitIndex]
```
> Note that `entries` and `commitIndex` are not actually required, it just makes the TLA+ in other places simpler.

The write uses put-if-absent, so it races with the old leader's pending data write:

- **The fence wins:** the old leader's data write encounters an occupied address and fails. The new leader then validates its leadership before becoming ready.
- **The data write wins:** the fence write fails and the new leader returns to `[REFRESH]` to rejoin based on the fresh metadata. If it remains leader, it recovers the winning data batch before accepting new commands.

If recovery already reaches the reservation boundary, no fence is needed for that reservation: the batch has been written and can be recovered.

A fence consumes an index but adds nothing to the application state or successful-write history. Replaying its empty `entries` advances the apply index without applying a command to the local machine data. Once the fence is validated, the new leader's first data batch reserves `commitIndex + 1` through the normal metadata CAS. The `rReuseFirstIndex` variable is completely omitted in this variant.

## Validate after writing the fence

A successful fence creation is not sufficient by itself. The replica attempting to fence may also have become stale while it was paused. Another leader could have filled the address with data, snapshotted it, and allowed GC to delete it. The stale replica's fence creation would then succeed at a recycled address.

`PostFenceValidate` checks that the replica's cached leader-state version still equals the stored version:

- If it matches, the replica advances its apply index over the empty fence, marks itself joined, and enters `[READY]`.
- If it differs, the replica enters `[REFRESH]` for a rejoin without advancing its applied state.

```text
[CATCHUP]
    |
(missing trailing reservation)
    |
[FENCE_FIRST_INDEX]
    |
FenceFirstIndex--------------+
    |                        |
(address occupied)      (success, address free)
    |                        |
    v                        v
[REFRESH]          [POST_FENCE_VALIDATE]
                             |
                      PostFenceValidate
                         /         \
               (leaderState     (version current)
              version changed)       |
                     |               |
                     v               v
                 [REFRESH]        [READY]
```

This validation prevents a recycled address from being mistaken for successful fencing.

## Keep fences when collecting data

`GarbageCollect` only deletes records satisfying both conditions:

```text
index < snapshot.applyIndex
log[index].kind = DATA
```

**Fence records are never deleted in this model**, including fences below the snapshot boundary. Their application contents are empty, but their continued existence is what rejects stale put-if-absent writes.

Revisiting the original counterexample illustrates the difference:

| Step | With fencing |
| --- | --- |
| `r1` reserves index 1 for `A`, then pauses. | Index 1 is reserved but unwritten. |
| `r2` takes leadership and recovers. | It creates a `FENCE` at index 1 and validates its leader-state version. |
| `r2` writes `B` and `C`. | The data batches occupy indexes 2 and 3. |
| `r2` snapshots through index 3. | The snapshot contains `<<B, C>>`; the fence contributes no values. |
| GC runs. | It may delete data batch 2, but must retain fence 1. |
| `r1` resumes its write of `A` at index 1. | Put-if-absent fails because fence 1 still exists. `A` is neither applied nor recorded as a successful write. |

## Similarity to SlateDB

This uses the same fencing style as the [SlateDB WAL model](../slatedb/SlateDBWAL.tla): create a fence object in the numbered WAL address space so that a stale writer's conditional creation fails when it reaches that address. The fence remains useful after all earlier application data has been incorporated into a snapshot or flushed state. The local SlateDB model likewise restricts WAL deletion to `DATA` objects and retains fences.

The placement differs: S2C already has a CAS-protected reservation boundary, so it fences the missing trailing reservation discovered during recovery. SlateDB's writer initialization searches for an available WAL position and installs a fence there. Both depend on fencing the next address that blocks the stale writer from making progress.

SlateDB treats fence GC separately from ordinary WAL GC through its `wal-fence` GC task. Fence deletion is dry-run by default, so fences are retained unless deletion is explicitly enabled. If enabled, its minimum age must be longto prevent a delayed writer from resuming after its fence has disappeared. See [SlateDB's garbage-collection documentation](https://slatedb.io/docs/tutorials/standalone-garbage-collector/).

`S2CFencing.tla` models indefinite FENCE object retention.