# Shared Storage Consensus (S2C): Leader-follower replication over object storage

This document accompanies [S2C.tla](./S2C.tla), a simplified specification of Shared Storage Consensus. It describes the protocol represented by this model, including its consistency violation when garbage collection is enabled. The fencing variant, [S2CFencing.tla](./S2CFencing.tla), will be covered separately.

The specification focuses on leadership changes, durable batch writes, recovery, follower synchronization, snapshotting, and garbage collection. It omits implementation sequence numbers, heartbeats, and some liveness optimizations. The discussion below follows the executable actions where comments in the specification differ from them.

## Replica model

A **replica** is a complete stateful application instance. Every replica maintains local application state, represented by `rMachineData`, and an applied batch index, `rApplyIndex`.

Replicas take one of two roles:

- The **leader** accepts commands, reserves batch indexes in shared metadata, writes batches to object storage, applies successful writes locally, and pushes batches to followers. It also takes snapshots.
- A **follower** applies batches received from the leader. It can bootstrap from the snapshot and log in object storage, but does not write replicated batches back to storage.

Followers are therefore not needed to make an individual batch durable. Successful log creation completes the modeled write without waiting for follower acknowledgments. Follower acknowledgments track replication progress.

Each replica caches the shared leadership metadata in `rLeaderState`. `IsLeader(r)` checks whether this **local copy** names the replica as leader. It does not check the current metadata in object storage. Multiple replicas can consequently believe they are leader at the same time, with different cached epochs and versions.

## Durable state in S3

The model stores three kinds of durable data:

- A mutable **leader state** object records leadership and the batch reservation boundary.
- A numbered **log** stores batches using put-if-absent writes.
- A mutable **snapshot** object stores materialized application state and its applied batch index.

Leadership metadata and snapshot metadata have independent versions. There is no atomic transaction spanning either of these objects and a log batch.

### Leader state

`leaderState` is initially `None`. Once created, it contains:

- `replica`: the current leader's identity;
- `epoch`: the leadership generation;
- `commitIndex`: the highest reserved batch index;
- `version`: the revision used for compare-and-swap updates.

Claiming leadership increments both `epoch` and `version`, preserving `commitIndex`. Reserving a new batch increments `commitIndex` and `version`, preserving the leader and epoch.

Despite its name, **`commitIndex` is a reservation boundary, not necessarily the last durably written batch**. The leader advances it before creating the corresponding log object. Recovery must therefore allow one missing batch at the trailing reserved index.

### Log batches

`log` maps a batch index to a record containing:

- `entries`: a nonempty sequence of application values;
- `commitIndex`: the batch's index.

Batch indexes start at one. The logical batch index is also the modeled object address:

```text
log[1] = [entries |-> <<A, B>>, commitIndex |-> 1]
log[2] = [entries |-> <<C>>,    commitIndex |-> 2]
```

Indexes count batches, while `rMachineData` contains their flattened values. Applying the two batches above gives `rApplyIndex = 2` and `rMachineData = <<A, B, C>>`.

An existing log object cannot be overwritten. However, once GC deletes it, put-if-absent can succeed at the same address again. Object existence is therefore both a data-retention mechanism and the condition that prevents competing writers from filling the same index.

### Snapshot

`snapshot` is initially `None`. A stored snapshot contains:

- `entries`: the complete materialized application state;
- `applyIndex`: the inclusive batch index represented by that state;
- `epoch`: the snapshotting replica's cached leadership epoch;
- `version`: the snapshot object's own CAS revision.

The model represents the snapshot as one conditionally replaced object, with its contents and metadata written atomically. Each replica caches only its snapshot index and version in `rSnapshot`.

Recovery combines the snapshot with log batches **strictly above** its `applyIndex`. Log objects at or below that index are already covered and are not replayed after restoring the snapshot.

## State progress and liveness

`READY` means a replica has completed joining and can act in its local role. It is not a terminal state. Replicas can attempt leadership, detect a leadership change, return to recovery, or encounter a write conflict.

`ILLEGAL_STATE` records a recovery gap before the final reserved index.

`Spec` checks safety without requiring progress. `LivenessSpec` adds weak fairness for joining, leadership changes, message handling, committing writes, synchronization, and snapshot commit. It does not require command reception, snapshot preparation, or GC to occur.

`MaxEpoch` bounds leadership attempts to limit the explored state space. The liveness properties describe eventual joining and convergence on this bounded final epoch; they do not assert that every submitted command completes.

## Transitions

### Join process

When a replica starts, or after certain write conflicts or when a leader change is detected, a replica goes through the join process.

The process starts by refreshing the cached leader state. If there is no leader state, then the replica tries to become the leader (and is the one that creates the leaderState object).
If there is a leader, then it follows either the `JoinAsLeader` (if it believe IT is the leader, based on the cached leader state), or else `JoinAsFollower`.

```text
[IDLE] or [REFRESH]
         |
  RefreshLeaderState -- no metadata --> [ATTEMPT_LEADERSHIP]
         |                                      |
  metadata exists                        AttemptLeadership
         |                                 /         \
         |                            (success)    (conflict)
         |                                |             |
         v                                |         [REFRESH]
       [JOIN] <---------------------------+
         |
         +----> JoinAsLeader
         |           |
         |           +-- applyIndex < commitIndex --> [CATCHUP]
         |           |                                joined = FALSE
         |           |
         |           +-- otherwise -----------------> [READY]
         |                                            joined = TRUE
         |
         +----> JoinAsFollower
                     |
                     +-- rTooFarBehind = TRUE --> [CATCHUP]
                     |                            joined = FALSE
                     |
                     +-- rTooFarBehind = FALSE
                                  |
                           send FOLLOW_REQ
                                  |
                         [AWAIT_FOLLOW_RES]
                            joined = FALSE
```

`JoinAsLeader` enters `[CATCHUP]` when the local apply index is behind the cached reservation boundary. Otherwise it marks the replica joined and enters `[READY]`.

`JoinAsFollower` either enters `[CATCHUP]`, if previously told it was too far behind, or tries to register itself as a follower with the leader by sending a `FOLLOW_REQ` containing its applied index and enters `[AWAIT_FOLLOW_RES]`. The follow request registers the replica for leader-pushed replication. The request and response transitions are described below under **Follow requests and responses**.

The catchup process is documented next.

#### Catchup (join process)

`CatchUp` repeatedly takes the first applicable branch:

1. `RestoreFromSnapshot`. The replica updates its cached snapshot metadata (if the version differs) and if the stored snapshot is ahead of the replica's apply index, the replica restores its complete state based on the snapshot.
2. `ReplayOneLogEntry`: The snapshot was previous loaded and the log is replayed. If the next log batch exists in S3, append its entries to the local machine data and advance the apply index.

Upon completing log replay:
* If replay of the log is finished but the replica is short of `commitIndex - 1`, the replica enters `[ILLEGAL_STATE]`.
* A leader finishing exactly at `commitIndex - 1` sets `rReuseFirstIndex = TRUE`. Its first new batch will use the already-reserved trailing index. A leader that has caught up fully clears this flag. In either case, the replica enters `[READY]` and marks the leader joined.
* A follower finishing recovery clears `rTooFarBehind` and sends a follow request so the leader can push subsequent batches.

> The reason for rReuseFirstIndex is that commitIndex is more of a reservation than an actual commit boundary. It's legal for the commitIndex to be unwritten as the former leader might have crashed after advancing the commitIndex but before writing the log entry. Or the former leader might still be going be in a race to write to the log entry.

#### Follow requests and responses (Joining as a follower)

If rTooFarBehind is FALSE, then a follower initiates replication by telling the replica named in its cached leader state its applyIndex. This exchange registers the follower and afterward the follower marks itself as joined.

`SendFollowReq` sends a `FOLLOW_REQ` and moves the sender to `[AWAIT_FOLLOW_RES]`.
`RecvFollowReq` handles the request according to the receiver's local role:

- If it believes it is a joined leader, it records the sender in `rFollowIndex` with the supplied `applyIndex` and `pending = FALSE`, then replies with `FOLLOW_RES(result = OK)`. This replaces any previous registration for that sender.
- If it does not believe it is leader, it replies with `FOLLOW_RES(result = NOT_LEADER)` without registering the sender.

`RecvFollowRes` consumes the response. If the follower is still waiting for the response and it is an `OK` response, the follower marks itself as joined and enters `[READY]`.
A `NOT_LEADER` response causes the replica to enter `[REFRESH]` to read leadership metadata again and rejoin.

```text
Follower                                      Leader
   |                                             |
SendFollowReq                                    |
   |--- FOLLOW_REQ(applyIndex = i) ------------->|
   |                                             | 
[AWAIT_FOLLOW_RES]                         RecvFollowReq
   |                                      register follower:
   |                                      applyIndex = i
   |                                             |  
   |<--------------------- FOLLOW_RES(OK) -------+
RecvFollowRes                                    
[READY, joined]                                  
```

Once ready, the follower waits for synchronization (replication) requests from the leader (see the Synchronization subsection below). 

### Leader changes

`TryBecomeLeader` lets a nonleader outside the joining states read the latest leader state and attempt a claim, subject to `MaxEpoch`. This abstracts failure detection: there is no modeled heartbeat timeout or requirement that the old leader actually stop.

`DetectLeaderChange` notices a difference between cached and stored epochs, clears the cached leadership and follower-tracking state, and returns to `[REFRESH]`. 

### Appending values

Appending is split into command reception, reservation, and log creation:

```text
               [READY]
                  |
           ReceiveCommands
                  |
            [COMMIT_BATCH]
                  |
             CommitBatch
             /         \
    (stale version)  (reserve successfully,
          |           or reuse reserved index)
     [REFRESH]                |
                       [APPEND_TO_LOG]
                              |
                         AppendToLog
                         /         \
               (address exists)  (address free)
                        |              |
                    [REFRESH]       [READY]
```

`ReceiveCommands` chooses a nonempty set of previously unused model values, converts it to a sequence, and prepares a pending batch. Its target index is either `commitIndex + 1` or, when reusing the trailing reservation, `commitIndex` itself.

The finite, unique `Values` set is a state-space simplification. Values become used when received, even if their batch never succeeds. `auxCommitted`, by contrast, records only successful log writes.

`CommitBatch` normally CAS-updates `leaderState` to reserve the pending index. If the replica's cached version is stale, the executable action moves to `[REFRESH]`. When `rReuseFirstIndex` is true, `CommitBatch` skips the CAS and goes directly to `[APPEND_TO_LOG]`.

`AppendToLog` performs put-if-absent at the pending batch's index:

- If the address exists, the replica enters `[REFRESH]` without applying or committing its values.
- If the address is free, it creates the batch, appends its entries to local machine state and `auxCommitted`, advances the apply index, and returns to `[READY]`.

Both outcomes clear the pending batch and the reuse flag.

The successful log creation is the modeled write-completion point. **`AppendToLog` does not revalidate the stored leader epoch or version, or check the snapshot boundary.** It relies on the target address being occupied to reject a competing write once another leader has filled it.

### Synchronization (aka replication)

Replication is over the network via RPC. The spec models the network as bi-directional FIFO channels for each sender-receiver pair. Messages can be delayed by scheduling, but not reordered or lost.

Once a follower is registered, the leader pushes batches without waiting for further requests from that follower. Its `rFollowIndex` entry contains the follower's last reported `applyIndex` and a `pending` flag that prevents another ordinary sync send until a response arrives. Re-registering a follower resets this tracking entry.

`SendSyncReq` requires a the follow index of a follower to have `pending = FALSE`. It chooses:

```text
nextIndex = rFollowIndex[leader][follower].applyIndex + 1
```

The `LogIndexWritten` guard allows sending when the cached `commitIndex` is above `nextIndex`, or when it equals `nextIndex` and that index is present in the log or covered by the stored snapshot. Thus an unwritten trailing reservation does not immediately produce an error. A follower already at the cached head also waits for further progress.

When sending is enabled, the message depends on whether the batch still exists:

| Log state | `SYNC_REQ` contents | Leader's tracking update |
| --- | --- | --- |
| `log[nextIndex]` exists | `error = None`, `commitIndex = nextIndex`, `batch = log[nextIndex]` | Set `pending = TRUE`. |
| The required batch is missing | `error = TOO_FAR_BEHIND`, `commitIndex = 0`, `batch = None` | Remove the follower's registration. |

`RecvSyncReq` consumes the request and handles three cases:

- A follower receives an `OK` request and applies the batch only when `msg.commitIndex = rApplyIndex[r] + 1`. It appends the batch's entries to local machine data and advances its applied index.
- A follower receives `TOO_FAR_BEHIND` sets `rTooFarBehind = TRUE` and enters `[REFRESH]`, preserving its current machine data and applied index. In the rejoin process, it will see `rTooFarBehind` and do catchup from S3.
- In all other cases, including duplicate batches, batches that skip an index, or a receiver that believes it is leader, machine state remains unchanged.

Every case replies with `SYNC_RES(applyIndex = current applied index)`, using the updated index if the batch was applied.

`RecvSyncRes` sets the sender's tracked follower index to the reported index and clears `pending`, provided the receiver still believes it is leader, is joined, and still has that follower registered. Otherwise it consumes the response and clears any registration for that sender. A response to `TOO_FAR_BEHIND` does not itself re-register the follower.

```text
Leader                                        Follower
   |                                             |
SendSyncReq                                      |
   |--- SYNC_REQ(batch i+1) -------------------->|
pending = TRUE                             RecvSyncReq
   |                                       apply batch i+1
   |<---------------- SYNC_RES(applyIndex=i+1)---|
RecvSyncRes                                      |
tracked applyIndex = i+1                         |
pending = FALSE                                  |
   |--- SYNC_REQ(batch i+2) -------------------->|
```

For a follower told it is too far behind, the recovery path is:

```text
RecvSyncReq(TOO_FAR_BEHIND)
            |
        [REFRESH] -- RefreshLeaderState --> [JOIN]
                                              |
                                       JoinAsFollower
                                              |
                                          [CATCHUP]
                                              |
                              restore snapshot and replay log
                                              |
                                  FollowerCompleteCatchup
                                   send a new FOLLOW_REQ
                                              |
                                     [AWAIT_FOLLOW_RES]
```

This path assumes the refreshed metadata still names another replica as leader. Once registered again, the follower resumes receiving batches after its recovered index.

Sync messages contain no epoch, and acceptance does not check the sender against the receiver's cached leader. The next-index check prevents applying a duplicate or out-of-order batch; it does not independently establish current leadership. Sync acknowledgments track follower progress and allow the next batch to be sent; they are not part of the durable commit decision.

### Snapshotting

`TakeSnapshot` is enabled for a leader in `[READY]` whose apply index is ahead of its cached snapshot index. It captures the replica's complete machine data, applied batch index, cached epoch, and next snapshot version, then enters `[COMMIT_SNAPSHOT]`.

`CommitSnapshot` publishes the pending snapshot if the stored snapshot is absent or its version matches the replica's cached snapshot version. Success updates the replica's snapshot reference and returns it to `[READY]`.

On a version conflict the replica enters `[REFRESH]`.

Snapshot publication does not CAS the leader state or validate current leadership on the success path. Its condition is the snapshot object's own version. Snapshot preparation and batch appending by the same replica are serialized through `rState`, while other replicas and the network may continue progressing.

Publishing a snapshot does not itself delete log batches. Deletion is a separate action by GC.

### Garbage collection

`GarbageCollect` is enabled only when `GcEnabled = TRUE`. Each invocation deletes one existing log batch satisfying:

```text
batch index < snapshot.applyIndex
```

Deleting snapshot-covered data preserves the recoverable history at that moment. The problem is that deletion also removes the object that would reject a delayed put-if-absent from an earlier leader.

## Consistency violation caused by GC

Consider two replicas, `r1` and `r2`, and three distinct singleton batches, `A`, `B`, and `C`. The following execution is permitted by the model:

| Step | Action | Result |
| --- | --- | --- |
| 1 | `r1` becomes leader in epoch 1, receives `A`, and runs `CommitBatch`. | Index 1 is reserved, but `log[1]` is absent. `r1` pauses in `[APPEND_TO_LOG]`. |
| 2 | `r2` joins as a follower, then claims leadership in epoch 2. | The leader-state CAS changes the leader but preserves `commitIndex = 1`. `r1` has not detected the change. |
| 3 | `r2` catches up. | There is no snapshot or batch 1. Applied index 0 is exactly `commitIndex - 1`, so `r2` becomes ready with `rReuseFirstIndex = TRUE`. |
| 4 | `r2` receives and writes `B` at index 1. | It reuses the reservation, and put-if-absent succeeds. Its state and `auxCommitted` are `<<B>>`. |
| 5 | `r2` reserves and writes `C` at index 2. | Its state and `auxCommitted` become `<<B, C>>`. |
| 6 | `r2` takes and commits a snapshot through index 2. | The snapshot contains `<<B, C>>`. |
| 7 | GC deletes batch 1. | Deletion is allowed because `1 < 2`. The snapshot still represents both successful writes. |
| 8 | `r1` resumes its pending `AppendToLog` for `A` at index 1. | The address is absent again, so the write succeeds. `r1` applies `A` and the modeled successful-write history becomes `<<B, C, A>>`. |

The resulting state is:

```text
leaderState:       leader r2, epoch 2, commitIndex 2
snapshot:          applyIndex 2, entries <<B, C>>
log[1]:            <<A>>
log[2]:            <<C>>
r1 machine data:   <<A>>
r2 machine data:   <<B, C>>
auxCommitted:      <<B, C, A>>
```

Two safety properties fail immediately:

- `ReplicaStateIsCommittedPrefix`: `r1`'s `<<A>>` is not a prefix of `<<B, C, A>>`. The replicas have applied different values at batch index 1.
- `LogMatchesCommittedHistory`: recovery restores `<<B, C>>` from the snapshot and replays only indexes above 2. It cannot reconstruct the successful write of `A`, even though the recreated object physically exists at index 1.

`SnapshotIsCommittedPrefix` still holds in this execution: `<<B, C>>` is a prefix of the successful-write history. The snapshot was valid when created. The violation comes from subsequently accepting a write **behind the snapshot boundary**.

The specification has no explicit client-response action; successful `AppendToLog` represents a completed write. At the protocol level, this is an acknowledged-write-loss scenario: the old leader can report success for `A`, but snapshot-based recovery omits it. A later GC can also delete its recreated object. Meanwhile, `B` remains preserved in the snapshot; the failure is the newly accepted stale write and the resulting divergent application state.

Without the deletion in step 7, `log[1]` still contains `B`, so `r1`'s delayed put-if-absent fails. If `r1` instead wins the original race before `r2` fills index 1, `r2`'s competing creation fails and it must rejoin. GC changes the address from absent, to occupied, and back to absent, allowing both competing writes to succeed at different times.

The leader-state CAS cannot prevent this execution because `r1` already passed its reservation step. Eventual leadership-change detection is also insufficient: it can occur after the delayed write. No weak-fairness assumption forbids a finite delay lasting through snapshotting and GC.

This sequence was checked with a targeted TLC replay against `S2C.tla`, using two replicas, three values, `MaxEpoch = 2`, and `GcEnabled = TRUE`. The replay visited 24 states, including initialization, and confirmed that both history properties hold before the final append and fail afterward. This validates the specific counterexample, rather than an exhaustive exploration of all behaviors.

## Invariants

- `TypeOK`: Durable objects, replica state, channels, and auxiliary history have the expected types.
- `ValidReplicas`: No replica enters ILLEGAL_STATE.
- `ValidLeaderState`: Replicas caching the same leader-state version have identical cached leader state, even when that version is stale. A replica caching the current stored version also has exactly the leader state stored in S3. This does not require all replicas to hold the latest version or agree on who currently leads.
- `ReplicaStateIsCommittedPrefix`: Every replica's machine data is a prefix of `auxCommitted`, in every replica state, including recovery and stale-leader states.
- `SnapshotIsCommittedPrefix`: The current snapshot's entries, when a snapshot exists, are a prefix of the successful-write history.
- `LogMatchesCommittedHistory`: The log indexes above the snapshot form a contiguous suffix, and concatenating the snapshot contents with that suffix reconstructs exactly `auxCommitted`. Log objects at or below the snapshot index are excluded, allowing covered objects to be deleted without immediately violating the invariant.

The liveness properties are `AllReplicasJoin`, which requires every replica's joined flag eventually to remain true, and `AllReplicasReachMaxEpoch`, which requires every replica's cached epoch eventually to remain at `MaxEpoch`. They are checked under `LivenessSpec` and its fairness assumptions.
