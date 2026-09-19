# Continuity protocol

Based off the blog post https://cursor.com/blog/git-at-any-scale. The blog post is too vague for a faithful specification so this spec is a best-effort attempt to match the blog post and take reasonable decisions where the blog post is missing or ambiguous.

Continuity's WAL is multi-writer, though in practice, soft affinity is used so make one effective writer at a time. But the protocol remains correct under multi-writer scenarios.

In the other specifications, correctness is determined via a state-machine replication model. In Continuity's case, the machine data is a Git repository. Each copy of the repository must have the same sequence of packfiles applied to it.

Invariants check that:

1) The state machine data (the repo) of each writer is a prefix of the recorded write history (up to date writers contain the whole history, stale writers only a prefix)
2) The correct state machine data can be reconstituted based on the current WAL index, packfiles and machine data snapshot.

This spec uses snapshots like the other specs in this repo, in lieu of details about how Continuity's compaction works. This is beneficial in anycase, as we are trying to abstract away system domain specifics (like LSM trees in SlateDB or Git in this repo). 

## Transitions

States are shown in uppercase square brackets. Action names match the specification; descriptions in parentheses label their outcomes. The diagrams below show replica states, except for the garbage collection diagram, which shows GC states.

The "actions" READ, WRITE and REPLICATE are an artifact of this specification as it makes it simpler to model state transitions from common steps. For example, replaying the WAL index can occur in all three types of action. The state transition after this replay depends on whether it is part of a read, write or replication.

### Replica initialization

`StartReplica` reads the current WAL index and checks whether the local repo has applied all entries in that index. If it is caught up, the replica transitions directly to `[READY]`. Otherwise, it sets its action to `REPLICATE` and enters `[REPLAY_WAL_INDEX]` to catch up before becoming ready.

```text
[IDLE]
   |
StartReplica --(repo caught up)--> [READY]
   |
(repo behind)
   |
   v
[REPLAY_WAL_INDEX]
   |
ReplayWalIndex --(complete)--> [READY]
```

The shared WAL replay and missing-packfile recovery transitions below also apply during initialization.

### Writes

`WritePackFile` uploads a packfile with a unique ID and value, and records it as pending. `GetWalIndex` refreshes the cached index and checks whether the local repo has applied all entries in that index. If it has not, replay must finish before the replica can append its pending packfile reference.

```text
                  [READY]
                     |
                WritePackFile 
                     |
                     v
     +-------->[GET_WAL_INDEX]
     |               |
     |          GetWalIndex --(repo behind)--> [REPLAY_WAL_INDEX]
     |               |                                |
     |         (repo caught up)                  ReplayWalIndex
     |               |                                |
     |               v                                |
     |       [APPEND_WAL_INDEX]<----------------------+
     |               |
CAS failed)-- AppendToWalIndex
                     |
                (CAS success, 
                 apply entry)
                     |
                     v
                  [READY]
```

On CAS success, `AppendToWalIndex` updates both the stored and cached index, applies the pending packfile to the local repo, and clears the pending write. On CAS failure, the pending packfile is retained while the replica refreshes the index and retries, replaying any intervening writes first.

### Reads

`StartRead` checks the WAL index version and refreshes the cached index if it has changed. The replica must catch up to this index before serving the read. `ServeRead` returns the local repo and records it at the position identified by the cached index for invariant checking.

```text
[READY]
   |
StartRead --(repo behind)--> [REPLAY_WAL_INDEX]
   |                                |
(repo caught up)               ReplayWalIndex
   |                                |
   v                                |
[SERVE_READ]<-----------------------+
   |
ServeRead --(read served)--> [READY]
```

### Replication

`StartReplicate` is enabled only when the stored WAL index version differs from the cached version. It refreshes the index and starts replay if the local repo is behind. An index change caused only by compaction may leave the replica already caught up.

```text
[READY]
   |
StartReplicate --(repo caught up)--> [READY]
   |                                    ^
(repo behind)                           |
   |                                    |
   v                                    |
[REPLAY_WAL_INDEX]----ReplayWalIndex----+
```

### Shared WAL replay and missing-packfile recovery

Writes, reads, and replication use `ReplayWalIndex` to catch up to the cached index. Each step either loads the snapshot, applies one packfile, detects a missing packfile, or finishes replay. Loading a snapshot and applying a packfile keep the replica in `[REPLAY_WAL_INDEX]` for the next step.

```text
[REPLAY_WAL_INDEX]
   |
ReplayWalIndex --(complete, WRITE)-----------------------> [APPEND_WAL_INDEX]
   |
   +--(complete, READ)-----------------------------------> [SERVE_READ]
   |
   +--(complete, REPLICATE)------------------------------> [READY]
   |
   +--(complete, unexpected action)----------------------> [ILLEGAL_STATE]
   |
   +--(next position covered by snapshot; load snapshot)-> [REPLAY_WAL_INDEX]
   |
   +--(next packfile missing)----------------------------> [NOT_FOUND]
   |
   +--(next packfile found; apply packfile)--------------> [REPLAY_WAL_INDEX]

[NOT_FOUND]
   |
ValidateNotFound --(index version changed; refresh index)-> [REPLAY_WAL_INDEX]
   |
   +--(index version unchanged)--------------------------> [ILLEGAL_STATE]
```

A missing packfile can result from replaying an old index after compaction and garbage collection. `ValidateNotFound` refreshes a stale index so replay can continue, loading the snapshot if needed. If the index version has not changed, the missing packfile is an error. `[ILLEGAL_STATE]` has no outgoing action and violates `ValidReplicas`.

### Snapshots

`WriteSnapshot` writes the local repo at the position `rWalIndex[r].nextPos - 1`. It requires a nonempty repo, a position at or beyond the cached snapshot frontier, and no snapshot already stored at that position.

```text
[READY]
   |
WriteSnapshot --(snapshot written)--> [COMMIT_SNAPSHOT]
                                            |
                                      CommitSnapshot --(CAS success)--> [READY]
                                            |
                                            +--(CAS failed)-----------> [READY]
```

On CAS success, `CommitSnapshot` updates the stored and cached index to reference the new snapshot, clears the covered WAL entries, and increments the index version. On CAS failure, both indexes are unchanged. Both outcomes return the replica to `[READY]`; the snapshot object remains stored even if its commit fails.

### Garbage collection

GC processes have their own states. `StartGC` is enabled when at least one stored packfile is neither referenced by the current WAL index nor pending commit by any replica. It captures these packfiles in a delete set. As noted in the spec, knowing which packfiles are pending commit is an abstraction rather than a modeled storage protocol.

```text
[IDLE]
   |
StartGC --(delete set captured)--> [DELETE]
                                     |
                               DeletePackFile --(more files remain)--> [DELETE]
                                     |
                                     +--(delete set empty)-----------> [IDLE]
```

`DeletePackFile` removes one ID from the delete set per step, deleting the object if it still exists. The remaining delete set determines the next state, including when another GC process has already deleted the object. Snapshot objects are not garbage collected in this spec.
