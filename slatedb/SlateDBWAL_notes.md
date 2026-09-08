# SlateDB WAL protocol

Single-writer WAL protocol with fencing. This specification replaces the LSM flush with a flush of state-machine data to a snapshot file. Part of writer initialization, before replaying the WAL, it is to load the current snapshot. The machine data is the sequence of successfully written values. All uses of the word `snapshot` refer to a snapshot of the state machine, not a manifest snapshot (which is a term SlateDB uses).

Invariants check that:

1) The state machine data of each writer is a prefix of the recorded write history (up to date writers contain the whole history, stale writers only a prefix)
2) The correct state machine data can be reconstituted based on the current manifest, WAL and machine data snapshot.

This brings the SlateDB spec inline with other WAL specs in this repo that use the same approach of storing and recovering state machine state.

## State progress and liveness

The spec has two terminal states for each writer: READY (for writes) and FENCED (after a write conflict). FENCED is the equivalent of PREEMPTED in other specs.

During the initialization phase, up to the successful claiming of a writer epoch, any conflict will cause the writer to restart where it can try to initialize again. After an epoch has been claimed, any conflict will cause it to transition to FENCED, where it will stay forever. So, writers can battle it out for control, but once a writer with an established epoch has lost control, it stops. This allows us to model competing writers and keep liveness checks simple.

## Transitions

### Manifest refresh (sub-action)

When a manifest refresh is required, it goes through a three step process:

1. Load the latest manifest
2. Read the boundary file and check if the loaded manifest id is valid (above the boundary). If the manifest id <= the GC boundary it means that this address may have had a different manifest but was deleted by GC.
3. React to the valid/invalid result.
    
RefreshManifest sub-action does steps 1 and 2, the actions that invoke it do step 3.

### Writer initialization

All the states up to READY.

```text
  [IDLE] --StartWriter (valid manifest)--> [FIND_NEXT_WAL_ID]
    ^                                               |
    |                                        FindNextWalId
    |                                               |
    |                                               v
    +--ClaimEpoch (manifest id exists)--------[CLAIM_EPOCH]
                                                    |
                                           ClaimEpoch (success)
                                                    |
                                                    v
                                             [CHECK_BOUNDARY]
                                               |          |
                CheckBoundary (id at/below GC boundary)   | CheckBoundary
                                               |          |
                                               v          | (valid)
                                            [IDLE]        v
                                                   [WRITE_FENCE]
```

`StartWriter` remains in `IDLE` while its manifest refresh is incomplete, and
also remains there when the refreshed manifest is invalid. A claim conflict or
a claimed manifest that has already fallen at or below the GC boundary restarts
initialization.

```text
                                      WriteFenceWalEntry
                    +--------------------(occupied)--------------------+
                    |                                                  |
                    |                                                  v
              [WRITE_FENCE]                                [VALIDATE_BEFORE_RETRY]
                    ^                                                  |
                    |                             ValidateEpochBeforeWalFenceRetry
                    +--------------------(still current)----------------+
                                                                       |
                                                (invalid or newer epoch)|
                                                                       v
                                                                   [FENCED]

              [WRITE_FENCE]
                    |
          WriteFenceWalEntry
               (success)
                    |
                    v
        [VALIDATE_BEFORE_REPLAY]
                    |
          ValidateEpochBeforeReplay
             |               |
(invalid/newer epoch)   (epoch is current)
             |               |
             v               v
         [FENCED]       [LOAD_SNAPSHOT]
                              |
                         LoadSnapshot
                          |         |
             (snapshot missing)  (snapshot read, or id is zero)
                          |         |
                          v         v
                     [FENCED]   [REPLAY_WAL]<--------------------------+
                                      |   |                            |
               (replay cursor reaches |   +--ReplayWAL (DATA or FENCE)-+
               the id after its fence)|
                                      v
                                   [READY]
```

If `ReplayWAL` finds a missing WAL object, it takes the validation path below.
The validation states remain unchanged while a manifest refresh is pending.

```text
     [REPLAY_WAL]
          |       
       ReplayWAL
          |   
     object missing)
          |
          v
[VALIDATE_BEFORE_NOT_FOUND]
          |
ValidateBeforeNotFound
          |
          +--ValidateBeforeNotFound (invalid or newer epoch)--> [FENCED]
          |
          +--ValidateBeforeNotFound (epoch is current)--> [NOT_FOUND*]
          |
          +--ValidateBeforeNotFound (local epoch is ahead)--> [ILLEGAL_STATE*]
```

`NOT_FOUND*` and `ILLEGAL_STATE*` are error states that the invariants require
to be unreachable. `FENCED` is terminal.

### Writer steady state

```text
[COMMIT_SNAPSHOT]---(id occupied)-->[FENCED]
  |         ^
(success)   |
  |         |
  |    WriteSnapshot
  |         |
  +----->[READY]<-----------------+
            |                     |
            |                     |
    AppendEntryToWAL---(success)--+
            |          
      (id occupied)
            |          
            v          
         [FENCED]   
```

An append writes a `DATA` object, advances `wNextWalId`, and applies the value
to the local machine data. Snapshot creation first writes the snapshot object;
`CommitSnapshot` then conditionally publishes its address in a new manifest.

### GC transitions

Manifest and WAL GC share the initialization, but then diverge.

```text
        [IDLE]<---------+
          |             |
        StartGC         |
          |         (invalid manifest)
          v             |
    [LOAD_BOUNDARY]-----+
      |          |
WAL_GC task     MANIFEST_GC task    
    |                  |
    v                  v
[FIND_LAST_WAL_ID]  [COMPUTE_BOUNDARY]
      |                     |
 FindLastWalId      ComputeMaxManifestId
      |                     |
      v                     v
   [DELETE]<--+      [ADVANCE_BOUNDARY]
      |       |             |                             +--------+ 
      |       |      AdvanceGcBoundary                    |        |
      +-------+             |                             v        |
                            +--(boundary advanced)---->[DELETE]----+
                            |
                            +--(stale local version)-->[IDLE]
                            |
                            +--(no advance needed)---->[DONE]
                            |
                            +--(local version ahead)-->[ILLEGAL_STATE*]
```

`DELETE` and `DONE` are terminal GC states. A manifest collector stays in `DELETE` while deleting manifests at or below the boundary; when no eligible manifest remains, no further delete transition is enabled.

The WAL collector records the last WAL ID before entering `DELETE`, never
deletes that object, and only deletes `DATA` objects below the manifest's
`replayAfterWalId`. Fence objects are retained. It may also delete snapshots
older than the snapshot referenced by that manifest.
