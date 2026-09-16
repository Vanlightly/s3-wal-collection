# SlateDB WAL protocol variant with a single CAS-write manifest

This specification models the general approach of the SlateDB WAL protocol, but based on a single versioned manifest object which is updated via CAS writes (based on the version). The purpose is to explore a single-writer WAL protocol that doesn't require numbered manifests for historical reads.

The invariants are basically the same.

The main differences are that:

1. Manifest writes do not need to be verified against a GC boundary.
2. There is no manifest GC (no advancing the GC boundary).
3. There is no boundary file (as there is no need). GC only deletes DATA WAL objects lowerer than the replayAfterWalID (stored in the manifest).

This avoids the need to verify the manifest after writing one and after refreshing the cached manifest.

There still remains the need to verify the fence write by refreshing the manifest to check the replayAfterWalID, as a stale writer could successfully write a fence object to an address that was garbage collected.

## Transitions

### Writer initialization

All the states up to READY.

```text
  [IDLE] --StartWriter --> [FIND_NEXT_WAL_ID]
    ^                             |
    |                       FindNextWalId
    |                             |
    |                             v
    |                         [CLAIM_EPOCH]
    |                          |        |
    |                 (cond failed)   (success)
    |                          |        |            
    +--------------------------+        |
                                        v
               +------------------>[WRITE_FENCE]
               |                     |        |
               |            (cond failed)   (success)              
          (manifest valid)         |            |
               |                   v            v
               |    [VALIDATE_BEFORE_RETRY]  [VALIDATE_FENCE]
               |                   |                |
               +---------ValidateEpochBefore   ValidateFence
                             WalFenceRetry      |         |
                                   |            |         |
                       (manifest invalid)   (invalid)  (valid)
                                   |            |         |
                                   +-----+------+         |
                                         |                v
                                         |          [LOAD_SNAPSHOT]   
                                         v                |
                                     [FENCED]        LoadSnapshot
                                                          |
                                                          |
                                                          v
                                                     [ReplayWAL]<--+
                                                       |     |     |
                                                       |     +-----+
                                                       v
                                                    [READY]               
```

### Writer steady state

```text
[COMMIT_SNAPSHOT]--(cond failed)-->[FENCED]
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