# Some notes to remember

* There can be no gaps in the chunk address space
* In multi-writer setups, there is contention on the log tail. A writer that gets a write conflict transitions to Catchup Recovery to apply the latest chunks and discover the new tail.
* Chunks below the GC watermark may be inconsistent as it's possible for a stale writer to write a chunk to a position which was just deleted by GC. The validation in Catchup Recovery prevents a stale reader that has read an invalid chunk from reaching the Ready state (t must restart at snapshot recovery). Likewise, validation after an append prevents the writer of an invalid chunk from applying it to its state machine data (it also transitions to snapshot recovery). Other reads simply won't read such invalid chunks as they lie below the snapshot LSN.

# Sequences 

The basic action sequences, see the TLA+ for the nuances.

## Writer initialization

```
[SNAPSHOT_RECOVERY]
          |
          | SnapshotRecovery
          v
  [CATCHUP_RECOVERY] <-----+
          |                |
    CatchupRecovery        |
          |                |
          |  (chunk found) |
          +----------------+
          |
          | (no chunk found)
          |
          v
      [VALIDATE]
          |
       Validate
        |    |
        |    | (validation fails)
        |    v
        |  [SNAPSHOT_RECOVERY]
        |
        | (validation succeeds)
        v
      [READY]
```

## Writer append

```
                    +--(write conflict)-->[CATCHUP_RECOVERY]
                    |                              
  [READY] --AppendChunk--(ok)-->[VALIDATE]      
                                    |
                                 Validate
                                    |
                        +-----------+-----------+
                        |                       |
                        | (succeeds)            | (fails)
                        v                       v
                     [READY]          [SNAPSHOT_RECOVERY]
```

## Writer snapshot

```
  [READY] --WriteSnapshot--(no-conflict)--> [UPDATE_MANIFEST]
                 |                                 |
             (conflict)                      UpdateManifest
                 |                                 |
                 +-------------->[READY]<----------+
```

## Garbage collection

The GC process stays in DELETE until there are no more chunks at LSNs <= the GC watermark to delete and no more snapshots at LSNs < watermark.

```
  [READY] --AdvanceGcWatermark--> [DELETE]
     ^                                |
     |                    +-----------+-----------+
     |                    |                       |
     |                DeleteChunk            DeleteSnapshot
     |                    |                       | 
     |                    v                       v
     |                 [DELETE]                [DELETE]
     |                    |                       |
     +--------------------+-----------------------+
```