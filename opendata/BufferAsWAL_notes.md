# Buffer modified to be a single-writer WAL

Turns out that the manifest epoch is not required, just the manifest version as only one role type needs to modify the file. GC can read it but doesn't need to write it.

## State progress and liveness

The spec has two terminal states for each writer: READY (for writes) and PREEMPTED (after a write conflict). During the initialization phase, any conflict will cause the writer to restart. After initialization (once it has reached READY), any conflict will cause it to transition to PREEMPTED, where it will stay forever. So, writers can battle it out for control, but once an established writer has lost control, it stops. This allows us to model competing writers and keep liveness checks simple.

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