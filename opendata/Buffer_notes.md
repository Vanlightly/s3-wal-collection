# Standard Buffer notes

https://github.com/opendata-oss/opendata/blob/main/buffer/rfcs/0001-stateless-buffer.md

It's a multi-writer, single consumer queue, but if you squint, you can think of the dequeue as log GC also.

Buffer relies on batch objects ids being ULIDs, for the GC algorithm to work. This spec simply models them as monotonic integers.

## Reader Preemption

The spec has two terminal states for each reader: READ_ENTRY (ready for more reads) and PREEMPTED (after a write conflict on acking). During the initialization phase, any conflict will cause the reader to restart where it can try to initialize again. After initialization (once it has reached READ_ENTRY), any conflict will cause it to transition to PREEMPTED, where it will stay forever. So, readers can battle it out for control, but once an established reader has lost control, it stops. This allows us to model competing readers and keep liveness checks simple.

## GC Correctness

Buffer uses a GC algorithm based on ULID, unique identifiers with a timestamp prefix. A GC process reads the manifest and deletes any batch object that meets these criteria:

1. It is not referenced in the current manifest snapshot.
2. Its ULID timestamp is older than the oldest manifest entry's ULID timestamp. This prevents deleting a file that a producer has written to object storage but has not yet enqueued in the manifest.
3. Its ULID timestamp is older than the configured grace period relative to the current wall-clock time.

The grace period here is the trick to make this work. The TLA+ specification does not model time and so no grace period, therefore GC is unsafe as it can delete a valid batch file. See:

1. w1 writes object ts1->A
2. w2 writes object ts2->B
3. w2 reads manifest
4. w2 enqueues object ts2 in the manifest
5. GC reads manifest (sees floor is ts2)
6. w1 reads manifest
7. w1 enqueues object ts1 in the manifest
8. GC lists objects ts=1, ts=2
9. GC deletes object ts1 (deleting a batch from the current manifest)

For this reason, there is a constant EnableGC, which when enabled, causes a safety property violation.

## Cursor management

Getting the cursor management right is critical here and left as an exercise to the user (not part of Buffer protocol). So I implemented a versioned register that you could do with an S3 object.

This spec does the following to initialize a reader:

1. Read manifest
2. Read cursor (version and nextSeq)
3. CAS manifest to increment epoch
4. CAS cursor to increment version

Importantly, both reads happen before either claim completes.

There are two relevant outcomes after a reader wins the manifest CAS:
 - Its subsequent cursor CAS succeeds. It owns the cursor and may process.
 - Its subsequent cursor CAS fails. Another reader updated the cursor, so it restarts initialization and reads both objects again. This could be a lower epoch reader committing a cursor advancement, or another reader in the initialization phase.

A lower-epoch reader can still claim the cursor after a higher epoch has been installed, but that is safe:

1. The lower-epoch reader may durably advance cursor.nextSeq.
2. It cannot trim the manifest because its epoch check/CAS fails.
3. The higher-epoch reader’s cursor claim conflicts.
4. The higher-epoch reader restarts, obtains a newer epoch, and reads the advanced cursor.
5. Its eventual cursor claim preserves that nextSeq.

Not sure how to do cursor management without some kind of conditional write. Couldn't we just store the cursor in the manifest?

## Transition sequences

### Producer append

```                           
[IDLE] --WriteBatch--> [READ_MANIFEST] --ReadManifest--> [APPEND_TO_MANIFEST]
     ^                       ^                              |
     |                       |                         AppendToManifest
     |                       |                              | 
     |                       +------- (write conflict)------+
     |                                                      |
     +---------------------- (succeeds)---------------------+
```


### Reader initialization

```
  [IDLE] --ReaderInitialize--> [INCREMENT_EPOCH]
       ^                              |
       |                              | IncrementManifestEpoch
       |                              |
       |                 +------------+------------+
       |                 |                         |
       |         (write conflict)               (succeeds)
       |                 |                         |
       +-----------------+                         v
       |                                      [CLAIM_CURSOR]
       |                                           |
       |                              +------------+------------+
       |                              |                         |
       |                       write conflict                succeeds
       |                              |                         |
       +------------------------------+                         v
                                                          [READ_ENTRY]
```

`ReaderInitialize` reads both the manifest and cursor before either conditional write is attempted. A conflict restarts the entire initialization flow.

### Reader tailing

```
      +--------[READ_ENTRY]<--------------+
      |             |                     |
      |          ReadEntry                |
      |            |   |                  |
RefreshManifest    |   +---(entry read)---+
       |           |
       |     (invalid cursor)
       |           |
       |           v
       |      [INVALID_STATE]
       | 
       +----+----------------+
            |                |
      (same epoch)      (newer epoch)
            |                |
            v                v
       [READ_ENTRY]     [PREEMPTED]
```

`RefreshManifest` is enabled when the reader has exhausted its local manifest and observes that the global manifest has changed.

### Reader acknowledgement

```
      [READ_ENTRY]
           |
      AckPersistCursor
           |
    +------+-----------+
    |                  |
(write conflict)   (succeeds)
    |                  |
    v                  v
[PREEMPTED]         [START_ACK]
                        |
                  AckReadManifest
                        | 
                 +-----------+-----------+
                 |                       |
            (newer epoch)           (same epoch)
                 |                       |
                 v                       v
            [PREEMPTED]             [PREFIX_TRIM]
                                         |
                                    AckPrefixTrim
                                         | 
                                         v
                                      [COMMIT]
                                         |
                                      AckCommit
                                         | 
                             +-----------+-----------+
                             |                       |
                      (write conflict)           (succeeds)
                             |                       |
                             v                       v
                        [START_ACK]             [READ_ENTRY]
```

`AckPersistCursor` durably advances the cursor before any entries are trimmed. A manifest write conflict returns to `START_ACK`, so the reader reloads the manifest and recomputes the prefix trim without persisting the cursor again.

## Making this into a WAL

Could plausibly use the manifest epoch to turn this into a single writer WAL. 