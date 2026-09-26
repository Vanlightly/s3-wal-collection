# Simplified Walgit WAL protocol

This specification is a simplified version of https://github.com/tobi/walgit, and might be better described as inspired by walgit (which itself was inspired by Cursor's Contintinuity blog post).

## Basic mechanics

The following is a stripped down, simplified version focusing on the WAL protocol. It differs from Walgit, but keeps the core correctness mechanics.

The system stores three kinds of durable data:

- A mutable **manifest** contains a version, the `headSeq` of the committed WAL, an optional checkpoint reference, and a list of log segment references. Each segment reference identifies an immutable log segment and records the range of sequence numbers it contains.
- An immutable **log segment** contains one or more writes, indexed by sequence number. 
- An immutable **checkpoint** contains the complete materialized state through a particular sequence number.

The manifest defines the committed state. That state is the checkpoint named by the manifest, if there is one, followed by the manifest's referenced log segments above the checkpoint in sequence-number order. Together they contain every committed entry through `headSeq`. A log segment or checkpoint object that exists in storage but is not referenced by the manifest is not part of the committed state.

A log segment's address is determined by its sequence lower bound. A segment reference simply stores the sequence bounds and address of the log segment.

If we have three log segments each containing 5 entries, then we'll have the following log segments:

```
/logs/0000000000000.pb (seq 0-4)
/logs/0000000000005.pb (seq 5-9)
/logs/0000000000010.pb (seq 10-14)
```

A basic write proceeds as follows:

1. A caught-up replica assigns the new values a sequence range beginning at its cached `headSeq + 1`.
2. It writes an immutable log segment to a log segment address (slot) identified by the first sequence number, using put-if-absent so that concurrent writers cannot overwrite one another.
3. It uses a compare-and-swap (CAS) on the manifest version to add the segment reference, advance `headSeq`, and increment the manifest version. This successful manifest update is the commit point.
4. If another writer wins first, the replica refreshes the manifest, replays any newly committed entries, chooses another slot if necessary, and retries. Once its CAS succeeds, it applies its segment locally.

To replay the WAL, a replica first reads the latest manifest. If the manifest's checkpoint is ahead of the replica's applied sequence, it loads that checkpoint and replaces its local materialized state. It then reads and applies the referenced log segments in sequence order until its applied sequence reaches `headSeq`. This same replay process is used when a replica starts, performs background replication, or must catch up during a write retry.

### Write conflicts

Being a multi-writer design, replicas can compete in two places:

1. Write to the same segment address (slot).
2. CAS write of the manifest

**Log segment conflicts** If a replica gets a write conflict when writing a log segment, it refreshes its manifest to see if the winning segment got committed. If it did get committed then the replica replays the WAL and tries writing a new log segment based on the latest manifest state again.

If the competing segment is uncommitted, the replica adds that segment to a "burn set", then attempt to write its own log segment again but offsetting its sequence range by + 1. If that slot + 1 is free and the write succeeds then the replica proceeds to do a CAS manifest write. If the CAS succeeds then the write is done. But for housekeeping it deletes the segment(s) in its burn set. The replica that wrote it cannot commit it as the manifest version has been bumped. If it is competing against many replicas, the burnset can grow to multiple segments as multiple attempts to write its log segment at the slot + 1 address fails.

**Manifest CAS conflicts** If the manifest version has changed, the CAS fails and the replica deletes its own log segment that it wrote. It then refreshes its manifest, replays the WAL and then tries the whole process again (starting by writing a new log segment at `headSeq + 1`).

To avoid deleting the wrong segment, every log-segment write includes a unique `attemptKey`. When deleting its own segment, a replica only deletes it if the attempt key matches. This prevents the replica from deleting a newer segment that has since reused the same slot. 

## Sparse sequences

Due to how the protocol handles competing writes of log segments, the sequence range can have gaps.

## Simplifications

The spec itself discards all git-related parts, and focuses on the basic WAL mechanics. It makes the following main simplifications:

- Writes embed values into log segments directly, rather than writing separate data files which are referenced from log segments.
- The nuances of ambiguous CAS write failures (those which are not condition failed results) are not modeled but the Walgit specs do.
- Walgit has not implemented full GC so this spec also does not cover the GC of old log segments.
- It does not model crashes. A crash is mostly a device useful for testing liveness. When only testing safety properties, in this spec at least, there is no difference between an explicit crash and a replica simply not taking any further actions.

Walgit is multi-writer (by necessity). In the other specifications, correctness is determined via a state-machine replication model. In Walgit's case, the machine data is a Git repository. Each copy of the repository must have the same sequence of values applied to it. This spec uses snapshots like the other specs in this repo, but calls them checkpoints.

## Invariants

Invariants check that:

1) The state machine data (the repo) of each replica is a prefix of the recorded write history (up to date replicas contain the whole history, stale replicas only a prefix).
2) The correct state machine data can be reconstituted based on the current manifest, log segments and checkpoint (snapshot in other specs).
3) Reads are modeled as an invariant that specifies that given an up-to-date replica, it returns machine data (the git repo) that is consistent with the full recorded sequence of committed values.

## Transitions

States are shown in [UPPER CASE]. Action names match the specification (such as StartPublish); descriptions in parentheses label their outcomes.

The "operations" WRITE and REPLICATE are an artifact of this specification as it makes it simpler to model state transitions from common steps. For example, replaying the WAL can occur in two operations. The state transition after this replay depends on whether it is part of a write or replication.

### Replica initialization / replication

`StartReplica` reads the current manifest. If the local machine data has already applied through the manifest's `headSeq`, the replica transitions directly to `[READY]`. Otherwise, it sets its operation to `REPLICATE` and enters `[REPLAY_WAL]` to catch up.

```text
[IDLE]
   |
StartReplica --(replica caught up)--> [READY]
   |                                     ^
(replica behind)                         |
   |                                     |
   v                                     |
[REPLAY_WAL]<---------------+            |
   |                        |            |
ReplayWAL --(still behind)--+            |
   |                                     |
(caught up)                              |
   |                                     |
   +-------------------------------------+
```

Replication follows the same set of transtions, but the replica starts in the READY state and replay is trigger by `StartReplicate`, which is enabled when the stored manifest version differs from the replica's cached version. It refreshes the cached manifest and starts WAL replay if the replica is behind. A manifest change caused only by a checkpoint may leave the replica already caught up.

WAL replay itself is modeled as three sub-actions:
1. LoadCheckpoint. Checkpoint loading replaces the local machine data with the checkpoint contents and advances the applied sequence to the checkpoint sequence. 
2. ReplayNextSegment (repeats for each log segment). Segment replay then applies referenced segments in ascending order (of their seq range) until the applied sequence reaches the cached manifest's `headSeq`
3. CompleteReplay (transitions out of replay). Replay can occur in replication or during a write.

```
 [REPLAY_WAL]
      |
      v
LoadCheckpoint
      |
      v
ReplayNextSegment<---------------+
    |        |                   |
    |        +--(more segments)--+
    |
    v
CompleteReplay--(in write op)-->[CLAIM_SLOT]
    |
(in replication op)
    v
 [READY]       
```

### Publish

`StartPublish` accepts a nonempty set of previously unused values only when the replica is `[READY]`, its cached manifest is current, and its machine data is caught up. In reality, a write request can arrive at a stale replica and it must check if it is current and replay the WAL first if it is not. This is same behavior is achieved in this spec by replication executing then a write executing.

The replica records the values as pending, chooses `headSeq + 1` as the first candidate sequence for its log segment, sets its operation to `WRITE`, and enters `[CLAIM_SLOT]`.

`ClaimFreeLogSlot` uses put-if-absent to upload a log segment at the candidate sequence. The segment contains the pending values and a unique attempt key. If the slot is free, the replica retains the uploaded segment as pending and proceeds to commit it through the manifest. If the slot is occupied, it must inspect the latest manifest before deciding how to retry.

```text
[READY]
   |
StartPublish
   |
   v
[CLAIM_SLOT]
   |
ClaimFreeLogSlot --(slot free; segment uploaded)--> [CAS_MANIFEST]
   |
(slot occupied)
   |
   v
[CHECK_SLOT]
```

`CheckSlot` refreshes the cached manifest after a slot conflict. If another log segment has been committed, the replica clears its burn list, resets its candidate sequence, and replays the WAL before retrying. Otherwise, it returns to `[CLAIM_SLOT]`: it either retries the same slot if it has become free, or records the occupying uncommitted log segment in the burn list and advances to the next candidate slot.

```text
[CHECK_SLOT]
   |
CheckSlot --(committed head advanced)---------------> [REPLAY_WAL]
   |                                                       |
   |                                               (replay complete)
   |                                                       |
   |                                                       v
   +--(candidate slot is now free)------------------> [CLAIM_SLOT]
   |                                                       ^
   +--(candidate still occupied;                           |
       add to burn set and advance candidate seq)----------+
```

`CasManifest` attempts to append the pending log segment reference and advance the manifest head. On success, it applies the pending entries to the local machine data and clears the pending write. The publish either finishes immediately or first deletes the uncommitted segments recorded in its burn list.

```text
[CAS_MANIFEST]
   |
CasManifest --(success; burn set empty)--------> [READY]
   |
   +--(success; burn set non-empty)---+---> [DELETE_BURNED_SEGMENTS]
   |                                  |                |
   |                 (burn set non-empty)   DeleteOneBurnedLogSegment
   |                                  |        |       |
   |                                  +--------+       |
   |                                            (burn set empty)
   |                                                   |
   |                                                   v 
   |                                                [READY]
   |
   +--(CAS conflict; head unchanged)-----------> [CAS_MANIFEST]
   |
   +--(CAS conflict; committed head advanced)--> [DELETE_OWN_SEGMENT]
                                                         |
                                                DeleteOwnLogSegment
                                                         |
                                                         v
                                                   [REPLAY_WAL]
                                                         |
                                                  (replay complete)
                                                         |
                                                         v
                                                   [CLAIM_SLOT]
```

A CAS conflict with an unchanged head is a manifest-version change caused by a checkpoint. The replica refreshes the manifest and retries the same pending segment. If the committed head advanced, its pending segment has been preempted: `DeleteOwnLogSegment` deletes it only if the stored attempt key still matches, clears the pending segment and burn set, resets the candidate sequence, and starts WAL replay.

After a successful commit, `DeleteOneBurnedLogSegment` similarly checks each recorded attempt key before deleting the object. It removes one burn-set entry per step, remaining in `[DELETE_BURNED_SEGMENTS]` until the set is empty and then returning to `[READY]`. This is basically just housekeeping.

### Checkpoints

`WriteCheckpoint` is enabled when the replica is `[READY]` and its cached manifest is current. Walgit performs checkpoints on the local head, but can end up committing a checkpoint behind HEAD after retries. This simpler spec does not do retries in case of a CAS conflict (it discards the checkpoint which naturally allows a new fresh a attempt). But to allow for checkpoints behind HEAD to be committed, the replica is allowed to choose an applied sequence lower than HEAD. It uploads the local machine data through that sequence as a uniquely identified checkpoint, records the checkpoint as pending, and enters `[COMMIT_CHECKPOINT]`.

```text
     [READY]
        |
  WriteCheckpoint 
        |
  (checkpoint uploaded)
        |
        v
[COMMIT_CHECKPOINT]
        |
  CommitCheckpoint --(CAS success)--> [READY]
        |
    (CAS conflict, discard cp)
        |              
        v
      [READY]
```

On CAS success, `CommitCheckpoint` updates the stored and cached manifests to reference the new checkpoint, removes checkpointed log-segment references from the manifest, and increments the manifest version. On a CAS conflict, both manifests remain unchanged. In either case, it clears the pending checkpoint and returns the replica to `[READY]`. The uploaded checkpoint object remains stored after a conflict, and log segments removed from the manifest are not garbage collected by this specification.
