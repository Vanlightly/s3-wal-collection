----------------------------- MODULE Walgit -------------------------

(*
    This specification is a simplified version of https://github.com/tobi/walgit,
    and might be better described as inspired by walgit (which itself
    was inspired by Cursor's Contintinuity blog post).

    The spec itself discards all git-related parts, and focuses on
    the basic WAL mechanics. It simplifies writes by embedding
    write values into log segments, rather than writing separate
    data files which are referenced from log segments.

    Walgit has not implemented full GC so this spec also does not
    cover GC of old log segments.

    This spec models reads as an invariant. A read can only
    be served if the local manifest and local state are
    current, if a read is received and local state is stale
    then the replica must catch-up and then serve the read. This
    is modeled by the replication action and the ConsistentReads
    invariant.
*)

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, 
        SequencesExt, TLC

\* Parameters
CONSTANTS Replicas, \* replica processes
          Values    \* The set of values to write
          
\* Replica states
CONSTANTS IDLE, GET_MANIFEST, REPLAY_WAL, CLAIM_SLOT, 
          CAS_MANIFEST, CHECK_SLOT, DELETE_OWN_SEGMENT, 
          DELETE_BURNED_SEGMENTS, READY,  
          COMMIT_CHECKPOINT, ILLEGAL_STATE

\* Replica operations
CONSTANTS REPLICATE, WRITE, CHECKPOINT

CONSTANT None

\* S3 state
VARIABLES logSegments,     \* Seq -> Log Segment on S3
          checkpoints,     \* Id -> Checkpoint (snapshot) on S3
          manifest         \* Mutable manifest on S3

\* per-replica state
VARIABLES rOperation,      \* Replica -> operation (write, replicate, checkpoint etc)
          rState,          \* Replica -> state (individual steps inside operations)
          rManifest,       \* Replica -> local copy of the manifest
          rMachineData,    \* Replica -> materialized state (aka git repo)
          rAppliedSeq,     \* Replica -> the applied seq (applied to machine state)
          rPendingValue,   \* Replica -> value being written
          rPendingSegment, \* Replica -> Log Segment being committed
          rPendingCp,      \* Replica -> checkpoint being committed
          rCandidateSeq,   \* Replica -> the seq of the LogSegment being written
          rBurned          \* Replica -> the Log Segment seqs to be deleted

\* auxilliary variables for invariant checking
VARIABLES auxUsedValues,   \* the set of values being or having been written
          auxAttemptKey,   \* counter for unique keys
          auxCommitted     \* the committed [seq -> value]

storeVars == <<logSegments, manifest, checkpoints>>
replicaVars == <<rOperation, rState, rManifest, rMachineData, 
                 rAppliedSeq, rPendingValue, rPendingSegment,
                 rPendingCp, rCandidateSeq, rBurned>>
auxVars == <<auxUsedValues, auxAttemptKey, auxCommitted>>
vars == <<storeVars, replicaVars, auxVars>>

\***************************************************************************
\* Helpers
\***************************************************************************

MaxOrDef(set, def) == IF set = {} THEN def ELSE Max(set)
RemoveKey(f, key) == [x \in (DOMAIN f \ {key}) |-> f[x]]

\* The applied seq has reached the headSeq
IsCaughtUp(r, currManifest) ==
    rAppliedSeq[r] = currManifest.headSeq

ReadCheckpoint(id) == IF id \in DOMAIN checkpoints
                      THEN checkpoints[id]
                      ELSE None
ReadLogSegment(id) == IF id \in DOMAIN logSegments
                      THEN logSegments[id]
                      ELSE None

IllegalState(r) ==
    /\ rState' = [rState EXCEPT ![r] = ILLEGAL_STATE]
    /\ UNCHANGED <<rOperation, rPendingValue, rManifest, rMachineData, 
                   rAppliedSeq, rPendingSegment, rBurned, 
                   rCandidateSeq, rPendingCp>>

RefreshManifest(r) ==
    rManifest' = [rManifest EXCEPT ![r] = manifest]

TransitionToReady(r) ==
    /\ rState' = [rState EXCEPT ![r] = READY]
    /\ rOperation' = [rOperation EXCEPT ![r] = READY]

TransitionToReplayWAL(r) ==
    /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL]
    /\ rOperation' = [rOperation EXCEPT ![r] = REPLICATE]

\* If the entries share a common seq, then there is a bug,
\* so set the result to be empty to trigger an invariant
ConcatEntries(sq1, sq2) ==
    IF \/ \E i \in DOMAIN sq1 : i \in DOMAIN sq2
       \/ \E i \in DOMAIN sq2 : i \in DOMAIN sq1
    THEN <<>>
    ELSE sq1 @@ sq2

\***************************************************************************
\* Common actions
\***************************************************************************

(* ---------------------------------------------------------
    ACTION: StartReplica

    A replica starts by loading the current manifest.
    If the replica is caught up it transitions to READY
    where it can start serving reads and writes, else
    it transitions to REPLAY_WAL to catch up.
    Reads are modeled as the ConsistentReads invariant.
-----------------------------------------------------------*)

StartReplica(r) ==
    /\ rState[r] = IDLE
    /\ RefreshManifest(r)
    /\ IF IsCaughtUp(r, manifest)
       THEN TransitionToReady(r)
       ELSE TransitionToReplayWAL(r)
    /\ UNCHANGED <<storeVars, auxVars, rPendingValue, 
                   rPendingSegment, rPendingCp, rMachineData,
                   rAppliedSeq, rBurned, rCandidateSeq>>

(* ---------------------------------------------------------
    ACTION: ReplayWAL
    
    WAL replay consists of three sub-actions:
     * LoadCheckpoint
     * ReplayNextSegment
     * ReplayComplete

    Once replay is complete, the replica transitions to the
     next state, depending on what operation it is performing: 
    - WRITE: after replaying the WAL, the replica transitions to
             CLAIM_SLOT to attempt to write a log segment again
    - REPLICATE: the replica returns to READY state
-----------------------------------------------------------*)

(* SUB-ACTION LoadCheckpoint  -----------------------------*)
ShouldLoadCheckpoint(r) ==
    \* there is a checkpoint to load
    /\ rManifest[r].checkpoint /= None
    \* the applied seq is covered the checkpoint
    /\ rAppliedSeq[r] < rManifest[r].checkpoint.seq

LoadCheckpoint(r) ==
    LET cp == ReadCheckpoint(rManifest[r].checkpoint.id) IN
        \* overwrite the machine data with the checkpoint data
        /\ rMachineData' = [rMachineData EXCEPT ![r] = cp.entries]
        \* advance the applied seq
        /\ rAppliedSeq' = [rAppliedSeq EXCEPT ![r] = cp.seq]
        /\ UNCHANGED <<rOperation, rState, rPendingValue, rManifest,
                       rPendingSegment, rPendingCp, rBurned, rCandidateSeq>>

(* SUB-ACTION ReplayNextSegment -------------------------- *)
ShouldLoadNextSegment(r) ==
    \* There is a segment whose seq range is above the applied seq
    \E s \in DOMAIN rManifest[r].logSegments : 
        rManifest[r].logSegments[s].lastSeq > rAppliedSeq[r]

NextSegmentRef(r) ==
    \* choose the segment with the lowest seq range that 
    \* is above the applied seq
    LET segRefs == rManifest[r].logSegments
        next == CHOOSE s \in DOMAIN segRefs :
                    /\ segRefs[s].lastSeq > rAppliedSeq[r]
                    /\ ~\E s0 \in DOMAIN segRefs :
                        /\ segRefs[s0].lastSeq > rAppliedSeq[r]
                        /\ s0 < s
    IN segRefs[next]

ReplayNextSegment(r) ==
    LET segRef  == NextSegmentRef(r) 
        segment == ReadLogSegment(segRef.id)
    IN
        \* apply the log segment data to the local machine data
        /\ rMachineData' = [rMachineData EXCEPT ![r] = 
                                    ConcatEntries(@, segment.entries)] 
        \* advance the applied seq
        /\ rAppliedSeq' = [rAppliedSeq EXCEPT ![r] = segRef.lastSeq]
        /\ UNCHANGED <<rOperation, rState, rPendingValue, rManifest, rPendingCp,
                       rPendingSegment, rBurned, rCandidateSeq>>

(* SUB-ACTION ReplayComplete ------------------------------*)
ShouldCompleteReplay(r) ==
    rAppliedSeq[r] = rManifest[r].headSeq

StateAfterReplay(r) ==
    CASE 
         rOperation[r] = WRITE -> CLAIM_SLOT
      [] rOperation[r] = REPLICATE -> READY
      [] OTHER -> ILLEGAL_STATE

\* If the next state is READY, then the operation is over
\* and is set to READY, else it remains unchanged
OpAfterReplay(r, nextState) ==
    IF nextState = READY THEN READY ELSE rOperation[r]

CompleteReplay(r) ==
    LET nextState == StateAfterReplay(r)
        nextOp    == OpAfterReplay(r, nextState)
    IN
        /\ rState' = [rState EXCEPT ![r] = nextState]
        /\ rOperation' = [rOperation EXCEPT ![r] = nextOp]
        /\ UNCHANGED <<rPendingValue, rManifest, rMachineData,  
                       rPendingCp, rAppliedSeq, rPendingSegment, 
                       rBurned, rCandidateSeq>>

ReplayWAL(r) ==
    /\ rState[r] = REPLAY_WAL
    /\ CASE ShouldCompleteReplay(r) -> CompleteReplay(r)
         [] ShouldLoadCheckpoint(r) -> LoadCheckpoint(r)
         [] ShouldLoadNextSegment(r) -> ReplayNextSegment(r)
         [] OTHER -> IllegalState(r)
    /\ UNCHANGED <<storeVars, auxVars>>

\***************************************************************************
\* Replicate actions
\***************************************************************************

(* ---------------------------------------------------------
    ACTION: StartReplicate

    A replica checks if its manifest is up-to-date and if
    it is not, the replica refreshes its manifest. If
    the replica's applied seq is behind the manifest headSeq,
    it transitions to replay the WAL.
-----------------------------------------------------------*)

StartReplicate(r) ==
    /\ rState[r] = READY
    /\ rManifest[r].version /= manifest.version
    /\ RefreshManifest(r)
    /\ IF IsCaughtUp(r, manifest)
       THEN UNCHANGED <<rState, rOperation>>
       ELSE TransitionToReplayWAL(r)
    /\ UNCHANGED <<storeVars, auxVars, rPendingValue,
                   rAppliedSeq, rPendingSegment, rMachineData,
                   rPendingCp, rBurned, rCandidateSeq>>

\***************************************************************************
\* Write actions
\***************************************************************************

(* ---------------------------------------------------------
    ACTION: StartPublish

    A replica can start a write only if it is caught up. Catch
    up is deferred to the replication action.

    A caught up replica accepts a set of values for a write 
    operation. A candidate seq for the log segment is chosen,
    based on the headSeq of the local manifest (which we know
    is current). The replica transitions to CLAIM_SLOT where
    it will attempt tp write a numbered log segment (the 
    candidate seq).
-----------------------------------------------------------*)

StartPublish(r, values) ==
    /\ rState[r] = READY
    /\ values /= {}
    /\ \A v \in values: v \notin auxUsedValues
    /\ rManifest[r].version = manifest.version
    /\ IsCaughtUp(r, rManifest[r])
    /\ rCandidateSeq' = [rCandidateSeq EXCEPT ![r] = rManifest[r].headSeq + 1]
    /\ rState' = [rState EXCEPT ![r] = CLAIM_SLOT]
    /\ rOperation' = [rOperation EXCEPT ![r] = WRITE]
    /\ rPendingValue' = [rPendingValue EXCEPT ![r] = SetToSeq(values)]
    /\ auxUsedValues' = auxUsedValues \union values
    /\ UNCHANGED <<storeVars, auxAttemptKey, auxCommitted, rManifest,
                   rAppliedSeq, rPendingSegment, rPendingCp, rMachineData, 
                   rBurned>>
(* ---------------------------------------------------------
    ACTION: ClaimFreeLogSlot

    A replica attempts to write a log segment (using 
    put-if-absent) containing the values to be written
    and an "attempt key", which is unique and used to
    safely delete log segments later under certain 
    write conflict scenarios.

    If a write conflict occurs, the replica transitions
    to CHECK_SLOT, where it will figure out how to handle
    this conflict.
    If the write succeeds, the replica transitions to
    CAS_MANIFEST.
-----------------------------------------------------------*)

Entries(r, first, last) ==
    LET diff == first - 1 IN
        [i \in first..last |-> rPendingValue[r][i-diff]]

ClaimFreeLogSlot(r) ==
    /\ rState[r] = CLAIM_SLOT
    /\ LET firstSeq == rCandidateSeq[r]
           lastSeq  == rCandidateSeq[r] + Len(rPendingValue[r]) - 1
           segRef   == [id       |-> firstSeq, 
                        firstSeq |-> firstSeq,
                        lastSeq  |-> lastSeq]
           segment  == [entries    |-> Entries(r, firstSeq, lastSeq),
                        attemptKey |-> auxAttemptKey]
           pending  == [ref |-> segRef, segment |-> segment]
       IN
          \* CASE 1 - write conflict, transition to CHECK_SLOT
          \/ /\ firstSeq \in DOMAIN logSegments
             /\ rState' = [rState EXCEPT ![r] = CHECK_SLOT]
             /\ UNCHANGED <<logSegments, rPendingSegment, auxAttemptKey>>
          \* CASE 2 - no write conflict, append new log segment
          \/ /\ firstSeq \notin DOMAIN logSegments
             /\ logSegments' = logSegments @@ (firstSeq :> segment)
             /\ rPendingSegment' = [rPendingSegment EXCEPT![r] = pending]
             /\ auxAttemptKey' = auxAttemptKey + 1
             /\ rState' = [rState EXCEPT ![r] = CAS_MANIFEST]
    /\ UNCHANGED <<manifest, checkpoints, auxCommitted, auxUsedValues,
                   rOperation, rAppliedSeq, rManifest, rPendingValue,
                   rMachineData, rPendingCp, rBurned, rCandidateSeq>>

(* ---------------------------------------------------------
    ACTION: CheckSlot

    A replica experienced a write conflict writing a log
    segment. It refreshes its manifest to determine the
    next action (see the three cases below).
-----------------------------------------------------------*)

CheckSlot(r) ==
    /\ rState[r] = CHECK_SLOT
    /\ RefreshManifest(r)
    /\ CASE 
         \* CASE 1 - Since writing the log segment, someone else has 
         \*          committed a log segment which this replica must 
         \*          replay before trying to claim a slot again. Set 
         \*          the canidate seq again and transition to REPLAY_WAL.
            rAppliedSeq[r] < manifest.headSeq ->
                  /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL]
                  /\ rBurned' = [rBurned EXCEPT ![r] = <<>>]
                  /\ rCandidateSeq' = [rCandidateSeq EXCEPT ![r] = manifest.headSeq + 1]
                  /\ UNCHANGED <<rOperation, rPendingValue>> 
         \* CASE 2 - The candidate seq is uncommitted and free, so 
         \*          it can be claimed again. Transition to CLAIM_SLOT
         [] /\ rCandidateSeq[r] > manifest.headSeq
            /\ rCandidateSeq[r] \notin DOMAIN logSegments ->
                  /\ rState' = [rState EXCEPT ![r] = CLAIM_SLOT]
                  /\ UNCHANGED <<rOperation, rPendingValue, rCandidateSeq, rBurned>>
         \* CASE 3 - The candidate seq is uncommitted but occupied, so 
         \*          add it to the burn set, advance the candidate seq 
         \*          and transition to CLAIM_SLOT to try and claim a 
         \*          slot again.
         [] /\ rCandidateSeq[r] > manifest.headSeq
            /\ rCandidateSeq[r] \in DOMAIN logSegments ->
                  /\ LET id     == rCandidateSeq[r]
                         burned == [id |-> id, attemptKey |-> logSegments[id].attemptKey]
                     IN /\ rBurned' = [rBurned EXCEPT ![r] = Append(@, burned)]
                        /\ rCandidateSeq' = [rCandidateSeq EXCEPT ![r] = @ + 1]
                        /\ rState' = [rState EXCEPT ![r] = CLAIM_SLOT]
                  /\ UNCHANGED <<rOperation, rPendingValue>>
    /\ UNCHANGED <<storeVars, auxVars, rAppliedSeq, rPendingSegment,
                   rMachineData, rPendingCp>>

(* ---------------------------------------------------------
    ACTION: CasManifest

    A replica successfully wrote a log segment and now
    attempts a CAS write of the manifest, with the new
    log segment ref appended to the manifest log segments.

    If the write succeeds and there are no log segments
    to burn, then the write op is over. If there are log
    segments to burn then transition to DELETE_BURNED_SEGMENTS.
    In the case of a write conflict, it could mean that
    another replica committed a log segment first 
    (invalidating this replica's log segment), or it could 
    have been a manifest version bump due to a checkpoint 
    (which does not invalidate the written log segment).
-----------------------------------------------------------*)

CasManifest(r) ==
    /\ rState[r] = CAS_MANIFEST
    /\ LET segRef    == rPendingSegment[r].ref
           successor == [rManifest[r] EXCEPT !.headSeq     = segRef.lastSeq,
                                             !.logSegments = Append(@, segRef),
                                             !.version     = @ + 1]
           committed == rPendingSegment[r].segment.entries
       IN
            \* CASE 1 - Write conflict! Another replica has committed a log
            \*          segment causing the replica to fall behind. The replica
            \*          refreshes its manifest and transitions to DELETE_OWN_SEGMENT
            \*          to delete its now invalid segment (after which the
            \*          the replica will retry the write process).
            \/ /\ rManifest[r].version /= manifest.version
               /\ rAppliedSeq[r] < manifest.headSeq
               /\ RefreshManifest(r)
               /\ rState' = [rState EXCEPT ![r] = DELETE_OWN_SEGMENT]
               /\ UNCHANGED <<manifest, auxCommitted, rOperation, 
                              rMachineData, rAppliedSeq,
                              rPendingValue, rPendingSegment>>
            \* CASE 2 - Write conflict! But no log segments have been committed
            \*          by other replicas, so refresh the manifest and remain
            \*          in CAS_MANIFEST for another try.
            \/ /\ rManifest[r].version /= manifest.version
               /\ rAppliedSeq[r] = manifest.headSeq
               /\ RefreshManifest(r)
               /\ UNCHANGED <<manifest, auxCommitted, rOperation, 
                              rState, rMachineData, rAppliedSeq,
                              rPendingValue, rPendingSegment>>
            \* CASE 3 - Write success! Apply the committed entries to the
            \*          local machine state and advance the applied seq.
            \*          If the burn set is empty, then the operation
            \*          is complete, else transition to DELETE_BURNED
            \/ /\ rManifest[r].version = manifest.version
               /\ manifest' = successor
               /\ rManifest'       = [rManifest EXCEPT ![r] = successor]
               /\ rMachineData'   = [rMachineData EXCEPT ![r] = 
                                            ConcatEntries(@, committed)]
               /\ rAppliedSeq'     = [rAppliedSeq EXCEPT ![r] = segRef.lastSeq]
               /\ rPendingValue'   = [rPendingValue EXCEPT ![r] = None]
               /\ rPendingSegment' = [rPendingSegment EXCEPT ![r] = None]
               /\ auxCommitted' = ConcatEntries(auxCommitted, committed)
               /\ IF Len(rBurned[r]) = 0
                  THEN TransitionToReady(r)
                  ELSE /\ rState' = [rState EXCEPT ![r] = DELETE_BURNED_SEGMENTS]
                       /\ UNCHANGED rOperation
    /\ UNCHANGED <<logSegments, checkpoints, auxAttemptKey, auxUsedValues,
                   rBurned, rCandidateSeq, rPendingCp>>          

(* ---------------------------------------------------------
    ACTION: DeleteOwnLogSegment

    The CAS write of the manifest failed, and refreshing
    the manifest showed that another replica had committed
    a competing log segment first. So this replica must
    now delete its own preempted log segment and then 
    transition to REPLAY_WAL to catch up before retrying
    the write.
-----------------------------------------------------------*)

DeleteOwnLogSegment(r) ==
    /\ rState[r] = DELETE_OWN_SEGMENT
    /\ logSegments' = RemoveKey(logSegments, rPendingSegment[r].ref.id)
    /\ rPendingSegment' = [rPendingSegment EXCEPT ![r] = None]
    /\ rCandidateSeq' = [rCandidateSeq EXCEPT ![r] = rManifest[r].headSeq + 1]
    /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL]
    /\ rBurned' = [rBurned EXCEPT ![r] = <<>>]
    /\ UNCHANGED <<manifest, checkpoints, auxVars, rOperation, rManifest,
                   rAppliedSeq, rPendingValue, rMachineData, rPendingCp>>

(* ---------------------------------------------------------
    ACTION: DeleteOneBurnedLogSegment

    The replica preempted one or more other replicas in
    committing a log segment. The "burned" segment(s)
    written by the other replica(s) can now be deleted
    as they have not been added to the manifest log segments
    (they are dangling/orphan log segments) that would
    not be read by another replica. This is just
    housekeeping.
-----------------------------------------------------------*)

DeleteOneBurnedLogSegment(r) ==
    /\ rState[r] = DELETE_BURNED_SEGMENTS
    /\ LET burned == Head(rBurned[r])
       IN /\ logSegments' =
                  IF /\ burned.id \in DOMAIN logSegments
                     /\ logSegments[burned.id].attemptKey = burned.attemptKey
                  THEN RemoveKey(logSegments, burned.id)
                  ELSE logSegments
          /\ rBurned' = [rBurned EXCEPT ![r] = Tail(@)]
          /\ IF Len(rBurned[r]) = 1
             THEN TransitionToReady(r)
             ELSE UNCHANGED <<rState, rOperation>>
    /\ UNCHANGED <<manifest, checkpoints, auxVars, rAppliedSeq, rManifest, 
                   rPendingValue, rMachineData, rCandidateSeq, 
                   rPendingSegment, rPendingCp>>

\***************************************************************************
\* Snapshot actions
\***************************************************************************

(* ---------------------------------------------------------
    ACTION: WriteCheckpoint

    A caught-up replica has something to checkpoint.
    It writes a checkpoint file (which contains its local
    machine data) with a unique id (composed of the 
    checkpoint seq and a unique key). Then it transitions
    to COMMIT_CHECKPOINT.
-----------------------------------------------------------*)

WriteCheckpoint(r) ==
    /\ rState[r] = READY
    /\ rManifest[r].version = manifest.version
    /\ IsCaughtUp(r, rManifest[r])
    /\ \* Either, no checkpoint has ever been written and
       \* there is data to checkpoint
       \/ /\ rManifest[r].checkpoint = None
          /\ rAppliedSeq[r] > 0
       \* Or there is a previous checkpoint, and the applied
       \* seq has advanced beyond it.
       \/ /\ rManifest[r].checkpoint /= None
          /\ rAppliedSeq[r] > rManifest[r].checkpoint.seq
    /\ LET cpId  == [seq |-> rAppliedSeq[r], attemptKey |-> auxAttemptKey]
           cpRef == [id |-> cpId, seq |-> rAppliedSeq[r]]   
           cp    == [seq     |-> rAppliedSeq[r],
                     entries |-> rMachineData[r]]
       IN /\ checkpoints' = checkpoints @@ (cpId :> cp)
          /\ rPendingCp' = [rPendingCp EXCEPT ![r] = cpRef]
          /\ rState' = [rState EXCEPT ![r] = COMMIT_CHECKPOINT]
          /\ rOperation' = [rOperation EXCEPT ![r] = CHECKPOINT]
          /\ auxAttemptKey' = auxAttemptKey + 1
    /\ UNCHANGED <<manifest, logSegments, auxUsedValues, auxCommitted,
                   rAppliedSeq, rBurned, rCandidateSeq, rManifest,
                   rPendingSegment, rPendingValue, rMachineData>>

(* ---------------------------------------------------------
    ACTION: WriteCheckpoint

    A replica attempts a CAS write of the manifest, updated
    with the new checkpoint ref. If the write is successful
    or not, the replica returns back to the READY state.
    If there was a conflict, then the replica can catch-up
    via the replication action and then try to 
    checkpoint again (if the latest checkpoint is behind).
-----------------------------------------------------------*)

CommitCheckpoint(r) ==
    /\ rState[r] = COMMIT_CHECKPOINT
    /\ LET successor == [rManifest[r] EXCEPT !.checkpoint = rPendingCp[r],
                                             !.version = @ + 1]
       IN
           /\ IF rManifest[r].version = manifest.version
              THEN /\ manifest' = successor
                   /\ rManifest' = [rManifest EXCEPT ![r] = successor]
              ELSE UNCHANGED <<manifest, rManifest>>
           /\ TransitionToReady(r)
           /\ rPendingCp' = [rPendingCp EXCEPT ![r] = None]
    /\ UNCHANGED <<checkpoints, logSegments, auxVars, rAppliedSeq, rMachineData,
                   rBurned, rCandidateSeq, rPendingSegment, rPendingValue>>

\***************************************************************************
\* Types (data model)
\***************************************************************************

\* Durable state ##############

\* EntriesType ---------
\* A function of [Nat -> Value], with gaps in the Nat domain
ValidEntriesType(entries) ==
    \A seq \in DOMAIN entries : 
        /\ seq \in Nat
        /\ entries[seq] \in Values

\* CheckpointType ---------
\* Checkpoint { seq: Nat, entries: EntriesType}
ValidCheckpointType(cp) ==
    \/ cp = None
    \/ /\ cp /= None
       /\ cp.seq \in Nat
       /\ ValidEntriesType(cp.entries)

\* LogSegment type ---------
\* LogSegment { attemptKey: Nat, entries: EntriesType}
ValidLogSegmentType(s) ==
    \/ s = None
    \/ /\ s /= None
       /\ ValidEntriesType(s.entries)
       /\ s.attemptKey \in Nat       

CheckpointIdType == [seq: Nat, attemptKey: Nat]
CheckpointRefType == [id: CheckpointIdType, seq: Nat]   
LogSegmentRefType == [id: Nat, firstSeq: Nat, lastSeq: Nat]

ManifestType == [headSeq: Nat, 
                 logSegments: Seq(LogSegmentRefType),
                 checkpoint: CheckpointRefType \union {None},
                 version: Nat]

\* Local replica state ##############

\* PendingSegmentType -----------
\* PendingSegmentType {ref: LogSegmentRefType, segment: LogSegmentType}
ValidPendingSegment(ps) ==
    \/ ps = None
    \/ /\ ps /= None
       /\ ps.ref \in LogSegmentRefType
       /\ ValidLogSegmentType(ps.segment)

BurnedType == [id: Nat, attemptKey: Nat]

\* type correctness
TypeOK ==
    /\ \A id \in DOMAIN logSegments :
        /\ id \in Nat
        /\ ValidLogSegmentType(logSegments[id])
    /\ \A id \in DOMAIN checkpoints :
        /\ id \in CheckpointIdType
        /\ ValidCheckpointType(checkpoints[id])
    /\ manifest \in ManifestType
    /\ rOperation \in [Replicas -> {IDLE, READY, REPLICATE, WRITE, CHECKPOINT}]
    /\ rState \in [Replicas -> {IDLE, GET_MANIFEST, REPLAY_WAL, CLAIM_SLOT, 
                                CAS_MANIFEST, CHECK_SLOT, DELETE_OWN_SEGMENT, 
                                DELETE_BURNED_SEGMENTS, READY, COMMIT_CHECKPOINT,
                                ILLEGAL_STATE}]
    /\ rManifest \in [Replicas -> ManifestType \union {None}]
    /\ \A r \in Replicas: ValidEntriesType(rMachineData[r])
    /\ rAppliedSeq \in [Replicas -> Nat]
    /\ rPendingValue \in [Replicas -> Seq(Values) \union {None}]
    /\ \A r \in Replicas : ValidPendingSegment(rPendingSegment[r]) 
    /\ rCandidateSeq \in [Replicas -> Nat]
    /\ rBurned \in [Replicas -> Seq(BurnedType)]
    /\ auxUsedValues \in SUBSET Values
    /\ auxAttemptKey \in Nat
    /\ ValidEntriesType(auxCommitted)
    
\***************************************************************************
\* Properties
\***************************************************************************    

\* INV: ValidReplicas
\* No replicas enter an invalid state.
ValidReplicas == 
    \A r \in Replicas :
        /\ rState[r] /= ILLEGAL_STATE
        /\ rState[r] = READY => rOperation[r] = READY

(* INV: ReplicaStateIsCommittedPrefix
   The machine data of every replica is a valid prefix
   of the recorded committed sequence of entries.
*)

IsPrefixOfComitted(mState, appliedSeq) ==
    /\ Cardinality(DOMAIN mState) <= Cardinality(DOMAIN auxCommitted)
    /\ \A seq \in DOMAIN mState : 
        mState[seq] = auxCommitted[seq]
    /\ \A seq \in DOMAIN auxCommitted : 
        \/ /\ seq > appliedSeq
           /\ seq \notin DOMAIN mState
        \/ /\ seq <= appliedSeq
           /\ seq \in DOMAIN mState
           /\ mState[seq] = auxCommitted[seq]

ReplicaStateIsCommittedPrefix ==
    \A r \in Replicas :
        IsPrefixOfComitted(rMachineData[r], rAppliedSeq[r])

(* INV: ManifestRepresentsCommittedState
   Central WAL safety property: a replica can reconstruct 
   the complete committed state from the checkpoint and 
   log segments listed in the current manifest.
*)
ManifestRepresentsCommittedState ==
    LET cpSeq == IF manifest.checkpoint = None THEN 0 
                 ELSE manifest.checkpoint.seq 
        cp    == checkpoints[manifest.checkpoint.id]
        hist  == auxCommitted
    IN
        \A seq \in DOMAIN hist :
            /\ seq <= cpSeq => 
                    /\ seq \in DOMAIN cp.entries
                    /\ cp.entries[seq] = hist[seq]
            /\ seq > cpSeq => 
                    \E i \in DOMAIN manifest.logSegments :
                        LET s == manifest.logSegments[i] IN
                            /\ seq >= s.firstSeq
                            /\ seq <= s.lastSeq
                            /\ seq \in DOMAIN ReadLogSegment(s.id).entries
                            /\ ReadLogSegment(s.id).entries[seq] = hist[seq]

(* INV: ConsistentReads
   Every possible served read is consistent with the
   recorded history of written entries.
*)
ConsistentReads ==
    \A r \in Replicas :
        rAppliedSeq[r] = manifest.headSeq =>
            LET read == rMachineData[r] IN
                rMachineData[r] = auxCommitted

\***********************************************************************
\* LIVENESS
\***********************************************************************

AllValuesWritten ==
    <>[](\A v \in Values :
            \E pos \in DOMAIN auxCommitted :
                auxCommitted[pos] = v)

ReplicaReachesReadyState ==
    \A r \in Replicas :
        rState[r] /= READY ~> rState[r] = READY 

\***************************************************************************
\* Init, Next and Spec
\***************************************************************************

Init ==
    /\ logSegments = <<>>
    /\ checkpoints = <<>>
    /\ manifest = [headSeq     |-> 0, 
                   logSegments |-> <<>>,
                   checkpoint  |-> None,
                   version     |-> 1]
    /\ rOperation = [r \in Replicas |-> IDLE]
    /\ rState = [r \in Replicas |-> IDLE]
    /\ rManifest = [r \in Replicas |-> None]
    /\ rMachineData = [r \in Replicas |-> <<>>]
    /\ rAppliedSeq = [r \in Replicas |-> 0]
    /\ rPendingValue = [r \in Replicas |-> None]
    /\ rPendingSegment = [r \in Replicas |-> None]
    /\ rPendingCp = [r \in Replicas |-> None]
    /\ rCandidateSeq = [r \in Replicas |-> 0]
    /\ rBurned = [r \in Replicas |-> <<>>]
    /\ auxUsedValues = {}
    /\ auxAttemptKey = 1
    /\ auxCommitted = <<>>

Next ==
    \E r \in Replicas :
        \* common actions
        \/ StartReplica(r)
        \/ ReplayWAL(r)
        \* replication
        \/ StartReplicate(r)
        \* checkpoints
        \/ WriteCheckpoint(r)
        \/ CommitCheckpoint(r)
        \* writes
        \/ \E v \in SUBSET Values : StartPublish(r, v)
        \/ ClaimFreeLogSlot(r)
        \/ CheckSlot(r)
        \/ CasManifest(r)
        \/ DeleteOwnLogSegment(r)
        \/ DeleteOneBurnedLogSegment(r)
        
Fairness ==
    \A r \in Replicas :
        /\ WF_vars(StartReplica(r))
        /\ WF_vars(ReplayWAL(r))
        /\ WF_vars(StartReplicate(r))
        /\ WF_vars(CommitCheckpoint(r))
        /\ \A v \in SUBSET Values : SF_vars(StartPublish(r, v))
        /\ WF_vars(ClaimFreeLogSlot(r))
        /\ WF_vars(CheckSlot(r))
        /\ WF_vars(CasManifest(r))
        /\ WF_vars(DeleteOwnLogSegment(r))
        /\ WF_vars(DeleteOneBurnedLogSegment(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness        

=============================================================