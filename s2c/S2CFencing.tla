----------------------------- MODULE S2CFencing -------------------------

(*
    This spec is a variant of the S2C.tla which avoids
    the consistency violation due to GC by implementing
    fencing at the log level.
*)

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences,
        SequencesExt, TLC

CONSTANTS Replicas, \* The set of replica processes
          Values,   \* The set of values to append
          MaxEpoch  \* The maximum epoch to explore (state-space limit)  

\* replica states
CONSTANTS IDLE, REFRESH, ATTEMPT_LEADERSHIP, CATCHUP, JOIN, 
          AWAIT_FOLLOW_RES, READY, COMMIT_BATCH,
          APPEND_TO_LOG, COMMIT_SNAPSHOT, 
          FENCE_FIRST_INDEX, POST_FENCE_VALIDATE, ILLEGAL_STATE

\* Message errors
CONSTANTS OK, NOT_LEADER, TOO_FAR_BEHIND

\* Message types
CONSTANTS FOLLOW_REQ, FOLLOW_RES, SYNC_REQ, SYNC_RES

\* Log batch kinds
CONSTANTS DATA, FENCE

CONSTANTS None

\* Durable state on S3
VARIABLES leaderState,      \* CAS protected leader state manifest file
          log,              \* Id -> Log entry file
          snapshot          \* CAS protected snapshot file

\* The network modelled as bi-directional channels between replica pairs
VARIABLES channel

\* Replica state, e.g. [Replica -> some kind of state]
VARIABLES rState,           \* The state determining it's next action
          rJoined,          \* TRUE=JOINED, FALSE=JOINING
          rLeaderState,     \* Local copy of the leaderState
          rApplyIndex,      \* Locally applied index
          rMachineData,     \* Local state machine data (at the applied index)
          rFollowIndex,     \* The set of follower positions (for replication)
          rPendingBatch,    \* A data batch pending commit
          rTooFarBehind,    \* TRUE=catch up from S3, FALSE=catch up from leader
          rSnapshot,        \* Local copy of snapshot applyIndex and version
          rPendingSnapshot  \* A pending full snapshot to commit
          
VARIABLES auxUsedValues,    
          auxCommitted \* Successful write history         

storeVars == <<leaderState, log, snapshot>>
repStateVars == <<rState, rLeaderState, rJoined>>
repMachineVars == <<rApplyIndex, rMachineData>>
repLeaderVars == <<rFollowIndex, rPendingBatch>>
repFollowVars == <<rTooFarBehind>>
repSnapVars == <<rSnapshot, rPendingSnapshot>>
replicaVars == <<repStateVars, repMachineVars, repLeaderVars,
                 repFollowVars, repSnapVars>>
auxVars == <<auxUsedValues, auxCommitted>>
vars == <<storeVars, replicaVars, auxVars, channel>>

Symmetry ==
      Permutations(Replicas)
          \union Permutations(Values)

\* ****************************************************
\* HELPERS
\* ****************************************************

\* Local state helpers -------------------
Leader(r)      == rLeaderState[r].replica
CommitIndex(r) == IF rLeaderState[r] = None THEN 0 ELSE rLeaderState[r].commitIndex
Epoch(r)       == IF rLeaderState[r] = None THEN 0 ELSE rLeaderState[r].epoch
Version(r)     == IF rLeaderState[r] = None THEN 0 ELSE rLeaderState[r].version
ApplyIndex(r)  == rApplyIndex[r]

IsLeader(r) == /\ rLeaderState[r] /= None
               /\ Leader(r) = r

JoiningStates == {IDLE, REFRESH, ATTEMPT_LEADERSHIP, JOIN, CATCHUP, AWAIT_FOLLOW_RES}

\* Snapshot metadata helpers -------------------
SnapshotIndex(s) == IF s = None THEN 0 ELSE s.applyIndex
SnapshotVersion(s) == IF s = None THEN 0 ELSE s.version
MaybeUpdateSnapshotMetadata(r) ==
    IF SnapshotVersion(rSnapshot[r]) /= SnapshotVersion(snapshot)
    THEN rSnapshot' = [rSnapshot EXCEPT ![r] =
                        [applyIndex |-> SnapshotIndex(snapshot),
                         version    |-> SnapshotVersion(snapshot)]]
    ELSE UNCHANGED rSnapshot

\* Network helpers -------------------
Send(from, to, msg) ==
    channel' = [channel EXCEPT ![to][from] = Append(@, msg)]

Reply(replier, replyTo, sendMsg) ==
    channel' = [channel EXCEPT ![replier][replyTo] = Tail(@),
                               ![replyTo][replier] = Append(@, sendMsg)]

Received(to, from) ==
    channel' = [channel EXCEPT ![to][from] = Tail(@)]

MsgReady(to, from) ==
    Len(channel[to][from]) > 0

TakeNextMsg(to, from) ==
    Head(channel[to][from])

SendFollowReq(r) ==
    /\ Send(r, Leader(r), [type |-> FOLLOW_REQ,
                           applyIndex |-> ApplyIndex(r)])
    /\ rState' = [rState EXCEPT ![r] = AWAIT_FOLLOW_RES]

\* ******************************************************************
\* ACTIONS
\* ******************************************************************

(* ---------------------------------------------------------
    ACTION: RefreshLeaderState

    Either the replica is starting, or it has encountered
    a situation that requires it refresh its leaderState
    and either attempt leadership or (re)start the join
    process.
-----------------------------------------------------------*)

RefreshLeaderState(r) ==
    /\ rState[r] \in {IDLE, REFRESH}
    /\ \/ /\ leaderState = None
          /\ rState' = [rState EXCEPT ![r] = ATTEMPT_LEADERSHIP]
       \/ /\ leaderState /= None 
          /\ rState' = [rState EXCEPT ![r] = JOIN]
    /\ rLeaderState' = [rLeaderState EXCEPT ![r] = leaderState]
    /\ UNCHANGED <<storeVars, channel, auxVars, rJoined, repMachineVars,
                   repLeaderVars, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: AttemptLeadership

    A replica has decided it must assume leadership. This
    happens when the current leaderState has not been
    writing to S3, or at any time when a replica is not
    in the join process. This spec does not model heart
    beats or any failure detection, it simply allows any
    replica to try and assume leadership.

    If the replica experiences a condition failed on
    its leaderState CAS, it returns to REFRESH. Else it
    it starts the join process as the new leader.
-----------------------------------------------------------*)

AttemptLeadership(r) ==
    /\ rState[r] = ATTEMPT_LEADERSHIP
    /\ LET leaderState0 == IF rLeaderState[r] = None
                           THEN [replica      |-> r,
                                 epoch        |-> 1,
                                 commitIndex  |-> 0,
                                 version      |-> 1]
                           ELSE [rLeaderState[r] EXCEPT !.replica = r,
                                                        !.epoch = @ + 1,
                                                        !.version = @ + 1]
       IN IF \/ \* fails put-if-absent
                /\ rLeaderState[r] = None
                /\ leaderState /= None
             \/ \* or fails put-if-match
                /\ rLeaderState[r] /= None
                /\ Version(r) /= leaderState.version
          THEN /\ rState' = [rState EXCEPT ![r] = REFRESH]
               /\ UNCHANGED <<leaderState, rLeaderState>>
          ELSE /\ leaderState' = leaderState0
               /\ rLeaderState' = [rLeaderState EXCEPT ![r] = leaderState0]
               /\ rState' = [rState EXCEPT ![r] = JOIN]
    /\ UNCHANGED <<log, snapshot, auxVars, channel, rJoined, repMachineVars,
                   repLeaderVars, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: JoinAsLeader

    A new leader transitions to CATCHUP if its applyIndex
    is behind the commitIndex (the commitIndex is registered
    in the leaderState). If the new leader is up to date
    it switches to READY where it can start accepting writes.
-----------------------------------------------------------*)

JoinAsLeader(r) ==
    /\ rState[r] = JOIN
    /\ IsLeader(r)
    /\ IF ApplyIndex(r) < CommitIndex(r)
       THEN /\ rState' = [rState EXCEPT ![r] = CATCHUP]
            /\ rJoined' = [rJoined EXCEPT ![r] = FALSE]
            /\ UNCHANGED rSnapshot
       ELSE /\ rState' = [rState EXCEPT ![r] = READY]
            /\ rJoined' = [rJoined EXCEPT ![r] = TRUE]     
            /\ MaybeUpdateSnapshotMetadata(r)
    /\ UNCHANGED <<storeVars, auxVars, channel, rLeaderState, repMachineVars,
                   repLeaderVars, repFollowVars, rPendingSnapshot>>

(* ---------------------------------------------------------
    ACTION: JoinAsFollower

    A follower starts the join process. If, from the previous
    attempt to join, it was told it is too far behind the 
    leader, it switches to CATCHUP, to replay the log on
    S3. Else it sends a follow request to the leader, to
    register with the leader, so that it will start pushing
    log entries to the follower.
-----------------------------------------------------------*)

JoinAsFollower(r) ==
    /\ rState[r] = JOIN
    /\ ~IsLeader(r)
    /\ rJoined' = [rJoined EXCEPT ![r] = FALSE]
    /\ \/ /\ rTooFarBehind[r] = TRUE
          /\ rState' = [rState EXCEPT ![r] = CATCHUP]
          /\ UNCHANGED channel
       \/ /\ rTooFarBehind[r] = FALSE
          /\ SendFollowReq(r)
    /\ UNCHANGED <<storeVars, auxVars, rLeaderState, repMachineVars,
                   repLeaderVars, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: CatchUp

    A leader or follower catches up by:
    1. Restoring from snapshot, if there is one that 
       covers the current apply index of the replica.
    2. Reading log entries from S3 and applying them to
       the local machine data.

    This action repeats until it reaches one of three
    termination conditions:
    1. If no more log entries exist, but we haven't
       reached the commitIndex - 1, then there's
       data loss and we register an illegal state.
       It is legal for the commitIndex to be unwritten,
       but no prior indexes.
    2. We reached the end of the log as the leader
    3. We reached the end of the log as the follower
    
    Once catchup is complete:
    * A leader will check if it has reached the commitIndex.
      If it hasn't it means that the prior leader has not 
      yet written its log entry to that index. Therefore,
      this new leader switches to FENCE_FIRST_INDEX, to
      fence off that index to prevent progress by the stale
      leader. If the leader has caught up completely, it 
      marks itself as JOINED and in the READY state to start
      accepting writes.
    * A follower will send a follow request to the leader,
      so it can start being pushed the latest log entries.
-----------------------------------------------------------*)

\* Snapshot restore -----------------

SnapshotCoversApplyIndex(r) ==
    /\ snapshot /= None
    /\ ApplyIndex(r) < snapshot.applyIndex

NeedsSnapshotRestore(r) ==
    \/ SnapshotVersion(rSnapshot[r]) /= SnapshotVersion(snapshot)
    \/ SnapshotCoversApplyIndex(r)

\* If the snapshot covers the current applyIndex then overwrite
\* local state with the snapshot. No matter what, update
\* the local cached snapshot metadata.
RestoreFromSnapshot(r) ==
    /\ IF SnapshotCoversApplyIndex(r)
       THEN /\ rMachineData' = [rMachineData EXCEPT ![r] = snapshot.entries]
            /\ rApplyIndex' = [rApplyIndex EXCEPT ![r] = snapshot.applyIndex]
       ELSE UNCHANGED <<rMachineData, rApplyIndex>>
    /\ MaybeUpdateSnapshotMetadata(r)
    /\ UNCHANGED <<rState, rJoined, repFollowVars, channel>>

\* Log entry replay -----------------
LogCoversNextIndex(r) ==
    \E id \in DOMAIN log : id = (ApplyIndex(r) + 1)

ReplayOneLogEntry(r) ==
    LET entryId  == ApplyIndex(r) + 1
        logEntry == log[entryId]
    IN
        /\ rMachineData' = [rMachineData EXCEPT ![r] = @ \o logEntry.entries]
        /\ rApplyIndex' = [rApplyIndex EXCEPT ![r] = logEntry.commitIndex]
        /\ UNCHANGED <<rState, rJoined, repFollowVars, rSnapshot, channel>>

\* Illegal state -----------------
\* We've reached the end of the log but not reached the log
\* entry preceding the commit index (which can legally be unwritten)
ShortOfPreCommitIndex(r) ==
    ApplyIndex(r) < CommitIndex(r) - 1

IllegalState(r) ==
    /\ rState' = [rState EXCEPT ![r] = ILLEGAL_STATE]
    /\ UNCHANGED <<repMachineVars, rJoined, repFollowVars, rSnapshot, channel>>

\* Leader finished catchup -----------------
ReachedEndAsLeader(r) == IsLeader(r)
LeaderCompleteCatchup(r) ==
    /\ IF ApplyIndex(r) = CommitIndex(r) - 1
       THEN /\ rState' = [rState EXCEPT ![r] = FENCE_FIRST_INDEX]
            /\ rJoined' = [rJoined EXCEPT ![r] = FALSE]
       ELSE /\ rState' = [rState EXCEPT ![r] = READY]
            /\ rJoined' = [rJoined EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<repMachineVars, repFollowVars, rSnapshot, channel>>

\* Follower finished catchup -----------------
ReachedEndAsFollower(r) == ~IsLeader(r)
FollowerCompleteCatchup(r) ==
    /\ rTooFarBehind' = [rTooFarBehind EXCEPT ![r] = FALSE]
    /\ SendFollowReq(r)
    /\ UNCHANGED <<rJoined, repMachineVars, rSnapshot>>

CatchUp(r) ==
    /\ rState[r] = CATCHUP
    /\ CASE NeedsSnapshotRestore(r)  -> RestoreFromSnapshot(r)
         [] LogCoversNextIndex(r)    -> ReplayOneLogEntry(r)
         [] ShortOfPreCommitIndex(r) -> IllegalState(r)
         [] ReachedEndAsLeader(r)    -> LeaderCompleteCatchup(r)
         [] ReachedEndAsFollower(r)  -> FollowerCompleteCatchup(r)
    /\ UNCHANGED <<storeVars, auxVars, rLeaderState, rPendingBatch,
                   rFollowIndex, rPendingSnapshot>>

(* ---------------------------------------------------------
    ACTION: FenceFirstIndex

    A leader attempts a put-if-absent write of a fence
    object to the current commit index (which the prior
    leader had not written to yet).
    On success, the leader must validate that it is
    still the leader, as a fence write could have 
    succeeded if GC had deleted the prior object, meaning
    that this leader is in fact stale. So to detect that
    situation, the leader switches to POST_FENCE_VALIDATE.

    On condition failed, the leader switches back to
    REFRESH where it must rejoin, and if it is still
    leader, it replays the log entry that the stale
    leader wrote before this replica could write the
    fence object.
-----------------------------------------------------------*)

FenceFirstIndex(r) ==
    /\ rState[r] = FENCE_FIRST_INDEX
    /\ LET index == ApplyIndex(r) + 1 
           fenceObj == [kind        |-> FENCE, 
                        entries     |-> <<>>,
                        commitIndex |-> index] 
       IN
            \/ /\ index \in DOMAIN log
               /\ rState' = [rState EXCEPT ![r] = REFRESH]
               /\ UNCHANGED log
            \/ /\ index \notin DOMAIN log 
               /\ log' = log @@ (index :> fenceObj)
               /\ rState' = [rState EXCEPT ![r] = POST_FENCE_VALIDATE]
    /\ UNCHANGED <<leaderState, snapshot, auxVars, channel, rJoined,
                   rLeaderState,  repSnapVars, repFollowVars, 
                   repLeaderVars, repMachineVars>>

(* ---------------------------------------------------------
    ACTION: PostFenceValidate

    A leader just wrote a fence object and now verifies
    that the leaderState version is still current.
    If it is current, it marks itself as JOINED, 
    advances its apply index (there are no entries to
    apply as the commitIndex is now an empty fence object)
    and switches to READY to start accepting writes.
    If its leaderState is now stale, then another writer
    must have assumed leadership and its fencing write
    was likely a false success (success due to GC freeing
    its address). So the replica switches to REFRESH so
    it can rejoin (likely as a follower).
-----------------------------------------------------------*)

PostFenceValidate(r) ==
    /\ rState[r] = POST_FENCE_VALIDATE
    /\ \/ /\ Version(r) = leaderState.version
          /\ rApplyIndex' = [rApplyIndex EXCEPT ![r] = ApplyIndex(r) + 1]
          /\ rJoined' = [rJoined EXCEPT ![r] = TRUE]
          /\ rState' = [rState EXCEPT ![r] = READY]
       \/ /\ Version(r) /= leaderState.version
          /\ rState' = [rState EXCEPT ![r] = REFRESH]
          /\ UNCHANGED <<rJoined, rApplyIndex>>
    /\ UNCHANGED <<storeVars, auxVars, channel, rLeaderState, repFollowVars, 
                   repLeaderVars, repSnapVars, rMachineData>>

(* ---------------------------------------------------------
    ACTION: RecvFollowReq

    A replica receives a follow request but only processes
    it if it is JOINED.
    If the replica believes it is the leader, it adds
    the follower to its follow index (so it can start
    pushing log entries to it, aka follower synchronization) 
    and sends an OK response.
    If the replica is not the leader, it simply responds
    with a NOT_LEADER error.
-----------------------------------------------------------*)

RecvFollowReq(r, from) ==
    /\ MsgReady(r, from)
    /\ LET msg == TakeNextMsg(r, from) IN
        /\ msg.type = FOLLOW_REQ
        /\ \/ /\ IsLeader(r)
              /\ rState[r] /= CATCHUP \* equivalent of leader-starting check in this spec
              /\ rFollowIndex' = [rFollowIndex EXCEPT ![r][from] = 
                                        [applyIndex |-> msg.applyIndex,
                                         pending    |-> FALSE]]
              /\ Reply(r, from, [type   |-> FOLLOW_RES,
                                 result |-> OK])
           \/ /\ ~IsLeader(r)
              /\ Reply(r, from, [type   |-> FOLLOW_RES,
                                 result |-> NOT_LEADER])
              /\ UNCHANGED rFollowIndex
    /\ UNCHANGED <<storeVars, auxVars, repStateVars, repMachineVars,
                   rPendingBatch, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: RecvFollowRes

    A replica receives a follow response.
    If the replica is not expecting this response, (may
    be another event happened in between, it just discards
    the message). I
    f it is expecting it then:
    * If the response is OK, then the replica marks itself
      as JOINED and switches to READY.
    * If the response is NOT_LEADER, the replica switches
      to REFRESH so it can rejoin, based on fresh 
      information.
-----------------------------------------------------------*)

RecvFollowRes(r, from) ==
    /\ MsgReady(r, from)
    /\ LET msg == TakeNextMsg(r, from) IN
        /\ msg.type = FOLLOW_RES
        /\ IF rState[r] = AWAIT_FOLLOW_RES 
           THEN \/ /\ msg.result = NOT_LEADER
                   /\ rState' = [rState EXCEPT ![r] = REFRESH]
                   /\ UNCHANGED rJoined
                \/ /\ msg.result = OK
                   /\ rState' = [rState EXCEPT ![r] = READY]
                   /\ rJoined' = [rJoined EXCEPT ![r] = TRUE]
           ELSE UNCHANGED <<rState, rJoined>> 
    /\ Received(r, from)
    /\ UNCHANGED <<storeVars, auxVars, rLeaderState, repMachineVars,
                   repLeaderVars, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: ReceiveCommands
    
    Step 1 of a write.
    A joined leader receives a set of commands from a client
    and prepares a log entry batch.
-----------------------------------------------------------*)

ReceiveCommands(r, values) ==
    /\ IsLeader(r)
    /\ rState[r] = READY
    /\ rJoined[r] = TRUE
    /\ Cardinality(values) > 0
    /\ \A v \in values : v \notin auxUsedValues
    /\ LET batch == [kind        |-> DATA,
                     entries     |-> SetToSeq(values),
                     commitIndex |-> CommitIndex(r) + 1]
       IN
          /\ rPendingBatch' = [rPendingBatch EXCEPT ![r] = batch]
          /\ rState' = [rState EXCEPT ![r] = COMMIT_BATCH]
          /\ auxUsedValues' = auxUsedValues \union values
    /\ UNCHANGED <<storeVars, auxCommitted, channel, rLeaderState, rJoined,
                   repMachineVars, rFollowIndex,
                   repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: CommitBatch

    Step 2 of a write.
    A joined leader with a prepared batch attempts
    to commit it by performing a CAS write to the 
    leaderState, updating the commitIndex. Note,
    it advances the commit index before writing the
    batch to the log address space. This is why
    it is legal for the commitIndex to be unwritten.
    If the CAS write fails, the replica switches to
    REFRESH so it can rejoin based on fresh metadata.
-----------------------------------------------------------*)

CommitBatch(r) ==
    /\ IsLeader(r)
    /\ rJoined[r] = TRUE
    /\ rState[r] = COMMIT_BATCH
    /\ \/ /\ Version(r) /= leaderState.version
          /\ rState' = [rState EXCEPT ![r] = JOIN]
          /\ UNCHANGED <<leaderState, rLeaderState>>
       \/ /\ Version(r) = leaderState.version
          /\ LET leaderState0 == [rLeaderState[r] EXCEPT 
                                    !.commitIndex = rPendingBatch[r].commitIndex,
                                    !.version = @ + 1]
             IN
                /\ rState' = [rState EXCEPT ![r] = APPEND_TO_LOG]
                /\ leaderState' = leaderState0
                /\ rLeaderState' = [rLeaderState EXCEPT ![r] = leaderState0]
    /\ UNCHANGED <<log, snapshot, auxVars, channel, rJoined, repMachineVars,
                   repLeaderVars, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: AppendToLog

    Step 3 of a write.
    A leader who has just advanced the commit index
    in the leaderState on S3, now performs a put-if-absent
    to the log address space, where the address is
    based on the index of the log entry batch.

    If the put succeeds, the write is complete and
    the contents are applied to the local machine
    state and the applied index advanced.
    The contents are also registered in the 
    auxCommitted variable for safety property checking.

    If the put failed, the replica switches to REFRESH,
    so it can rejoin based on fresh metadata.
-----------------------------------------------------------*)

AppendToLog(r) ==
    /\ IsLeader(r)
    /\ rJoined[r] = TRUE
    /\ rState[r] = APPEND_TO_LOG
    /\ \/ /\ rPendingBatch[r].commitIndex \in DOMAIN log
          /\ rState' = [rState EXCEPT ![r] = REFRESH]
          /\ UNCHANGED <<repMachineVars, log, auxCommitted>>
       \/ /\ rPendingBatch[r].commitIndex \notin DOMAIN log
          /\ log' = log @@ (rPendingBatch[r].commitIndex :> rPendingBatch[r])
          /\ rMachineData' = [rMachineData EXCEPT ![r] = @ \o rPendingBatch[r].entries]
          /\ rApplyIndex' = [rApplyIndex EXCEPT ![r] = rPendingBatch[r].commitIndex]
          /\ rState' = [rState EXCEPT ![r] = READY]
          /\ auxCommitted' = auxCommitted \o rPendingBatch[r].entries
    /\ rPendingBatch' = [rPendingBatch EXCEPT ![r] = None]
    /\ UNCHANGED <<leaderState, snapshot, auxUsedValues, channel, rLeaderState,
                   rJoined, rFollowIndex, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: SendSyncReq

    A leader tries to send a log entry to a registered
    follower, based on the follower's apply index (which
    was first recorded on receipt of its follow request).
    
    Three cases can occur:
    1. The log has the next index to sync and it is a
       DATA entry. So send the sync request.
    2. The log has the next index to sync but it is a
       FENCE entry. So send nothing, and advance the
       follow index for this follower.
    3. The next index is not covered by the log (due to
       snapshotting and GC or due to fencing), 
       so it sends a sync request with TOO_FAR_BEHIND
       error (so the follower bootstraps from S3 instead).
-----------------------------------------------------------*)

LogIndexWritten(r, to) ==
    LET nextIndex == rFollowIndex[r][to].applyIndex + 1 IN 
        \/ CommitIndex(r) > nextIndex 
        \/ /\ CommitIndex(r) = nextIndex
           /\ \/ nextIndex \in DOMAIN log 
              \/ nextIndex <= SnapshotIndex(snapshot)
           \* the log might not have the commit index

SendSyncReq(r, to) ==
    /\ IsLeader(r)
    /\ rJoined[r] = TRUE
    /\ rFollowIndex[r][to] /= None \* follower connected
    /\ rFollowIndex[r][to].pending = FALSE \* ready to push batch to follower
    /\ LogIndexWritten(r, to) 
    /\ LET index == rFollowIndex[r][to].applyIndex + 1 
           inLog == index \in DOMAIN log
           isData == log[index].kind = DATA
       IN
            CASE inLog /\ isData ->
                    /\ Send(r, to, [type        |-> SYNC_REQ,
                                    error       |-> None,
                                    batch       |-> log[index],
                                    commitIndex |-> index])
                    /\ rFollowIndex' = [rFollowIndex EXCEPT ![r][to].pending = TRUE]
              [] inLog /\ ~isData ->
                    /\ rFollowIndex' = [rFollowIndex EXCEPT ![r][to] =
                                            [applyIndex |-> index,
                                             pending    |-> FALSE]]
                    /\ UNCHANGED channel
              [] OTHER -> 
                    /\ Send(r, to, [type        |-> SYNC_REQ,
                                    error       |-> TOO_FAR_BEHIND,
                                    batch       |-> None,
                                    commitIndex |-> 0])             
                    /\ rFollowIndex' = [rFollowIndex EXCEPT ![r][to] = None]
    /\ UNCHANGED <<storeVars, auxVars, repStateVars, repMachineVars,
                   rPendingBatch, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: RecvSyncReq

    A replica receives a sync request. If the replica
    is a leader, it just replies with its current
    apply index. Eventually the sender will realize that
    this replica is not a follower.

    Else, if the message has the TOO_FAR_BEHIND error,
    the replica sets its rTooFarBehind to TRUE and
    switches to REFRESH where it will rejoin. In the
    join process, due to its rTooFarBehind value, it
    will do catchup from S3, then reregister as a follower
    by sending a follow request to the leader.

    Else, if the message is OK and the batch index to equal
    to the applyIndex + 1, the follower applies the
    batch entries to its state machine and sets its local
    apply index to the index of the batch. 
    Otherwise, it acknowledges its current index without
    applying the batch.
-----------------------------------------------------------*)

CanAcceptSync(r, msg) ==
    /\ msg.error = None
    /\ ~IsLeader(r) 
    /\ msg.commitIndex = ApplyIndex(r) + 1

TooFarBehind(r, msg) ==
    /\ ~IsLeader(r)
    /\ msg.error = TOO_FAR_BEHIND

RecvSyncReq(r, from) ==
     /\ MsgReady(r, from)
     /\ LET msg == TakeNextMsg(r, from)
            replyApplyIndex == IF CanAcceptSync(r, msg) THEN msg.commitIndex
                               ELSE ApplyIndex(r)
        IN
            /\ msg.type = SYNC_REQ
            /\ CASE CanAcceptSync(r, msg) ->
                        /\ rMachineData' = [rMachineData EXCEPT ![r] = @ \o msg.batch.entries]
                        /\ rApplyIndex' = [rApplyIndex EXCEPT ![r] = msg.commitIndex]
                        /\ UNCHANGED <<repFollowVars, rState>>
                 [] TooFarBehind(r, msg) ->
                        /\ rTooFarBehind' = [rTooFarBehind EXCEPT ![r] = TRUE]
                        /\ rState' = [rState EXCEPT ![r] = REFRESH]
                        /\ UNCHANGED repMachineVars
                 [] OTHER ->
                        UNCHANGED <<repMachineVars, repFollowVars, rState>>
            /\ Reply(r, from, [type       |-> SYNC_RES,
                               applyIndex |-> replyApplyIndex])
    /\ UNCHANGED <<storeVars, auxVars, rLeaderState, rJoined,
                   repLeaderVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: RecvSyncRes

    A replica receives a sync response.

    If the replica is a joined leader and the follower is
    registered, it advances its apply index. Else
    it discards the message.
-----------------------------------------------------------*)

RecvSyncRes(r, from) ==
    /\ MsgReady(r, from)
    /\ LET msg == TakeNextMsg(r, from) IN
        /\ msg.type = SYNC_RES
        /\ IF /\ IsLeader(r)
              /\ rJoined[r] = TRUE
              /\ rFollowIndex[r][from] /= None
           THEN rFollowIndex' = [rFollowIndex EXCEPT ![r][from] = 
                                        [applyIndex |-> msg.applyIndex,
                                         pending    |-> FALSE]]
           ELSE rFollowIndex' = [rFollowIndex EXCEPT ![r][from] = None]
    /\ Received(r, from)
    /\ UNCHANGED <<storeVars, auxVars, repStateVars, repMachineVars,
                   rPendingBatch, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: TryBecomeLeader

    A replica that is not in a joining state who believes
    it is not a leader switches to ATTEMPT_LEADERSHIP.
    In reality, this will be based on some kind of
    failure detection, such as heartbeats. This spec
    just allows for replicas to attempt leadership
    when they want.
    For state space limitation, this is only enabled
    if the current leaderState.epoch has not reached
    its max value.
-----------------------------------------------------------*)

TryBecomeLeader(r) ==
    /\ rState[r] \notin JoiningStates
    /\ ~IsLeader(r)
    /\ leaderState.epoch < MaxEpoch
    /\ rLeaderState' = [rLeaderState EXCEPT ![r] = leaderState]
    /\ rState' = [rState EXCEPT ![r] = ATTEMPT_LEADERSHIP]
    /\ UNCHANGED <<storeVars, auxVars, channel, rJoined, repMachineVars,
                   repLeaderVars, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: DetectLeaderChange

    A replica that is not in a joining state detects
    a leader change has occuured (as its cached leader
    epoch no longer matches the epoch stored in the 
    leaderState on S3).
    It resets its follow index state, wipes its local
    leaderState and switches to REFRESH to rejoin based
    on the fresh leaderState.
-----------------------------------------------------------*)

DetectLeaderChange(r) ==
    /\ rState[r] \notin JoiningStates
    /\ rLeaderState[r] /= None
    /\ Epoch(r) /= leaderState.epoch
    /\ rState' = [rState EXCEPT ![r] = REFRESH]
    /\ rFollowIndex' = [rFollowIndex EXCEPT ![r] = [rr \in Replicas |-> None]]
    /\ rLeaderState' = [rLeaderState EXCEPT ![r] = None]
    /\ UNCHANGED <<storeVars, auxVars, channel, rJoined, repMachineVars,
                   rPendingBatch, repFollowVars, repSnapVars>>

(* ---------------------------------------------------------
    ACTION: TakeSnapshot

    A leader prepares a snapshot of its machine data,
    as long as its apply index is ahead of the
    current cached snapshot index. It then switches
    to COMMIT_SNAPSHOT to attempt to commit it.
-----------------------------------------------------------*)

TakeSnapshot(r) ==
    /\ IsLeader(r)
    /\ rState[r] = READY
    /\ ApplyIndex(r) > SnapshotIndex(rSnapshot[r])
    /\ rPendingSnapshot' = [rPendingSnapshot EXCEPT ![r] =
                                [entries    |-> rMachineData[r],
                                 applyIndex |-> ApplyIndex(r),
                                 epoch      |-> Epoch(r),
                                 version    |-> SnapshotVersion(rSnapshot[r]) + 1]]
    /\ rState' = [rState EXCEPT ![r] = COMMIT_SNAPSHOT]
    /\ UNCHANGED <<storeVars, auxVars, channel, rLeaderState, rJoined,
                   repMachineVars, repLeaderVars, repFollowVars, rSnapshot>>

(* ---------------------------------------------------------
    ACTION: CommitSnapshot

    A leader attempt either a put-if-absent (if no
    existing snapshot exists in S3) or a put-if-match
    (if one does exist) based on the snapshot version.
    If the put succeeds then the replica continues
    as leader, if it fails (condition failed), the
    replica switches to REFRESH to rejoin based on
    fresh metadata.

    NOTE! In the implementation, if a write conflict
    occurs, the implementation treats it as a leadership
    change. If the new leader epoch matches the
    epoch used to attempt the snapshot write, it enters
    an ILLEGAL_STATE.  
    But a snapshot ETag conflict does not necessarily
    imply a leadership change. For example: a stale 
    leader writes a snapshot at index i, then the new leader
    tries to write the same snapshot at index i. In the
    impl, the new leader would enter an illegal
    state. This spec does treat a snapshot write conflict
    as a leader change.
-----------------------------------------------------------*)

IsMatch(r) ==
    \/ snapshot = None
    \/ /\ snapshot /= None
       /\ SnapshotVersion(rSnapshot[r]) = snapshot.version

CommitSnapshot(r) ==
    /\ rState[r] = COMMIT_SNAPSHOT
    /\ LET snap == rPendingSnapshot[r] IN
        /\ \/ /\ IsMatch(r)
              /\ snapshot' = snap
              /\ rSnapshot' = [rSnapshot EXCEPT ![r] = 
                                    [applyIndex |-> snap.applyIndex,
                                     version    |-> snap.version]]
              /\ rState' = [rState EXCEPT ![r] = READY]
           \/ /\ ~IsMatch(r)
              /\ rState' = [rState EXCEPT ![r] = REFRESH]
              /\ UNCHANGED <<snapshot, rSnapshot>>
        /\ rPendingSnapshot' = [rPendingSnapshot EXCEPT ![r] = None]
        /\ UNCHANGED <<leaderState, log, auxVars, channel, rLeaderState, rJoined,
                       repMachineVars, repLeaderVars, repFollowVars>>

(* ---------------------------------------------------------
    ACTION: GarbageCollect

    An abstracted garbage collection process, which
    attempts to delete a DATA batch whose index
    is below the current snapshot index.
-----------------------------------------------------------*)

GarbageCollect ==
    \E index \in DOMAIN log :
        /\ index < SnapshotIndex(snapshot)
        /\ index \in DOMAIN log
        /\ log[index].kind = DATA
        /\ log' = [i \in DOMAIN log \ {index} |-> log[i]]
        /\ UNCHANGED <<leaderState, snapshot, replicaVars, 
                       auxVars, channel>>

\* ****************************************************
\* Data model
\* ****************************************************

\* DURABLE STATE START -----------------------    

LeaderStateType ==
    [replica: Replicas,
     epoch: Nat,
     commitIndex: Nat,
\*     followers: SUBSET Replicas, \* Omitted as only needed for optimization
     version: Nat] \union {None}

BatchType == 
    [kind: {DATA, FENCE},
     entries: Seq(Values),
     commitIndex: Nat]

ValidLog ==
    \A id \in DOMAIN log : 
        /\ id \in Nat
        /\ log[id] \in BatchType

SnapshotType == 
        [entries: Seq(Values), 
         applyIndex: Nat,
         epoch: Nat, 
         version: Nat] \union {None}

ValidDurableStateOnS3 ==
    /\ leaderState \in LeaderStateType
    /\ ValidLog
    /\ snapshot \in SnapshotType

\* DURABLE STATE END -----------------------    

\* REPLICA STATE START ---------------------

FollowerIndexType == 
    [applyIndex: Nat, pending: BOOLEAN] 

SnapshotRef ==
    [applyIndex: Nat, version: Nat]

ValidReplicasState ==
    /\ rState \in [Replicas -> {IDLE, REFRESH, ATTEMPT_LEADERSHIP, CATCHUP, JOIN, 
                                AWAIT_FOLLOW_RES, READY, COMMIT_BATCH,
                                APPEND_TO_LOG, COMMIT_SNAPSHOT, 
                                FENCE_FIRST_INDEX, POST_FENCE_VALIDATE, ILLEGAL_STATE}]
    /\ rJoined \in [Replicas -> BOOLEAN]
    /\ rLeaderState \in [Replicas -> LeaderStateType \union {None}]
    /\ rApplyIndex \in [Replicas -> Nat]
    /\ rFollowIndex \in [Replicas -> 
                            [Replicas -> FollowerIndexType \union {None}]]
    /\ rMachineData \in [Replicas -> Seq(Values)]
    /\ rPendingBatch \in [Replicas -> BatchType \union {None}]
    /\ rSnapshot \in [Replicas -> SnapshotRef \union {None}]
    /\ rPendingSnapshot \in [Replicas -> SnapshotType \union {None}]
    /\ rTooFarBehind \in [Replicas -> BOOLEAN]

\* REPLICA STATE END -----------------------

\* NETWORK AND MESSAGES START --------------

MessageType ==
    [type: {FOLLOW_REQ},
     applyIndex: Nat]
        \union
    [type: {FOLLOW_RES},
     result: {OK, NOT_LEADER}]
        \union
    [type: {SYNC_REQ},
     error: {None, TOO_FAR_BEHIND},
     commitIndex: Nat,
     batch: BatchType \union {None}]
        \union
    [type: {SYNC_RES},
     applyIndex: Nat]

ChannelType ==
    [Replicas -> [Replicas -> Seq(MessageType)]]

\* NETWORK AND MESSAGES END ----------------         

TypeOK ==
    /\ ValidDurableStateOnS3
    /\ ValidReplicasState
    /\ channel \in ChannelType
    /\ auxUsedValues \in SUBSET Values
    /\ auxCommitted \in Seq(Values)

\* ****************************************************
\* Properties
\* ****************************************************

\* INV: ValidReplicas
ValidReplicas ==
    \A r \in Replicas :
        rState[r] /= ILLEGAL_STATE

\* INV: ValidLeaderState
ValidLeaderState ==
    \* All replicas with up to date cached leaderState versions
    \* have cached leaderState that matches S3
    /\ \A r \in Replicas :
        (/\ rLeaderState[r] /= None 
         /\ Version(r) = leaderState.version) =>
            rLeaderState[r] = leaderState
    \* No two replicas at the same leaderState version have
    \* different leaderState
    /\ \A r1, r2 \in Replicas :
        Version(r1) = Version(r2) =>
            rLeaderState[r1] = rLeaderState[r2]

\* INV: ReplicaStateIsCommittedPrefix
\* Every replica's machine data is a prefix of the 
\* successful write history.
ReplicaStateIsCommittedPrefix ==
    \A r \in Replicas :
        IsPrefix(rMachineData[r], auxCommitted)

\* INV: SnapshotIsCommittedPrefix
\* The current snapshot is a prefix of the successful write history.
SnapshotIsCommittedPrefix ==
    IF snapshot = None THEN TRUE
    ELSE IsPrefix(snapshot.entries, auxCommitted)

\* INV: LogMatchesCommittedHistory
\* The log has contiguous batch indexes starting at 1, and its entries
\* in index order equal the successful write history.
LogMatchesCommittedHistory ==
    LET snapshotIndex == SnapshotIndex(snapshot)
        snapshotEntries == IF snapshot = None THEN <<>> ELSE snapshot.entries
        suffixIndexes == {i \in DOMAIN log : i > snapshotIndex}
        batchCount == Cardinality(suffixIndexes)
    \* Counting the suffix avoids searching for its maximum index.
    IN  IF suffixIndexes = (snapshotIndex + 1)..(snapshotIndex + batchCount)
        THEN LET batches == [offset \in 1..batchCount |->
                                 log[snapshotIndex + offset].entries]
             IN snapshotEntries \o FlattenSeq(batches) = auxCommitted
        ELSE FALSE

\* Liveness property: AllReplicasJoin
\* No replica gets stuck in the join process
AllReplicasJoin ==
    \A r \in Replicas :
        <>[](rJoined[r] = TRUE)
        
\* Liveness property: AllReplicasReachMaxEpoch
\* Given attempts at leadership are weakly fair,
\* the cluster should reach the max epoch
AllReplicasReachMaxEpoch ==
    \A r \in Replicas :
        <>[](/\ rLeaderState[r] /= None
             /\ rLeaderState[r].epoch = MaxEpoch)

\* ****************************************************
\* INIT, NEXT and Spec
\* ****************************************************

Init ==
    /\ leaderState = None
    /\ log = <<>>
    /\ snapshot = None
    /\ channel = [dest \in Replicas |->
                    [source \in Replicas |-> <<>>]]
    /\ rState = [r \in Replicas |-> IDLE]
    /\ rJoined = [r \in Replicas |-> FALSE]
    /\ rLeaderState = [r \in Replicas |-> None]     
    /\ rApplyIndex = [r \in Replicas |-> 0]
    /\ rFollowIndex = [r \in Replicas |-> 
                            [other \in Replicas |-> None]]
    /\ rPendingBatch = [r \in Replicas |-> None]
    /\ rMachineData = [r \in Replicas |-> <<>>]
    /\ rSnapshot = [r \in Replicas |-> None]
    /\ rPendingSnapshot = [r \in Replicas |-> None]
    /\ rTooFarBehind = [r \in Replicas |-> FALSE]
    /\ auxUsedValues = {}
    /\ auxCommitted = <<>>

Next ==
    \E r \in Replicas :
        \* Join process
        \/ RefreshLeaderState(r)
        \/ AttemptLeadership(r) \* also leader changes
        \/ JoinAsLeader(r)
        \/ JoinAsFollower(r)
        \/ CatchUp(r)
        \/ FenceFirstIndex(r)
        \/ PostFenceValidate(r)
        \/ \E from \in Replicas :
            \/ RecvFollowReq(r, from)
            \/ RecvFollowRes(r, from)
        \* Write process
        \/ \E values \in SUBSET Values :
            ReceiveCommands(r, values)
        \/ CommitBatch(r)
        \/ AppendToLog(r)
        \* Leader->follower replication
        \/ \E other \in Replicas :
            \/ SendSyncReq(r, other)
            \/ RecvSyncReq(r, other)
            \/ RecvSyncRes(r, other)
        \* Leader changes
        \/ TryBecomeLeader(r)
        \/ DetectLeaderChange(r)
        \* Snapshotting and GC
        \/ TakeSnapshot(r)
        \/ CommitSnapshot(r)
        \/ GarbageCollect
        
Fairness ==
    \A r \in Replicas :
        /\ WF_vars(RefreshLeaderState(r))
        /\ WF_vars(AttemptLeadership(r))
        /\ WF_vars(JoinAsLeader(r))
        /\ WF_vars(JoinAsFollower(r))
        /\ WF_vars(CatchUp(r))
        /\ WF_vars(FenceFirstIndex(r))
        /\ WF_vars(PostFenceValidate(r))
        /\ \A other \in Replicas :
            /\ WF_vars(RecvFollowReq(r, other))
            /\ WF_vars(RecvFollowRes(r, other))
            /\ WF_vars(SendSyncReq(r, other))
            /\ WF_vars(RecvSyncReq(r, other))
            /\ WF_vars(RecvSyncRes(r, other))
        /\ WF_vars(CommitBatch(r))
        /\ WF_vars(AppendToLog(r))
        /\ WF_vars(TryBecomeLeader(r))
        /\ WF_vars(DetectLeaderChange(r))
        /\ WF_vars(CommitSnapshot(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
