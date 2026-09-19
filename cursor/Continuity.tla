----------------------------- MODULE Continuity -------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Replicas, \* The set of replica processes
          GarbageCollectors, \* The set of garbage collector processes
          Values,   \* The set of values to push
          IDs       \* The set of packfile ids to write to

\* Replica/GC states
CONSTANTS IDLE, READY, GET_WAL_INDEX, APPEND_WAL_INDEX, REFETCH, 
          REPLAY_WAL_INDEX, SERVE_READ, ILLEGAL_STATE, COMMIT_SNAPSHOT,
          NOT_FOUND, DELETE 

\* Replica actions
CONSTANTS WRITE, READ, REPLICATE

CONSTANTS NIL

ASSUME Cardinality(IDs) = Cardinality(Values)

WritablePositions == 1..Cardinality(Values)

VARIABLES walPackFile,      \* ID -> Packfile (on S3)
          walIndex,         \* The reference file in S3
          snapshot,         \* ID -> Snapshot (snapshot of the repo - simplified compaction)
          rAction,          \* Replica -> write/read/replicate
          rState,           \* Replica -> state
          rPendingPackFile, \* Replica -> pending packfile id to commit to reference file
          rWalIndex,        \* Replica -> local copy of the WAL index file
          rRepo,            \* Replica -> the Git repo state (a sequence of values in this spec)
          gcState,          \* GC -> state
          gcDeleteSet       \* GC -> The set of packfiles to delete

\* Auxilliary variables for invariants
VARIABLES auxUsedValues,    \* The set of proposed values (aka packfile contents)
          auxUsedIds,       \* The set of IDs of written packfiles
          auxWrittenValues, \* The sequence of successful writes (of values)
          auxReadRepos      \* Position -> Set of repos read at that position

replicaVars == <<rAction, rState, rPendingPackFile, rWalIndex, rRepo>>
storeVars == <<walPackFile, walIndex, snapshot>>
gcVars == <<gcState, gcDeleteSet>>
auxVars == <<auxUsedValues, auxUsedIds, auxReadRepos, auxWrittenValues>>
vars == <<storeVars, replicaVars, gcVars, auxVars>>

Symmetry ==
    Permutations(Replicas)
        \union Permutations(GarbageCollectors)
        \union Permutations(Values)
        \union Permutations(IDs)

Read(id) == IF id \in DOMAIN walPackFile
            THEN walPackFile[id]
            ELSE NIL

RefreshWalIndex(r) ==
    rWalIndex' = [rWalIndex EXCEPT ![r] = walIndex]

InstallNewWalIndex(r, newIndex) ==
    /\ walIndex' = newIndex
    /\ rWalIndex' = [rWalIndex EXCEPT ![r] = newIndex]

IsCaughtUp(r, currIndex) ==
    Len(rRepo[r]) = currIndex.nextPos - 1
    
ResetToReady(r) ==
    /\ rState' = [rState EXCEPT ![r] = READY]
    /\ rAction' = [rAction EXCEPT ![r] = READY]    

\***********************************************************************
\* ACTIONS
\***********************************************************************

(* COMMON ACTIONS --------------------------------------*)

(* ---------------------------------------------------------
    ACTION: StartReplica
    A replica starts by reading the current WAL index.
    If the replica is caught up it transitions to READY
    where it can start serving reads and writes, else
    it transitions to REPLAY_WAL_INDEX to catch up.
-----------------------------------------------------------*)

StartReplica(r) ==
    /\ rState[r] = IDLE
    /\ RefreshWalIndex(r)
    /\ IF IsCaughtUp(r, walIndex)
       THEN ResetToReady(r)
       ELSE /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL_INDEX]
            /\ rAction' = [rAction EXCEPT ![r] = REPLICATE]
    /\ UNCHANGED <<storeVars, rPendingPackFile, 
                   rRepo, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: ReplayWalIndex
    A replica makes progress replaying the local WAL index.
    There are many scenarios when a replica must catch-up by
    applying the latest packfiles to its local repo.
    This action is repeated until either all entries have
    been applied or an entry is not found.
-----------------------------------------------------------*)

StateAfterReplay(r) ==
    CASE rAction[r] = WRITE     -> APPEND_WAL_INDEX
      [] rAction[r] = READ      -> SERVE_READ
      [] rAction[r] = REPLICATE -> READY
      [] OTHER -> ILLEGAL_STATE

ActionAfterReplay(r) ==
    IF rAction[r] = REPLICATE THEN READY ELSE rAction[r]

ReplayWalIndex(r) ==
    /\ rState[r] = REPLAY_WAL_INDEX
    /\ LET nextPos    == Len(rRepo[r]) + 1
           packFileId == rWalIndex[r].entries[nextPos]
           packFile   == Read(packFileId)
       IN
           CASE 
             \* CASE 1: Replay complete, transition to next state
                nextPos = rWalIndex[r].nextPos ->
                   /\ rState' = [rState EXCEPT ![r] = StateAfterReplay(r)]
                   /\ rAction' = [rAction EXCEPT ![r] = ActionAfterReplay(r)] 
                   /\ UNCHANGED rRepo
             \* CASE 2: Current position behind the compaction frontier, 
             \*         load the snapshot instead, then replay from there
             [] nextPos <= rWalIndex[r].snapshotId ->
                   /\ rRepo' = [rRepo EXCEPT ![r] = snapshot[rWalIndex[r].snapshotId]]
                   /\ UNCHANGED <<rAction, rState>>
             \* CASE 3: The packfile to read does not exist
             [] packFile = NIL ->
                   /\ rState' = [rState EXCEPT ![r] = NOT_FOUND]
                   /\ UNCHANGED <<rAction, rRepo>>
             \* CASE 4: Read and apply the packfile
             [] OTHER ->
                   /\ rRepo' = [rRepo EXCEPT ![r] = Append(@, packFile)]
                   /\ UNCHANGED <<rAction, rState>>
    /\ UNCHANGED <<storeVars, rPendingPackFile, rWalIndex, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: ValidateNotFound
    A replica did not find an expected packfile during
    WAL index replay. If checks if its local WAL index
    version matches the current WAL index. If it matches
    then its hit an illegal state (a valid packfile does
    not exist). If the version does not match, then the
    replica refreshes its copy of the WAL index and 
    transitions back to REPLAY_WAL_INDEX.
-----------------------------------------------------------*)
ValidateNotFound(r) ==
    /\ rState[r] = NOT_FOUND
    /\ \/ /\ rWalIndex[r].version = walIndex.version
          /\ rState' = [rState EXCEPT ![r] = ILLEGAL_STATE]
          /\ UNCHANGED rWalIndex
       \/ /\ rWalIndex[r].version /= walIndex.version
          /\ RefreshWalIndex(r)
          /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL_INDEX]
    /\ UNCHANGED <<storeVars, rAction, rPendingPackFile, rRepo, gcVars, auxVars>>    

(* WRITE ACTIONS --------------------------------------*)

(* ---------------------------------------------------------
    ACTION: WritePackFile
    A client pushes value v (packfile) to replica r. 
    The replica writes the packfile to S3.

    Note auxUsedIds and auxUsedValues ensure that every
    written value is unique and every id is unique.
-----------------------------------------------------------*)
WritePackFile(r, v) ==
    /\ rState[r] = READY
    /\ v \notin auxUsedValues
    /\ \E id \in IDs :
        /\ id \notin auxUsedIds
        /\ walPackFile' = walPackFile @@ (id :> v)
        /\ rAction' = [rAction EXCEPT ![r] = WRITE]
        /\ rState' = [rState EXCEPT ![r] = GET_WAL_INDEX]
        /\ rPendingPackFile' = [rPendingPackFile EXCEPT ![r] = 
                                    [id   |-> id, data |-> v]]
        /\ auxUsedIds' = auxUsedIds \union {id}
        /\ auxUsedValues' = auxUsedValues \union {v}
    /\ UNCHANGED <<walIndex, snapshot, rWalIndex, rRepo, gcVars,
                   auxReadRepos, auxWrittenValues>>

(* ---------------------------------------------------------
    ACTION: GetWalIndex
    A replica just wrote a packfile and now refreshes the
    WAL index. If the local repo is behind the WAL then
    the replica transitions to REPLAY_WAL_INDEX, else
    it transitions to APPEND_WAL_INDEX.
-----------------------------------------------------------*)
GetWalIndex(r) ==
    /\ rState[r] = GET_WAL_INDEX
    /\ RefreshWalIndex(r)
    /\ rState' = [rState EXCEPT ![r] = IF IsCaughtUp(r, walIndex)
                                       THEN APPEND_WAL_INDEX
                                       ELSE REPLAY_WAL_INDEX]
    /\ UNCHANGED <<storeVars, rAction, rPendingPackFile, 
                   rRepo, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: AppendToWalIndex
    A replica appends its packfile reference to its local
    WAL index and performs a CAS write to the WAL index on
    S3 (based on the version aka etag).
    If the condition fails it's a write conflict so the 
    writer transitions back to GET_WAL_INDEX so it
    can try again with a non-stale index.
    If the write succeeded, the replica applies the packfile
    to its local repo. The replica transitions back to
    READY.
-----------------------------------------------------------*)

AppendToWalIndex(r) ==
    /\ rState[r] = APPEND_WAL_INDEX
    /\ LET newEntries  == rWalIndex[r].entries @@ 
                            (rWalIndex[r].nextPos :> rPendingPackFile[r].id)
           currVersion == rWalIndex[r].version 
           newVersion  == rWalIndex[r].version + 1
           newWalIndex == [rWalIndex[r] EXCEPT !.entries = newEntries,
                                               !.nextPos = @ + 1,
                                               !.version = newVersion]
       IN \/ /\ walIndex.version = currVersion
             /\ InstallNewWalIndex(r, newWalIndex)
             /\ ResetToReady(r)
             /\ rRepo' = [rRepo EXCEPT ![r] = Append(@, rPendingPackFile[r].data)]
             /\ rPendingPackFile' = [rPendingPackFile EXCEPT ![r] = NIL]
             /\ auxWrittenValues' = Append(auxWrittenValues, rPendingPackFile[r].data)
          \/ /\ walIndex.version /= currVersion
             /\ rState' = [rState EXCEPT ![r] = GET_WAL_INDEX]
             /\ UNCHANGED <<walIndex, rWalIndex, rAction, rRepo, rPendingPackFile, auxWrittenValues>>
    /\ UNCHANGED <<walPackFile, snapshot, gcVars, auxUsedValues, auxUsedIds, auxReadRepos>>

(* REPLICATION ACTIONS --------------------------------------*)

(* ---------------------------------------------------------
    ACTION: StartReplicate
    A replica tests if the WAL index version has changed,
    if so, it refreshes its local copy. If the replica
    is still caught up, it remains in READY state. If it
    is behind, it transitions to REPLAY_WAL_INDEX
-----------------------------------------------------------*)

StartReplicate(r) ==
    /\ rState[r] = READY
    /\ rWalIndex[r].version /= walIndex.version
    /\ RefreshWalIndex(r)
    /\ IF IsCaughtUp(r, walIndex)
       THEN UNCHANGED <<rAction, rState>>
       ELSE /\ rAction' = [rAction EXCEPT ![r] = REPLICATE]
            /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL_INDEX]
    /\ UNCHANGED <<storeVars, rPendingPackFile, rRepo, gcVars, auxVars>>
    
(* READ ACTIONS --------------------------------------*)

(* ---------------------------------------------------------
    ACTION: StartRead
    A replica receives a fetch request from a client. It
    tests if its local WAL index is up-to-date by
    checking the WAL index version.
    If the version is up-to-date, there is no need to
    refresh its copy of the index. If the version has
    changed, it refreshes its copy.
    
    Next, if the replica has already applied all WAL 
    entries to its local repo, it transitions to 
    SERVE_READ. Else it transitions to REPLAY_WAL_INDEX 
    first.
-----------------------------------------------------------*)

StartRead(r) ==
    /\ rState[r] = READY
    /\ IF rWalIndex[r].version = walIndex.version THEN
            /\ rState' = [rState EXCEPT ![r] = 
                                IF IsCaughtUp(r, rWalIndex[r])
                                THEN SERVE_READ
                                ELSE REPLAY_WAL_INDEX]
            /\ UNCHANGED rWalIndex
       ELSE
            /\ RefreshWalIndex(r)
            /\ rState' = [rState EXCEPT ![r] = 
                                IF IsCaughtUp(r, walIndex)
                                THEN SERVE_READ
                                ELSE REPLAY_WAL_INDEX]
    /\ rAction' = [rAction EXCEPT ![r] = READ]
    /\ UNCHANGED <<storeVars, rPendingPackFile, rRepo, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: ServeRead
    A replica serves a client fetch request from its local
    repo state.
    The served repo state is recorded against the position
    in the WAL, for invariant checking.
-----------------------------------------------------------*)

ServeRead(r) ==
    /\ rState[r] = SERVE_READ
    /\ LET readPos == rWalIndex[r].nextPos-1 IN
        /\ auxReadRepos' = [auxReadRepos EXCEPT ![readPos] = @ \union {rRepo[r]}]
        /\ ResetToReady(r)
    /\ UNCHANGED <<storeVars, rRepo, rPendingPackFile, rWalIndex, auxUsedIds,
                   gcVars, auxUsedValues, auxWrittenValues>>

(* SNAPSHOT ACTIONS (aka simplified compaction) -----------*)

(* ---------------------------------------------------------
    ACTION: WriteSnapshot
    Step 1 of simplified compaction. The WAL prefix is
    compacted by rolling it up into a snapshot. The
    address of the snapshot is its position in the WAL.
    We're not implementing a git-type compaction as we don't
    actually care about git in this WAL-on-S3 survey.
-----------------------------------------------------------*)

WriteSnapshot(r) ==
    /\ rState[r] = READY
    /\ rRepo[r] /= <<>>
    /\ LET lastSnapshotId == rWalIndex[r].snapshotId
           nextSnapshotId == rWalIndex[r].nextPos - 1
       IN
          /\ nextSnapshotId >= lastSnapshotId 
          /\ nextSnapshotId \notin DOMAIN snapshot
          /\ snapshot' = snapshot @@ (nextSnapshotId :> rRepo[r])
          /\ rState' = [rState EXCEPT ![r] = COMMIT_SNAPSHOT]
    /\ UNCHANGED <<walPackFile, walIndex, rAction, rPendingPackFile,  
                   rWalIndex, rRepo, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: CommitSnapshot
    Step 2 of simplified compaction. The WAL index
    file is updated with the written snapshot id and
    the WAL entries the snapshot covers is trimmed from
    index. The updated file is CAS written. On a condition
    fail the snapshot is aborted.
-----------------------------------------------------------*)
CommitSnapshot(r) ==
    /\ rState[r] = COMMIT_SNAPSHOT
    /\ LET snapshotId  == rWalIndex[r].nextPos - 1
           newWalIndex == [rWalIndex[r] EXCEPT !.entries = <<>>,
                                               !.snapshotId = snapshotId,
                                               !.version = @ + 1]
       IN
          IF rWalIndex[r].version = walIndex.version
          THEN InstallNewWalIndex(r, newWalIndex)
          ELSE UNCHANGED <<walIndex, rWalIndex>>
    /\ ResetToReady(r)
    /\ UNCHANGED <<snapshot, walPackFile, rPendingPackFile,  
                   rRepo, gcVars, auxVars>>

(* GC ACTIONS --------------------------------------*)

(* ---------------------------------------------------------
    ACTION: StartGC
    A GC task starts by getting the WAL index and calculating
    the packfiles it will delete.
    NOTE! Packfile deletion is not covered by the Cursor 
    blog post, so in lieu of details, and to avoid inventing
    stuff, we make this work by magic! The GC process 
    magically can tell the difference between packfiles
    that are uploaded but pending commit, and packfiles
    that were compacted and now need to be deleted. OpenData
    Buffer uses ULIDs and a grace period that this design
    could use, or there are other options that would work,
    but I'm not going model them here. Numbered packfiles
    is also another option, but changes the write path
    considerably.
-----------------------------------------------------------*)

DeletablePackFile(id, index) ==
    \* start of magic way of knowing if a packfile is pending commit
    \* by a replica
    /\ ~\E r \in Replicas :
        /\ rPendingPackFile[r] /= NIL
        /\ rPendingPackFile[r].id = id
    \* end
    \* The packfile is not referenced in the WAL index
    /\ ~\E entryId \in DOMAIN index.entries :
        index.entries[entryId] = id

DeletablePackFiles(index) ==
    \E id \in DOMAIN walPackFile : DeletablePackFile(id, index)

StartGC(gc) ==
    /\ gcState[gc] = IDLE
    /\ DeletablePackFiles(walIndex)
    /\ LET deleteSet == {id \in DOMAIN walPackFile : DeletablePackFile(id, walIndex)}
       IN
            /\ gcDeleteSet' = [gcDeleteSet EXCEPT ![gc] = deleteSet]
            /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ UNCHANGED <<storeVars, replicaVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: DeletePackFile
    A GC task deletes a packfile in its delete set. If
    the file already doesn't exist then the file is just
    removed from the delete set.
-----------------------------------------------------------*)

DeletePackFile(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E id \in gcDeleteSet[gc] :
        /\ walPackFile' = [i \in (DOMAIN walPackFile \ {id})
                                |-> walPackFile[i]]
        /\ gcDeleteSet' = [gcDeleteSet EXCEPT ![gc] = @ \ {id}]
        /\ gcState' = [gcState EXCEPT ![gc] = IF Cardinality(gcDeleteSet[gc]) = 1
                                              THEN IDLE ELSE DELETE]
    /\ UNCHANGED <<walIndex, snapshot, replicaVars, auxVars>> 
            

\***********************************************************************
\* TYPE correctness
\***********************************************************************

PendingPackFileType == [id: IDs, data: Values]
RepoType == Seq(Values)

ValidIndex(index) ==
\*    [entries: [SUBSET WritablePositions -> IDs], <-- not valid in TLA+  
\*     nextPos: Nat,
\*     snapshotId: Nat, <-- acts as the compaction frontier 
\*     version: Nat]
    IF index = NIL
    THEN TRUE
    ELSE /\ \A i \in DOMAIN index.entries :
             /\ i \in Nat
             /\ index.entries[i] \in IDs
         /\ index.nextPos \in Nat
         /\ index.snapshotId \in Nat
         /\ index.version \in Nat

TypeOK ==
    /\ \A id \in DOMAIN walPackFile :
        /\ id \in IDs
        /\ walPackFile[id] \in Values
    /\ ValidIndex(walIndex)
    /\ \A id \in DOMAIN snapshot :
        /\ id \in Nat
        /\ snapshot[id] \in RepoType
    /\ rAction \in [Replicas -> {IDLE, READY, WRITE, READ, REPLICATE}]
    /\ rState \in [Replicas -> {IDLE, READY, GET_WAL_INDEX, APPEND_WAL_INDEX, REFETCH,
                                COMMIT_SNAPSHOT, REPLAY_WAL_INDEX, SERVE_READ, 
                                NOT_FOUND, ILLEGAL_STATE}]
    /\ rPendingPackFile \in [Replicas -> PendingPackFileType \union {NIL}]
    /\ \A r \in Replicas : ValidIndex(rWalIndex[r])
    /\ rRepo \in [Replicas -> RepoType]
    /\ gcState \in [GarbageCollectors -> {IDLE, DELETE}]
    /\ gcDeleteSet \in [GarbageCollectors -> SUBSET IDs]
    /\ auxUsedIds \in SUBSET IDs
    /\ auxUsedValues \in SUBSET Values
    /\ \A pos \in WritablePositions :
        \A repo \in auxReadRepos[pos] : repo \in RepoType
    /\ auxWrittenValues \in Seq(Values)

\***********************************************************************
\* INVARIANTS
\***********************************************************************

\* INV: ValidReplicas
\* No replicas enter an invalid state.
ValidReplicas ==
    \A r \in Replicas :
        /\ rState[r] /= ILLEGAL_STATE
        /\ rState[r] = READY => rAction[r] = READY

(* INV: ReadReposPrefixOfRecordedWriteHistory
   Every completed read (git fetch) returns exactly the prefix of
   successfully committed writes identified by the WAL position
   captured for that read. 
*)
ReadReposPrefixOfRecordedWriteHistory ==
    \A pos \in DOMAIN auxReadRepos :
        \A repo \in auxReadRepos[pos] :
            \* The captured index cannot refer beyond committed history.
            /\ pos <= Len(auxWrittenValues)
            \* The replica replayed every write visible in the captured index.
            /\ Len(repo) = pos
            \* The replayed values preserve the committed order and contents.
            /\ \A i \in DOMAIN repo :
                repo[i] = auxWrittenValues[i]

(* INV: WalIndexRepresentsCommittedRepo
   Central WAL safety property: a replica can reconstruct the complete
   committed repo from the snapshot and packfiles named by the current index.
*)
WalIndexRepresentsCommittedRepo ==
    LET snapshotId == walIndex.snapshotId
        hist       == auxWrittenValues
    IN
        \* The index covers exactly the committed history.
        /\ walIndex.nextPos = Len(hist) + 1
        /\ snapshotId <= Len(hist)
        \* The current snapshot is exactly the committed prefix through
        \* the compaction frontier.
        /\ IF snapshotId = 0
           THEN TRUE
           ELSE /\ snapshotId \in DOMAIN snapshot
                /\ Len(snapshot[snapshotId]) = snapshotId
                /\ \A pos \in 1..snapshotId :
                    snapshot[snapshotId][pos] = hist[pos]
        \* Every value after the snapshot remains available via the index.
        /\ \A pos \in (snapshotId + 1)..Len(hist) :
            /\ pos \in DOMAIN walIndex.entries
            /\ walIndex.entries[pos] \in DOMAIN walPackFile
            /\ walPackFile[walIndex.entries[pos]] = hist[pos]

\***********************************************************************
\* LIVENESS
\***********************************************************************

AllValuesWritten ==
    <>[](\A v \in Values :
            \E pos \in DOMAIN auxWrittenValues :
                auxWrittenValues[pos] = v)

ReplicaReachesReadyState ==
    \A r \in Replicas :
        rState[r] /= READY ~> rState[r] = READY 

\***********************************************************************
\* INIT, NEXT and SPEC
\***********************************************************************

Init ==
    /\ walPackFile = <<>>
    /\ walIndex = [entries    |-> <<>>, 
                   nextPos    |-> 1,
                   snapshotId |-> 0, \* compaction frontier
                   version    |-> 0] \* CAS condition
    /\ snapshot = <<>>
    /\ rAction = [r \in Replicas |-> IDLE]
    /\ rState = [r \in Replicas |-> IDLE]
    /\ rPendingPackFile = [r \in Replicas |-> NIL]
    /\ rWalIndex = [r \in Replicas |-> NIL]
    /\ rRepo = [r \in Replicas |-> <<>>]
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ auxUsedIds = {}
    /\ auxUsedValues = {}
    /\ auxReadRepos = [pos \in WritablePositions \union {0} |-> {}]
    /\ auxWrittenValues = <<>>
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ gcDeleteSet = [gc \in GarbageCollectors |-> {}]

Next ==
    \* Replicas
    \/ \E r \in Replicas :
        \/ StartReplica(r)
        \/ ValidateNotFound(r)
        \/ ReplayWalIndex(r)
        \* writes ---------------------
        \/ \E v \in Values : WritePackFile(r, v)              
        \/ GetWalIndex(r)
        \/ AppendToWalIndex(r)
        \* reads ----------------------
        \/ StartRead(r)
        \/ ServeRead(r)
        \* replication ----------------
        \/ StartReplicate(r)
        \* snapshots ------------------
        \/ WriteSnapshot(r)
        \/ CommitSnapshot(r)
    \* GC
    \/ \E gc \in GarbageCollectors :
        \/ StartGC(gc)
        \/ DeletePackFile(gc)

Fairness ==
    \* All actions have fairness except for actions that kick
    \* off snapshots, replication, reads and GC. WritePackFile
    \* is strongly fair as reads, replication and reads 
    \* temporarily disable it
    /\ \A r \in Replicas :
        /\ WF_vars(StartReplica(r))
        /\ WF_vars(ReplayWalIndex(r))
        /\ WF_vars(ValidateNotFound(r))
        /\ \A v \in Values : SF_vars(WritePackFile(r, v))
        /\ WF_vars(GetWalIndex(r))
        /\ WF_vars(AppendToWalIndex(r))
        /\ WF_vars(ServeRead(r))
        /\ WF_vars(CommitSnapshot(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
