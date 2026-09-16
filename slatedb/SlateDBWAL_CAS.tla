----------------------------- MODULE SlateDBWAL_CAS -------------------------

(*
    This is a variant of the SlateDB WAL protocol that uses a single
    manifest with CAS writes (instead of numbered manifests).
    The single manifest's replayAfterWalId determines the GC boundary
    for WAL files.
*)

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,           \* The set of writer processes
          GarbageCollectors, \* The set of garbage collector processes
          Values             \* The set of values to append

\* writer states
CONSTANTS IDLE, FIND_NEXT_WAL_ID, CLAIM_EPOCH, WRITE_FENCE,
          VALIDATE_BEFORE_RETRY, VALIDATE_FENCE, 
          VALIDATE_BEFORE_NOT_FOUND,
          LOAD_SNAPSHOT, REPLAY_WAL, READY, 
          COMMIT_SNAPSHOT, FENCED, NOT_FOUND

\* GC states (GC also uses IDLE)
CONSTANTS FIND_LAST_WAL_ID, DELETE

\* WAL record types
CONSTANTS DATA, FENCE

CONSTANTS NIL, ILLEGAL_STATE

VARIABLES manifest,         \* Manifest file (on S3)
          wal,              \* Id -> WAL file (on S3)
          snapshot,         \* Id -> Snapshot file (on S3) (snapshots of machine data, see spec comments)
          wState,           \* Writer -> state
          wEpoch,           \* Writer -> writer epoch
          wManifest,        \* Writer -> local copy of a manifest
          wNextWalId,       \* Writer -> the next WAL Id to write to
          wMachineData,     \* Writer -> State-machine data (a sequence of Values)
          wReplayId,        \* Writer -> Current position in WAL replay
          gcState,          \* GC -> state
          gcLastWalId,      \* GC -> the last detected WAL Id
          gcManifest        \* GC -> local copy of a manifest

VARIABLES auxUsedValues,    
          auxWrittenEntries \* Successful write history         

storeVars == <<manifest, wal, snapshot>>
writerVars == <<wState, wEpoch, wManifest, wNextWalId, 
                wMachineData, wReplayId>>
gcVars == <<gcState, gcLastWalId, gcManifest>>
auxVars == <<auxUsedValues, auxWrittenEntries>>
vars == <<storeVars, writerVars, gcVars, auxVars>>

Symmetry ==
      Permutations(Writers)
          \union Permutations(GarbageCollectors)
          \union Permutations(Values)

\* ****************************************************
\* HELPERS
\* ****************************************************

LastWalId == IF DOMAIN wal = {} THEN 0 ELSE Max(DOMAIN wal)
ReadWalEntry(id) == IF id \in DOMAIN wal THEN wal[id] ELSE NIL
ReadSnapshot(id) == IF id \in DOMAIN snapshot THEN snapshot[id] ELSE NIL

\* ******************************************************************
\* ACTIONS
\* ******************************************************************

\* Writer actions ------------------------------------------------------

(* ---------------------------------------------------------
    ACTION: StartWriter

    Initialization step 1. 
    An idle writer starts by loading the manifest.
-----------------------------------------------------------*)

StartWriter(w) ==
    /\ wState[w] = IDLE
    /\ wManifest' = [wManifest EXCEPT ![w] = manifest]
    /\ wState' = [wState EXCEPT ![w] = FIND_NEXT_WAL_ID]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId, 
                   wMachineData, wNextWalId, wReplayId>>

(* ---------------------------------------------------------
    ACTION: FindNextWalId

    Initialization step 2. 
    The writer discovers the last object id in the WAL in
    order to know which id to write its fencing object to.
    It transitions to CLAIM_EPOCH.
-----------------------------------------------------------*)

FindNextWalId(w) ==
    /\ wState[w] = FIND_NEXT_WAL_ID
    /\ wState' = [wState EXCEPT ![w] = CLAIM_EPOCH]
    /\ wNextWalId' = [wNextWalId EXCEPT ![w] = LastWalId + 1]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, 
                   wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: ClaimEpoch

    Initialization step 3.
    The writer attempts a CAS write of the manifest based on
    the manifest version (that it previously read in step 1). 
    If the condition fails, the writer transitions back to IDLE
    where it can try to initialize again. If it succeeds
    in writing the new manifest it transitions to WRITE_FENCE
-----------------------------------------------------------*)

ClaimEpoch(w) ==
    /\ wState[w] = CLAIM_EPOCH
    /\ LET newManifest == [wManifest[w] EXCEPT !.writerEpoch = @ + 1,
                                               !.version = @ + 1]
       IN \/ /\ wManifest[w].version /= manifest.version 
             /\ wState' = [wState EXCEPT ![w] = IDLE]
             /\ UNCHANGED <<manifest, wManifest, wEpoch>>
          \/ /\ wManifest[w].version = manifest.version
             /\ manifest' = newManifest
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wEpoch' = [wEpoch EXCEPT ![w] = newManifest.writerEpoch]
             /\ wState' = [wState EXCEPT ![w] = WRITE_FENCE]
    /\ UNCHANGED <<gcVars, auxVars, wal, snapshot, wNextWalId,  
                   wMachineData, wNextWalId, wReplayId>>

(* ---------------------------------------------------------
    ACTION: WriteFenceWalEntry

    Initialization step 4.
    The writer attempts to write a FENCE object to the next
    WAL id (that it discovered earlier), using put-if-absent.
    If an object already exists it means either:
        1) The writer has been fenced by another writer (and
           the writer should stop)
        2) A stale writer has written another DATA object
           to the WAL (and the writer should try the FENCE
           writer again at the next address).
    To find out whether this is case 1 or 2, the writer 
    transitions to VALIDATE_BEFORE_RETRY.

    If the fence write succeeded, then the writer must next
    validate the fence write (as it's possible the writer
    is stale and its write succeeded because GC deleted the 
    original DATA object that occupied that address).
-----------------------------------------------------------*)

WriteFenceWalEntry(w) ==
    /\ wState[w] = WRITE_FENCE
    /\ \/ /\ wNextWalId[w] \in DOMAIN wal
          /\ wState' = [wState EXCEPT ![w] = VALIDATE_BEFORE_RETRY]
          /\ UNCHANGED <<wal, auxWrittenEntries>>
       \/ /\ wNextWalId[w] \notin DOMAIN wal
          /\ LET entry == [kind  |-> FENCE]
             IN
                /\ wal' = wal @@ (wNextWalId[w] :> entry)
                /\ wState' = [wState EXCEPT ![w] = VALIDATE_FENCE]
    /\ UNCHANGED <<gcVars, auxVars, manifest, snapshot, wEpoch, 
                   wManifest, wNextWalId, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: ValidateEpochBeforeWalFenceRetry

    The writer refreshes its manifest. If the manifest
    is still valid, then the writer did not get fenced
    and it bumps its next WAL Id and transitions to 
    WRITE_FENCE.
    If the manifest is invalid, the writer transitions 
    to FENCED where it remains. This spec does not
    restart fenced writers to avoid cycles which make
    liveness hard to check.
-----------------------------------------------------------*)

ValidateEpochBeforeWalFenceRetry(w) ==
    /\ wState[w] = VALIDATE_BEFORE_RETRY
    /\ LET refreshedM == manifest IN
        \/ /\ wEpoch[w] < refreshedM.writerEpoch
           /\ wState' = [wState EXCEPT ![w] = FENCED]
           /\ UNCHANGED <<wManifest, wNextWalId>>
        \/ /\ wEpoch[w] > refreshedM.writerEpoch
           /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
           /\ UNCHANGED <<wManifest, wNextWalId>>
        \/ /\ wEpoch[w] = refreshedM.writerEpoch
           /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
           /\ wState' = [wState EXCEPT ![w] = WRITE_FENCE]
           /\ wManifest' = [wManifest EXCEPT ![w] = refreshedM]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: ValidateFence

    Initialization step 5.
    The writer refreshes its manifest and checks:
    1) If the id of the fence record it wrote is < the latest 
    replayAfterWalId. If so, then that successful write was
    actually an invalid write and the writer must stop.
    2) If the writer epoch is still valid. Technically not
    required as if another writer had fenced this one, any subsequent
    write to the WAL would fail due to a fenced record occupying
    the next Id this writer would write to.
    
    If both checks succeed, the writer transitions to
    LOAD_SNAPSHOT, which is the first step in rebuilding
    the state machine data.
-----------------------------------------------------------*)

ValidateFence(w) ==
    /\ wState[w] = VALIDATE_FENCE
    /\ LET refreshedM == manifest IN
        \/ /\ \/ wEpoch[w] /= refreshedM.writerEpoch
              \/ wNextWalId[w] < refreshedM.replayAfterWalId
           /\ wState' = [wState EXCEPT ![w] = FENCED]
           /\ UNCHANGED <<wManifest, wNextWalId, wReplayId>>
        \/ /\ wEpoch[w] = refreshedM.writerEpoch
           /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
           /\ wReplayId' = [wReplayId EXCEPT ![w] = wManifest[w].replayAfterWalId]
           /\ wState' = [wState EXCEPT ![w] = LOAD_SNAPSHOT]
           /\ wManifest' = [wManifest EXCEPT ![w] = refreshedM]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wMachineData>>

(* ---------------------------------------------------------
    ACTION: LoadSnapshot

    Initialization step 6.
    The writer loads the snapshot file whose Id is the
    replayAfterWalId-1 (as the replayAfterWalId is advanced
    based on flushing snapshots).
    If the snapshot object doesn't exist, then the writer
    supposes the snapshot must have been GCed and so the
    writer must be stale, so it transitions to FENCED.
    Again, not strictly part of SlateDB WAL protocol,
    just a minor tweak.
-----------------------------------------------------------*)

LoadSnapshot(w) ==
    /\ wState[w] = LOAD_SNAPSHOT
    /\ LET snapshotId == wManifest[w].replayAfterWalId - 1
           readSnapshot == IF snapshotId = 0
                           THEN <<>> 
                           ELSE ReadSnapshot(snapshotId)
       IN
          \/ /\ readSnapshot = NIL
             /\ wState' = [wState EXCEPT ![w] = FENCED]
             /\ UNCHANGED <<wMachineData, wReplayId>>
          \/ /\ readSnapshot /= NIL
             /\ wMachineData' = [wMachineData EXCEPT ![w] = readSnapshot]
             /\ wReplayId' = [wReplayId EXCEPT ![w] = wManifest[w].replayAfterWalId]
             /\ wState' = [wState EXCEPT ![w] = REPLAY_WAL]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, wNextWalId>>

(* ---------------------------------------------------------
    ACTION: ReplayWAL

    Initialization step 7 (last initialization step).
    The writer replays the WAL entries in the range of
    [replayAfterWalId -> written fenced object id].
    This spec maintains a cursor position wReplayId
    which was set to replayAfterWalId in the previous step.
    Each DATA object read is applied to the machine data.
    This action advances the cursor and repeats until
    tyhe range has been read.

    Once the writer has replayed this fixed range, it
    transitions to READY, where it can accept writes.

    In the case that the object at the cursor does not 
    exist, the writer transitions to VALIDATE_BEFORE_NOT_FOUND.
    It needs to detect whether it is stale or whether 
    the object erroneously does not exist (should never happen).
-----------------------------------------------------------*)

ReplayWAL(w) ==
    /\ wState[w] = REPLAY_WAL
    /\ LET id   == wReplayId[w]
           read == ReadWalEntry(id)
       IN    
          CASE id = wNextWalId[w] ->
                    /\ wState' = [wState EXCEPT ![w] = READY]
                    /\ wReplayId' = [wReplayId EXCEPT ![w] = 0]
                    /\ UNCHANGED <<wMachineData>>
            [] read = NIL ->
                    /\ wState' = [wState EXCEPT ![w] = VALIDATE_BEFORE_NOT_FOUND]
                    /\ UNCHANGED <<wReplayId, wMachineData>>
            [] read.kind = DATA ->
                    /\ wMachineData' = [wMachineData EXCEPT ![w] = Append(@, read.value)]
                    /\ wReplayId' = [wReplayId EXCEPT ![w] = @ + 1]
                    /\ UNCHANGED <<wState>>
            [] read.kind = FENCE ->
                    /\ wReplayId' = [wReplayId EXCEPT ![w] = @ + 1]
                    /\ UNCHANGED <<wState, wMachineData>>
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId, wManifest>>

(* ---------------------------------------------------------
    ACTION: ValidateBeforeNotFound

    The writer was unable to read a WAL object. It refreshes
    its manifest. If the manifest is invalid, it means
    the writer was fenced and it transitions to FENCED.
    If the manifest is valid, then something very bad has
    happened! NOT_FOUND should never happen.
-----------------------------------------------------------*)

ValidateBeforeNotFound(w) ==
    /\ wState[w] = VALIDATE_BEFORE_NOT_FOUND
    /\ LET refreshedM == manifest IN
        \/ /\ wEpoch[w] < refreshedM.writerEpoch
           /\ wState' = [wState EXCEPT ![w] = FENCED]
        \/ /\ wEpoch[w] > refreshedM.writerEpoch
           /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
        \/ /\ wEpoch[w] = refreshedM.writerEpoch
           /\ wState' = [wState EXCEPT ![w] = NOT_FOUND]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, 
                   wNextWalId, wReplayId, wMachineData>>

(* ---------------------------------------------------------
    ACTION: AppendEntryToWAL

    Steady-state.
    The writer attempts to write a DATA object to the
    next address in the WAL, using put-if-absent.
    If an object already exists, it means the writer has
    been fenced (the object in question will be a FENCE
    object which is not garbage collected).
    If the write is successful, the writer applies the
    value to its machine data. The spec also records
    the write in the write history for invariant checking.
-----------------------------------------------------------*)

AppendEntryToWAL(w, v) ==
    /\ wState[w] = READY
    /\ v \notin auxUsedValues
    /\ \/ /\ wNextWalId[w] \in DOMAIN wal
          /\ wState' = [wState EXCEPT ![w] = FENCED]
          /\ UNCHANGED <<wal, wNextWalId, wMachineData, auxUsedValues,
                         auxWrittenEntries>>
       \/ LET entry == [kind  |-> DATA, value |-> v]
          IN
            /\ wNextWalId[w] \notin DOMAIN wal
            /\ wal' = wal @@ (wNextWalId[w] :> entry)
            /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
            /\ wMachineData' = [wMachineData EXCEPT ![w] = Append(@, v)]
            /\ auxUsedValues' = auxUsedValues \union {v}
            /\ auxWrittenEntries' = Append(auxWrittenEntries, [walId |-> wNextWalId[w],
                                                               value |-> v])
            /\ UNCHANGED wState
    /\ UNCHANGED <<gcVars, manifest, snapshot, wEpoch, wManifest, wReplayId>>

(* ---------------------------------------------------------
    ACTION: WriteSnapshot

    Steady-state.
    WriteSnapshot + CommitSnapshot are equivalent of Flush
    in the original spec.

    The writer writes its machine data as a snapshot file
    using the Id of the last written WAL entry, using
    put-if-absent.
-----------------------------------------------------------*)

WriteSnapshot(w) ==
    /\ wState[w] = READY
    /\ wMachineData[w] /= <<>>
    /\ LET lastSnapshotId == wManifest[w].replayAfterWalId - 1
           nextSnapshotId == wNextWalId[w] - 1
       IN
          /\ nextSnapshotId >= lastSnapshotId 
          /\ nextSnapshotId \notin DOMAIN snapshot
          /\ snapshot' = snapshot @@ (nextSnapshotId :> wMachineData[w])
          /\ wState' = [wState EXCEPT ![w] = COMMIT_SNAPSHOT]
    /\ UNCHANGED <<gcVars, auxVars, wal, manifest,  
                   wEpoch, wManifest, wNextWalId, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: CommitSnapshot

    Steady-state.
    The writer attempts a CAS write (based on version) of 
    the manifest to update replayAfterWalId. 
    Because the WAL has been flushed (in this case as a 
    machine data snapshot), the replayAfterWalId can be 
    advanced to the next Id after this snapshot. 
    
    If the CAS condition fails, the writer knows it has
    been fenced (only another writer claiming a higher epoch
    could have bumped the manifest version).
-----------------------------------------------------------*)

CommitSnapshot(w) ==
    /\ wState[w] = COMMIT_SNAPSHOT
    /\ LET snapshotId    == wNextWalId[w] - 1
           newManifest == [wManifest[w] EXCEPT !.replayAfterWalId = snapshotId + 1,
                                               !.version = @ + 1]
       IN
          \/ /\ wManifest[w].version /= manifest.version
             /\ wState' = [wState EXCEPT ![w] = FENCED]
             /\ UNCHANGED <<manifest, wManifest>>
          \/ /\ wManifest[w].version = manifest.version
             /\ manifest' = newManifest
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = READY]
    /\ UNCHANGED <<gcVars, auxVars, wal, snapshot, 
                   wEpoch, wNextWalId, wMachineData, wReplayId>>

\* WAL GC ---------------------------------------------------------

(* ---------------------------------------------------------
    ACTION: StartGC

    GC initialization step 1.
    A new WAL GC process starts by reading the manifest.
-----------------------------------------------------------*)

StartGC(gc) ==
    /\ gcState[gc] = IDLE
    /\ gcManifest' = [gcManifest EXCEPT ![gc] = manifest]
    /\ gcState' = [gcState EXCEPT ![gc] = FIND_LAST_WAL_ID]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, gcLastWalId>>

(* ---------------------------------------------------------
    ACTION: FindLastWalId

    GC initialization step 2.
    A GC task discovers the last WAL Id (that it later 
    guarantees not to delete as the WAL must contain at
    least one object).
-----------------------------------------------------------*)

FindLastWalId(gc) ==
    /\ gcState[gc] = FIND_LAST_WAL_ID
    /\ gcLastWalId' = [gcLastWalId EXCEPT ![gc] = LastWalId]
    /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, gcManifest>> 

(* ---------------------------------------------------------
    ACTION: DeleteWalEntry

    A GC task deletes a DATA object in the WAL whose
    Id is below the replayAfterWalId of the latest
    manifest (loaded previously) and not the last object
    in the WAL.
-----------------------------------------------------------*)

DeletableWalEntry(gc, id) ==
    /\ id < gcManifest[gc].replayAfterWalId
    /\ id < gcLastWalId[gc]
    /\ wal[id].kind = DATA
    
DeleteWalEntry(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN wal :
        /\ DeletableWalEntry(gc, id)
        /\ wal' = [i \in (DOMAIN wal \ {id}) |-> wal[i]]
    /\ UNCHANGED <<manifest, snapshot, writerVars, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: DeleteSnapshot

    A GC task deletes a snapshot file below the 
    last written snapshot. Not strictly part of SlateDB,
    but included to harmonize with other specs.
-----------------------------------------------------------*)

DeletableSnapshot(gc, id) ==
    id < gcManifest[gc].replayAfterWalId - 1

DeleteSnapshot(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN snapshot :
        /\ DeletableSnapshot(gc, id)
        /\ snapshot' = [i \in (DOMAIN snapshot \ {id}) |-> snapshot[i]]
    /\ UNCHANGED <<wal, manifest, writerVars, gcVars, auxVars>>

\* ****************************************************
\* TYPE correctness
\* ****************************************************

DataObjectType == [kind: {DATA}, value: Values]
FenceObjectType == [kind: {FENCE}]
WALObjectType == DataObjectType \union FenceObjectType

ManifestType ==
    [writerEpoch: Nat, 
     replayAfterWalId: Nat,
     version: Nat]

MachineDataType == Seq(Values)
HistoryEntryType == [walId: Nat, value: Values]

TypeOK ==
    /\ manifest \in ManifestType
    /\ \A id \in DOMAIN wal : 
        id \in Nat /\ wal[id] \in WALObjectType
    /\ \A id \in DOMAIN snapshot : 
        id \in Nat /\ snapshot[id] \in Seq(Values)
    /\ wState \in [Writers -> {IDLE, FIND_NEXT_WAL_ID, CLAIM_EPOCH, WRITE_FENCE,
                               VALIDATE_BEFORE_RETRY, VALIDATE_FENCE, VALIDATE_BEFORE_NOT_FOUND,
                               LOAD_SNAPSHOT, REPLAY_WAL, READY, COMMIT_SNAPSHOT, FENCED, NOT_FOUND}]
    /\ wEpoch \in [Writers -> Nat]
    /\ wManifest \in [Writers -> ManifestType \union {NIL}]
    /\ wNextWalId \in [Writers -> Nat]
    /\ wMachineData \in [Writers -> MachineDataType]
    /\ wReplayId \in [Writers -> Nat]
    /\ gcState \in [GarbageCollectors -> {IDLE, FIND_LAST_WAL_ID, DELETE}]
    /\ gcLastWalId \in [GarbageCollectors -> Nat]
    /\ gcManifest \in [GarbageCollectors -> ManifestType \union {NIL}]
    /\ auxUsedValues \in SUBSET Values
    /\ auxWrittenEntries \in Seq(HistoryEntryType)

\* ****************************************************
\* INVARIANTS
\* ****************************************************

\* INV: UniqueEpochs
\* Two writers cannot have the same writer epoch
\* (idle writers epoch is 0)
UniqueEpochs ==
    ~\E w1, w2 \in Writers :
        /\ w1 /= w2
        /\ wEpoch[w1] > 0
        /\ wEpoch[w1] = wEpoch[w2]

\* INV: ValidWriters
ValidWriters ==
    \* No writer can hit a NOT_FOUND or ILLEGAL_STATE error
    /\ \A w \in Writers : wState[w] \notin { NOT_FOUND, ILLEGAL_STATE }
    \* There must be at least one functional writer
    /\ \E w \in Writers : wState[w] /= FENCED

\* INV: ConsistentMachineData
\* The state machine data of each READY writer matches the
\* history of successful writes.
\* If the writer is stale, it matches a prefix of write history.
\* If the writer is current, it perfectly matches the write history.
PrefixOf(machineData, hist) ==
    /\ Len(machineData) <= Len(hist)
    /\ \A pos \in DOMAIN machineData :
            machineData[pos] = hist[pos].value

ConsistentMachineData ==
    \A w \in Writers :
        wState[w] \in {READY, COMMIT_SNAPSHOT} =>
            /\ PrefixOf(wMachineData[w], auxWrittenEntries)
            /\ IF wManifest[w].version = manifest.version
               THEN Len(wMachineData[w]) = Len(auxWrittenEntries)
               ELSE TRUE

\* INV: ManifestRepresentsCommittedLog
\* Central WAL safety property: every committed value remains
\* reconstructible from the current manifest.
ManifestRepresentsCommittedLog ==
    LET snapshotId == manifest.replayAfterWalId - 1
        snap       == IF snapshotId = 0 THEN <<>>
                      ELSE snapshot[snapshotId]
        hist       == auxWrittenEntries
    IN
        \* The current snapshot is a prefix of the recorded write history
        /\ PrefixOf(snap, hist)
        \* For every successful write in recorded history ...
        /\ \A i \in 1..Len(hist) :
            LET histEntry == hist[i]
                snapEntry == snap[i]
                walEntry  == wal[histEntry.walId] 
            IN
                \* either the id < replayAfterWalId and thus exists
                \* in the snapshot
                \/ /\ histEntry.walId < manifest.replayAfterWalId
                   /\ snapEntry = histEntry.value
                \* or the id is >= replayAfterWalId and thus exists
                \* in the WAL
                \/ /\ histEntry.walId >= manifest.replayAfterWalId
                   /\ walEntry.kind = DATA
                   /\ walEntry.value = histEntry.value

\* ****************************************************
\* Liveness
\* ****************************************************

AllValuesAttempted ==
    <>[](auxUsedValues = Values)

\* There are only two terminal states:
\* - READY: writable state (ends when there are no more values to append)
\* - FENCED: when another writer claims a higher epoch
\* Writers keep restarting (reverting to IDLE) when encountering
\* conflicts during epoch claim stage, but go to FENCED if conflicts occur
\* after that (from WRITE_FENCE and later).
WritersReachReadyOrFenced ==
    \A w \in Writers :
        <>[](wState[w] \in {READY, FENCED})
        
GcCompletes ==
    \A gc \in GarbageCollectors :
        <>[](gcState[gc] = DELETE)        

\* ****************************************************
\* INIT, NEXT and Spec
\* ****************************************************

Init ==
    /\ manifest = [writerEpoch      |-> 0, 
                   replayAfterWalId |-> 1,
                   version          |-> 1]
    /\ wal = <<>>
    /\ snapshot = <<>>
    /\ wState = [w \in Writers |-> IDLE]
    /\ wEpoch = [w \in Writers |-> 0]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ wNextWalId = [w \in Writers |-> 1]
    /\ wMachineData = [w \in Writers |-> <<>>]
    /\ wReplayId = [w \in Writers |-> 0]
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ gcLastWalId = [gc \in GarbageCollectors |-> 0]
    /\ gcManifest = [gc \in GarbageCollectors |-> NIL]
    /\ auxUsedValues = {}
    /\ auxWrittenEntries = <<>>

Next ==
    \/ \E w \in Writers :
        \* Writer initialization
        \/ StartWriter(w)
        \/ FindNextWalId(w)
        \/ ClaimEpoch(w)
        \/ WriteFenceWalEntry(w)
        \/ ValidateEpochBeforeWalFenceRetry(w)
        \/ ValidateFence(w)
        \/ LoadSnapshot(w)
        \/ ReplayWAL(w)
        \/ ValidateBeforeNotFound(w)
        \* Established writer steady state
        \/ \E v \in Values : AppendEntryToWAL(w, v)
        \/ WriteSnapshot(w)
        \/ CommitSnapshot(w)
    \/ \E gc \in GarbageCollectors :
        \/ StartGC(gc)
        \/ FindLastWalId(gc)
        \/ DeleteWalEntry(gc)
        \/ DeleteSnapshot(gc)
        
Fairness ==
    \A w \in Writers :
        \* Writer initialization
        /\ WF_vars(StartWriter(w))
        /\ WF_vars(FindNextWalId(w))
        /\ WF_vars(ClaimEpoch(w))
        /\ WF_vars(WriteFenceWalEntry(w))
        /\ WF_vars(ValidateEpochBeforeWalFenceRetry(w))
        /\ WF_vars(ValidateFence(w))
        /\ WF_vars(LoadSnapshot(w))
        /\ WF_vars(ReplayWAL(w))
        /\ WF_vars(ValidateBeforeNotFound(w))
        \* Established writer steady state
        /\ \A v \in Values : WF_vars(AppendEntryToWAL(w, v))
        /\ WF_vars(WriteSnapshot(w))
        /\ WF_vars(CommitSnapshot(w))
    /\ \A gc \in GarbageCollectors :
        /\ WF_vars(StartGC(gc))
        /\ WF_vars(FindLastWalId(gc))
        /\ WF_vars(DeleteWalEntry(gc))
        /\ WF_vars(DeleteSnapshot(gc))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
