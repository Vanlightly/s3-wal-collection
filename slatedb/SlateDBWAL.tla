----------------------------- MODULE SlateDBWAL -------------------------

(*
    This spec models SlateDB's WAL protocol. To keep the spec inline 
    with the other specs in this repo, it adds SMR to the protocol
    and verifies that the machine state is consistent with the WAL.
    It models:
    * a set of writers who maintain a state machine whose state
      is simply the sequence of successfully written values. 'Flush'
      is replaced by writing the machine state as a snapshot (whose
      address is the highest written WAL id) and committing the 
      snapshot by writing a new manifest with the corresponding 
      replayAfterWalId (which is the snapshot id + 1).
    * a set of garbage collector processes that can execute either
      mainfest GC or WAL GC.  1

    
*)

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,           \* The set of writer processes
          GarbageCollectors, \* The set of garbage collector processes
          Values             \* The set of values to append

\* writer states
CONSTANTS IDLE, FIND_NEXT_WAL_ID, CLAIM_EPOCH, CHECK_BOUNDARY, WRITE_FENCE,
          VALIDATE_BEFORE_RETRY, VALIDATE_BEFORE_REPLAY, VALIDATE_BEFORE_NOT_FOUND,
          LOAD_SNAPSHOT, REPLAY_WAL, READY, COMMIT_SNAPSHOT, 
          FENCED, NOT_FOUND

\* GC tasks
CONSTANTS MANIFEST_GC, WAL_GC

\* GC states (GC also uses IDLE)
CONSTANTS LOAD_BOUNDARY, COMPUTE_BOUNDARY, 
          ADVANCE_BOUNDARY, FIND_LAST_WAL_ID, DELETE, DONE

\* WAL record types
CONSTANTS DATA, FENCE

CONSTANTS NIL, ILLEGAL_STATE

VARIABLES manifest,         \* Id -> Manifest file (on S3)
          boundary,         \* GC Boundary file  (on S3)
          wal,              \* Id -> WAL file (on S3)
          snapshot,         \* Id -> Snapshot file (on S3) (snapshots of machine data, see spec comments)
          wState,           \* Writer -> state
          wEpoch,           \* Writer -> writer epoch
          wManifest,        \* Writer -> local copy of a manifest
          wManifestLoad,    \* Writer -> manifest refresh state
          wNextWalId,       \* Writer -> the next WAL Id to write to
          wMachineData,     \* Writer -> State-machine data (a sequence of Values)
          wReplayId,        \* Writer -> Current position in WAL replay
          gcType,           \* GC -> type of GC task
          gcState,          \* GC -> state
          gcLastWalId,      \* GC -> the last detected WAL Id
          gcBoundary,       \* GC -> local copy of the boundary file
          gcManifest        \* GC -> local copy of a manifest

VARIABLES auxUsedValues,    
          auxWrittenEntries \* Successful write history         

storeVars == <<manifest, boundary, wal, snapshot>>
writerVars == <<wState, wEpoch, wManifest, wManifestLoad, wNextWalId, 
                wMachineData, wReplayId>>
gcVars == <<gcType, gcState, gcLastWalId, gcBoundary, gcManifest>>
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
LastManifestId == Max(DOMAIN manifest)
ReadLastManifest == manifest[LastManifestId]
ReadSnapshot(id) == IF id \in DOMAIN snapshot THEN snapshot[id] ELSE NIL

\* ******************************************************************
\* ACTIONS
\* ******************************************************************

(* ---------------------------------------------------------
    RefreshManifest (sub-action)

    When a manifest refresh is required, it goes through a three step
    process:
    1. Load the latest manifest
    2. Read the boundary file and check if the loaded manifest id 
       is valid (above the boundary). If the manifest id <=
       the GC boundary it means that this address may have had
       a different manifest but was deleted by GC.
    3. React to the valid/invalid result.
    
    RefreshManifest sub-action does steps 1 and 2, the actions that 
    invoke it do step 3.
-----------------------------------------------------------*)

DoRefresh(w) ==
    \/ /\ wManifestLoad[w].loaded = FALSE
       /\ wManifest[w] /= ReadLastManifest
    \/ wManifestLoad[w].checked = FALSE

RefreshManifest(w) ==
    CASE /\ wManifestLoad[w].loaded = FALSE
         /\ wManifest[w] /= ReadLastManifest ->
            /\ wManifest' = [wManifest EXCEPT ![w] = ReadLastManifest]
            /\ wManifestLoad' = [wManifestLoad EXCEPT ![w] = 
                                            [loaded   |-> TRUE,
                                             checked  |-> FALSE,
                                             valid    |-> FALSE]]
      [] wManifestLoad[w].checked = FALSE -> 
            /\ wManifestLoad' = [wManifestLoad EXCEPT ![w] = 
                                    [loaded  |-> TRUE,
                                     checked |-> TRUE,
                                     valid   |-> wManifest[w].id > boundary.manifestId]]
            /\ UNCHANGED wManifest
                                 
ManifestRefreshed(w) ==
    /\ wManifestLoad' = [wManifestLoad EXCEPT ![w]=
                            [checked |-> FALSE,
                             loaded  |-> FALSE,
                             valid   |-> FALSE]]
    /\ UNCHANGED wManifest
          

\* Writer actions ------------------------------------------------------

(* ---------------------------------------------------------
    ACTION: StartWriter

    An idle writer starts by loading the manifest. If the
    manifest is valid, it transitions to FIND_NEXT_WAL_ID.
-----------------------------------------------------------*)

StartWriter(w) ==
    /\ wState[w] = IDLE
    /\ CASE DoRefresh(w) -> 
                /\ RefreshManifest(w)
                /\ UNCHANGED wState
         [] wManifestLoad[w].valid = FALSE ->
                /\ wState' = [wState EXCEPT ![w] = IDLE]
                /\ ManifestRefreshed(w)
         [] OTHER -> 
                /\ wState' = [wState EXCEPT ![w] = FIND_NEXT_WAL_ID]
                /\ ManifestRefreshed(w)
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId, 
                   wMachineData, wNextWalId, wReplayId>>

(* ---------------------------------------------------------
    ACTION: FindNextWalId

    The writer discovers the last object id in the WAL in
    order to know which id to write its fencing object.
    It transitions to CLAIM_EPOCH.
-----------------------------------------------------------*)

FindNextWalId(w) ==
    /\ wState[w] = FIND_NEXT_WAL_ID
    /\ wState' = [wState EXCEPT ![w] = CLAIM_EPOCH]
    /\ wNextWalId' = [wNextWalId EXCEPT ![w] = LastWalId + 1]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, 
                   wManifestLoad, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: ClaimEpoch

    The writer attempts to write a new manifest to the
    next manifest Id using put-if-absent. If an object
    already exists, the writer transitions back to IDLE
    where it can try to initialize again. If it succeeds
    in writing the new manifest it transitions to
    CHECK_BOUNDARY.
-----------------------------------------------------------*)

ClaimEpoch(w) ==
    /\ wState[w] = CLAIM_EPOCH
    /\ LET newManifestId == wManifest[w].id + 1 
           newManifest == [wManifest[w] EXCEPT !.id = newManifestId,
                                               !.writerEpoch = @ + 1]
       IN \/ /\ newManifestId \in DOMAIN manifest
             /\ wState' = [wState EXCEPT ![w] = IDLE]
             /\ UNCHANGED <<manifest, wManifest>>
          \/ /\ newManifestId \notin DOMAIN manifest
             /\ manifest' =  manifest @@ (newManifestId :> newManifest)
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = CHECK_BOUNDARY]
    /\ UNCHANGED <<gcVars, auxVars, wal, snapshot, boundary, wNextWalId,  
                   wEpoch, wManifestLoad, wMachineData, wNextWalId, wReplayId>>

(* ---------------------------------------------------------
    ACTION: CheckBoundary

    The writer reads the boundary file and checks if the
    manifest id it just wrote is valid (above the boundary).
    If it is not valid, it transitions back to IDLE where
    it can try to initialize again. If the manifest is still
    valid, it assumes the new writer epoch and transitions
    to WRITE_FENCE.
-----------------------------------------------------------*)

CheckBoundary(w) ==
    /\ wState[w] = CHECK_BOUNDARY
    /\ LET currBoundary == boundary.manifestId
       IN
            \/ /\ wManifest[w].id <= currBoundary
               /\ wState' = [wState EXCEPT ![w] = IDLE]
               /\ UNCHANGED wEpoch
            \/ /\ wManifest[w].id > currBoundary
               /\ wEpoch' = [wEpoch EXCEPT ![w] = wManifest[w].writerEpoch]
               /\ wState' = [wState EXCEPT ![w] = WRITE_FENCE]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wManifest, wManifestLoad,
                   wNextWalId, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: WriteFenceWalEntry

    The writer attempts to write a FENCE object to the next
    WAL id (that it discovered earlier), using put-if-absent.
    If an object already exists it means either:
        1) The writer has been fenced by another writer (and
           the writer shuld stop)
        2) A stale writer has written another DATA object
           to the WAL (and the writer should try the FENCE
           writer again at the next address).
    To find out whether this is case 1 or 2, the writer 
    transitions to VALIDATE_BEFORE_RETRY.

    If the fence write succeeded, then the writer must
    validate it's manifest before the WAL replay phase. So
    it transitions to VALIDATE_BEFORE_REPLAY.
-----------------------------------------------------------*)

WriteFenceWalEntry(w) ==
    /\ wState[w] = WRITE_FENCE
    /\ \/ /\ wNextWalId[w] \in DOMAIN wal
          /\ wState' = [wState EXCEPT ![w] = VALIDATE_BEFORE_RETRY]
          /\ UNCHANGED <<wal, auxWrittenEntries>>
       \/ /\ wNextWalId[w] \notin DOMAIN wal
          /\ LET entry == [kind  |-> FENCE, 
                           epoch |-> wEpoch[w]]
             IN
                /\ wal' = wal @@ (wNextWalId[w] :> entry)
                /\ wState' = [wState EXCEPT ![w] = VALIDATE_BEFORE_REPLAY]
    /\ UNCHANGED <<gcVars, auxVars, manifest, snapshot, boundary, wEpoch, 
                   wManifest, wManifestLoad, wNextWalId, wMachineData, wNextWalId, wReplayId>>

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
    /\ CASE DoRefresh(w) -> 
                /\ RefreshManifest(w)
                /\ UNCHANGED <<wState, wNextWalId>>
         [] wManifestLoad[w].valid = FALSE \/ wEpoch[w] < wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = FENCED]
                /\ ManifestRefreshed(w)
                /\ UNCHANGED wNextWalId
         [] wEpoch[w] > wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
                /\ ManifestRefreshed(w)
                /\ UNCHANGED wNextWalId
         [] wEpoch[w] = wManifest[w].writerEpoch ->
                /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
                /\ wState' = [wState EXCEPT ![w] = WRITE_FENCE]
                /\ ManifestRefreshed(w)
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: ValidateEpochBeforeReplay

    The writer refreshes its manifest. If it is invalid,
    it means it has been fenced so it transitions to FENCED
    and stops.
    If the manifest is still valid, it transitions to
    LOAD_SNAPSHOT, which is the first step in rebuilding
    the state machine data. This is not strictly part
    of SlateDB, but a minor tweak to make the spec work
    like the others in this repo.
-----------------------------------------------------------*)

ValidateEpochBeforeReplay(w) ==
    /\ wState[w] = VALIDATE_BEFORE_REPLAY
    /\ CASE DoRefresh(w) -> 
                /\ RefreshManifest(w)
                /\ UNCHANGED <<wState, wNextWalId, wReplayId>>
         [] wManifestLoad[w].valid = FALSE \/ wEpoch[w] < wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = FENCED]
                /\ ManifestRefreshed(w)
                /\ UNCHANGED <<wNextWalId, wReplayId>>
         [] wEpoch[w] > wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
                /\ ManifestRefreshed(w)
                /\ UNCHANGED <<wNextWalId, wReplayId>>
         [] wEpoch[w] = wManifest[w].writerEpoch ->
                 /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
                 /\ wReplayId' = [wReplayId EXCEPT ![w] = wManifest[w].replayAfterWalId]
                 /\ wState' = [wState EXCEPT ![w] = LOAD_SNAPSHOT]
                 /\ ManifestRefreshed(w)
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wMachineData>>

(* ---------------------------------------------------------
    ACTION: LoadSnapshot

    The writer loads the snapshot file whose Id is
    the replayAfterWalId - 1 (as the replayAfterWalId
    is advanced based on flushing snapshots).
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
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, wManifestLoad, wNextWalId>>

(* ---------------------------------------------------------
    ACTION: ReplayWAL

    The writer replays the WAL entries in the range of
    [replayAfterWalId -> written fenced object id].
    This spec maintains a cursor position wReplayId
    which was set to replayAfterWalId in the previous step.
    Each DATA object read is applied to the machine data.

    Once the writer has replayed this fixed range, it
    transitions to READY, where it can accept writes.

    In the case that the object does not exist, the writer
    transitions to VALIDATE_BEFORE_NOT_FOUND. It needs
    to detect whether it is stale or whether the object
    erroneously does not exist (should never happen).
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
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId, wManifest, wManifestLoad>>

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
    /\ CASE DoRefresh(w) -> 
                /\ RefreshManifest(w)
                /\ UNCHANGED wState
         [] wManifestLoad[w].valid = FALSE \/ wEpoch[w] < wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = FENCED]
                /\ ManifestRefreshed(w)
         [] wEpoch[w] > wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
                /\ ManifestRefreshed(w)
         [] wEpoch[w] = wManifest[w].writerEpoch ->
                /\ wState' = [wState EXCEPT ![w] = NOT_FOUND]
                /\ ManifestRefreshed(w)
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, 
                   wNextWalId, wReplayId, wMachineData>>

(* ---------------------------------------------------------
    ACTION: AppendEntryToWAL

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
       \/ LET entry == [kind  |-> DATA,
                        epoch |-> wEpoch[w],
                        value |-> v]
          IN
            /\ wNextWalId[w] \notin DOMAIN wal
            /\ wal' = wal @@ (wNextWalId[w] :> entry)
            /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
            /\ wMachineData' = [wMachineData EXCEPT ![w] = Append(@, v)]
            /\ auxUsedValues' = auxUsedValues \union {v}
            /\ auxWrittenEntries' = Append(auxWrittenEntries, [walId |-> wNextWalId[w],
                                                               value |-> v])
            /\ UNCHANGED wState
    /\ UNCHANGED <<gcVars, manifest, snapshot, boundary,
                   wEpoch, wManifest, wManifestLoad, wReplayId>>

(* ---------------------------------------------------------
    ACTION: WriteSnapshot

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
    /\ UNCHANGED <<gcVars, auxVars, wal, manifest, boundary, 
                   wEpoch, wManifest, wManifestLoad, wNextWalId, wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: CommitSnapshot

    The writer writes the new manifest with the updated
    replayAfterWalId. Because the WAL so far has been
    flushed (in this case as a machine data snapshot),
    the replayAfterWalId can be advanced to the next
    Id after this snapshot. 
    The writer doesn't need to check the boundary here
    as if a stale writer writes a snapshot that
    no-one will ever read, then it isn't an issue. It
    could of course write an invalid manifest file with
    a stale snapshot, but other writers always check the
    boundary after loading/refreshing the manifest, so
    it would never be acted on.
-----------------------------------------------------------*)

CommitSnapshot(w) ==
    /\ wState[w] = COMMIT_SNAPSHOT
    /\ LET snapshotId    == wNextWalId[w] - 1
           newManifestId == wManifest[w].id + 1
           newManifest == [wManifest[w] EXCEPT !.id = newManifestId,
                                               !.replayAfterWalId = snapshotId + 1]
        \*    currBoundary == boundary.manifestId
       IN
          \/ /\ newManifestId \in DOMAIN manifest
                \* \/ newManifestId <= currBoundary
             /\ wState' = [wState EXCEPT ![w] = FENCED]
             /\ UNCHANGED <<manifest, wManifest>>
          \/ /\ newManifestId \notin DOMAIN manifest
             /\ manifest' = manifest @@ (newManifestId :> newManifest)
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = READY]
    /\ UNCHANGED <<gcVars, auxVars, wal, snapshot, boundary, wManifestLoad,
                   wEpoch, wNextWalId, wMachineData, wReplayId>>

\* Manifest + WAL GC ---------------------------------------------------------

(* ---------------------------------------------------------
    ACTION: StartGC

    A new GC process starts, either as a manifest or
    a WAL GC task. It starts by reading the latest
    manifest. It transitions to LOAD_BOUNDARY.
-----------------------------------------------------------*)

StartGC(gc) ==
    /\ gcState[gc] = IDLE
    /\ \E type \in {MANIFEST_GC, WAL_GC} :
        /\ gcType' = [gcType EXCEPT ![gc] = type]
        /\ gcManifest' = [gcManifest EXCEPT ![gc] = ReadLastManifest]
        /\ gcState' = [gcState EXCEPT ![gc] = LOAD_BOUNDARY]
        /\ UNCHANGED <<storeVars, writerVars, auxVars, gcBoundary, gcLastWalId>>

(* ---------------------------------------------------------
    ACTION: LoadGcBoundary

    A new GC process has loaded a manifest and must now
    check that the manifest is valid (by loading and
    checking the GC boundary). If the manifest is invalid,
    the GC process transitions back to IDLE where it
    can start again.
    If the manifest is valid then, as a manifest-GC task
    it transitions to COMPUTE_BOUNDARY, else it transitions
    to FIND_LAST_WAL_ID.
-----------------------------------------------------------*)

LoadGcBoundary(gc) ==
    /\ gcState[gc] = LOAD_BOUNDARY
    /\ \/ /\ gcManifest[gc].id <= boundary.manifestId
          /\ gcState' = [gcState EXCEPT ![gc] = IDLE]
          /\ UNCHANGED gcBoundary 
       \/ /\ gcManifest[gc].id > boundary.manifestId
          /\ gcBoundary' = [gcBoundary EXCEPT ![gc] = boundary]
          /\ gcState' = [gcState EXCEPT ![gc] = 
                            IF gcType[gc] = MANIFEST_GC
                            THEN COMPUTE_BOUNDARY
                            ELSE FIND_LAST_WAL_ID]
    /\ UNCHANGED <<storeVars, writerVars, auxVars,
                   gcLastWalId, gcManifest, gcType>>
    
(* ---------------------------------------------------------
    ACTION: ComputeMaxManifestId

    The manifest GC task discovers the highest manifest
    below the current one, to know which manifests it
    can delete. 
-----------------------------------------------------------*)

MaxManifestId(gc) ==
    IF ~\E id \in DOMAIN manifest : id < gcManifest[gc].id
    THEN 0
    ELSE CHOOSE id \in DOMAIN manifest : 
                    /\ id < gcManifest[gc].id
                    /\ ~\E id1 \in DOMAIN manifest :
                        /\ id1 < gcManifest[gc].id
                        /\ id1 > id
             
ComputeMaxManifestId(gc) ==
    /\ gcState[gc] = COMPUTE_BOUNDARY
    /\ gcBoundary' = [gcBoundary EXCEPT ![gc].manifestId = MaxManifestId(gc)]
    /\ gcState' = [gcState EXCEPT ![gc] = ADVANCE_BOUNDARY]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, gcManifest, 
                   gcLastWalId, gcType>>

(* ---------------------------------------------------------
    ACTION: AdvanceGcBoundary

    The manifest GC task attempts a CAS write to the boundary
    file. If the CAS fails (another GC process already updated
    the file), the GC process goes back to IDLE where it can
    start again.
-----------------------------------------------------------*)

AdvanceGcBoundary(gc) ==
    /\ gcState[gc] = ADVANCE_BOUNDARY
    /\ CASE gcBoundary[gc].version < boundary.version ->
                /\ gcState' = [gcState EXCEPT ![gc] = IDLE]
                /\ UNCHANGED <<boundary, gcBoundary>>
         [] gcBoundary[gc].version > boundary.version ->
                /\ gcState' = [gcState EXCEPT ![gc] = ILLEGAL_STATE]
                /\ UNCHANGED <<boundary, gcBoundary>>
         [] /\ gcBoundary[gc].version = boundary.version
            /\ gcBoundary[gc].manifestId > boundary.manifestId ->
                LET newBoundary == [gcBoundary[gc] EXCEPT !.version  = @ + 1]
                IN /\ boundary' = newBoundary 
                   /\ gcBoundary' = [gcBoundary EXCEPT ![gc] = newBoundary] 
                   /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
         [] OTHER -> 
                /\ gcState' = [gcState EXCEPT ![gc] = DONE]
                /\ UNCHANGED <<boundary, gcBoundary>> 
    /\ UNCHANGED <<writerVars, auxVars, manifest, wal, snapshot, 
                   gcManifest, gcLastWalId, gcType>>

(* ---------------------------------------------------------
    ACTION: DeleteManifest

    The manifest GC task has advanced the GC boundary
    and starts deleting manifest files with ids
    <= the boundary
-----------------------------------------------------------*)

DeleteManifest(gc) ==
    /\ gcType[gc] = MANIFEST_GC
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN manifest :
        /\ id <= gcBoundary[gc].manifestId
        /\ manifest' = [i \in (DOMAIN manifest \ {id}) |-> manifest[i]]
        /\ UNCHANGED <<gcLastWalId, boundary, wal, snapshot, 
                       writerVars, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: FindLastWalId

    A WAL GC task finds the last WAL Id, that it 
    later guarantees not to delete.
-----------------------------------------------------------*)

FindLastWalId(gc) ==
    /\ gcState[gc] = FIND_LAST_WAL_ID
    /\ gcLastWalId' = [gcLastWalId EXCEPT ![gc] = LastWalId]
    /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, gcManifest,
                   gcBoundary, gcType>> 

(* ---------------------------------------------------------
    ACTION: DeleteWalEntry

    A WAL GC task deletes a DATA object in the WAL whose
    Id is below the replayAfterWalId of the latest
    manifest (loaded previously) and not the last object
    in the WAL.
-----------------------------------------------------------*)

DeletableWalEntry(gc, id) ==
    /\ id < gcManifest[gc].replayAfterWalId
    /\ id < gcLastWalId[gc]
    /\ wal[id].kind = DATA
    
DeleteWalEntry(gc) ==
    /\ gcType[gc] = WAL_GC
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN wal :
        /\ DeletableWalEntry(gc, id)
        /\ wal' = [i \in (DOMAIN wal \ {id}) |-> wal[i]]
    /\ UNCHANGED <<manifest, boundary, snapshot,
                   writerVars, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: DeleteSnapshot

    A WAL GC task deletes a snapshot file below the 
    last written snapshot. Not strictly part of SlateDB,
    but included to harmonize with other specs.
-----------------------------------------------------------*)

DeletableSnapshot(gc, id) ==
    id < gcManifest[gc].replayAfterWalId - 1

DeleteSnapshot(gc) ==
    /\ gcType[gc] = WAL_GC
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN snapshot :
        /\ DeletableSnapshot(gc, id)
        /\ snapshot' = [i \in (DOMAIN snapshot \ {id}) |-> snapshot[i]]
        /\ UNCHANGED <<boundary, wal, manifest, writerVars, 
                       gcVars, auxVars>>

\* ****************************************************
\* TYPE correctness
\* ****************************************************

DataObjectType == [kind: {DATA}, epoch: Nat, value: Values]
FenceObjectType == [kind: {FENCE}, epoch: Nat]
WALObjectType == DataObjectType \union FenceObjectType

ManifestType ==
    [id: Nat, 
     writerEpoch: Nat, 
     replayAfterWalId: Nat]

BoundaryType == [manifestId: Nat, version: Nat]

MachineDataType == Seq(Values)
HistoryEntryType == [walId: Nat, value: Values]

TypeOK ==
    /\ \A id \in DOMAIN manifest : 
        id \in Nat /\ manifest[id] \in ManifestType
    /\ \A id \in DOMAIN wal : 
        id \in Nat /\ wal[id] \in WALObjectType
    /\ \A id \in DOMAIN snapshot : 
        id \in Nat /\ snapshot[id] \in Seq(Values)
    /\ boundary \in BoundaryType
    /\ wState \in [Writers -> {IDLE, FIND_NEXT_WAL_ID, CLAIM_EPOCH, CHECK_BOUNDARY, WRITE_FENCE,
                               VALIDATE_BEFORE_RETRY, VALIDATE_BEFORE_REPLAY, VALIDATE_BEFORE_NOT_FOUND,
                               LOAD_SNAPSHOT, REPLAY_WAL, READY, COMMIT_SNAPSHOT, FENCED, NOT_FOUND}]
    /\ wEpoch \in [Writers -> Nat]
    /\ wManifest \in [Writers -> ManifestType \union {NIL}]
    /\ wManifestLoad \in [Writers -> [loaded: BOOLEAN, checked: BOOLEAN, valid: BOOLEAN]]
    /\ wNextWalId \in [Writers -> Nat]
    /\ wMachineData \in [Writers -> MachineDataType]
    /\ wReplayId \in [Writers -> Nat]
    /\ gcType \in [GarbageCollectors -> {MANIFEST_GC, WAL_GC, NIL}]
    /\ gcState \in [GarbageCollectors -> {IDLE, LOAD_BOUNDARY, COMPUTE_BOUNDARY, 
                                          ADVANCE_BOUNDARY, FIND_LAST_WAL_ID, 
                                          DELETE, DONE}]
    /\ gcLastWalId \in [GarbageCollectors -> Nat]
    /\ gcBoundary \in [GarbageCollectors -> BoundaryType \union {NIL}] 
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
            /\ IF wManifest[w].id = LastManifestId
               THEN Len(wMachineData[w]) = Len(auxWrittenEntries)
               ELSE TRUE

\* INV: ManifestRepresentsCommittedLog
\* Central WAL safety property: every committed value remains ,
\* reconstructible from the current manifest.
ManifestRepresentsCommittedLog ==
    LET m          == ReadLastManifest 
        snapshotId == m.replayAfterWalId - 1
        snap       == IF snapshotId = 0 THEN <<>>
                      ELSE snapshot[snapshotId]
        hist       == auxWrittenEntries
    IN
        \* The current snapshot is a prefix of the recorded write history
        /\ PrefixOf(snap, hist)
        \* For every written id ...
        /\ \A i \in 1..Len(hist) :
            LET histEntry == hist[i]
                snapEntry == snap[i]
                walEntry  == wal[histEntry.walId] 
            IN
                \* either the id is before the WAL and thus exists
                \* in the snapshot
                \/ /\ histEntry.walId < m.replayAfterWalId
                   /\ snapEntry = histEntry.value
                \* or the id is in the WAL id range and thus exists
                \* in the WAL
                \/ /\ histEntry.walId >= m.replayAfterWalId
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
        <>[](gcState[gc] \in {DELETE, DONE})        

\* ****************************************************
\* INIT, NEXT and Spec
\* ****************************************************

Init ==
    /\ manifest = <<>> @@ (0 :> [id               |-> 1, 
                                 writerEpoch      |-> 0, 
                                 replayAfterWalId |-> 1])
    /\ wal = <<>>
    /\ snapshot = <<>>
    /\ boundary = [manifestId |-> 0, version |-> 0]
    /\ wState = [w \in Writers |-> IDLE]
    /\ wEpoch = [w \in Writers |-> 0]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ wManifestLoad = [w \in Writers |-> [loaded  |-> FALSE,
                                           checked |-> FALSE,
                                           valid   |-> FALSE]]
    /\ wNextWalId = [w \in Writers |-> 1]
    /\ wMachineData = [w \in Writers |-> <<>>]
    /\ wReplayId = [w \in Writers |-> 0]
    /\ gcType = [gc \in GarbageCollectors |-> NIL]
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ gcLastWalId = [gc \in GarbageCollectors |-> 0]
    /\ gcBoundary = [gc \in GarbageCollectors |-> NIL]
    /\ gcManifest = [gc \in GarbageCollectors |-> NIL]
    /\ auxUsedValues = {}
    /\ auxWrittenEntries = <<>>

Next ==
    \/ \E w \in Writers :
        \* Writer initialization
        \/ StartWriter(w)
        \/ FindNextWalId(w)
        \/ ClaimEpoch(w)
        \/ CheckBoundary(w)
        \/ WriteFenceWalEntry(w)
        \/ ValidateEpochBeforeWalFenceRetry(w)
        \/ ValidateEpochBeforeReplay(w)
        \/ LoadSnapshot(w)
        \/ ReplayWAL(w)
        \/ ValidateBeforeNotFound(w)
        \* Established writer steady state
        \/ \E v \in Values : AppendEntryToWAL(w, v)
        \/ WriteSnapshot(w)
        \/ CommitSnapshot(w)
    \/ \E gc \in GarbageCollectors :
        \/ StartGC(gc)
        \/ LoadGcBoundary(gc)
        \/ ComputeMaxManifestId(gc)
        \/ AdvanceGcBoundary(gc)
        \/ DeleteManifest(gc)
        \/ FindLastWalId(gc)
        \/ DeleteWalEntry(gc)
        \/ DeleteSnapshot(gc)
        
Fairness ==
    \A w \in Writers :
        \* Writer initialization
        /\ WF_vars(StartWriter(w))
        /\ WF_vars(FindNextWalId(w))
        /\ WF_vars(ClaimEpoch(w))
        /\ WF_vars(CheckBoundary(w))
        /\ WF_vars(WriteFenceWalEntry(w))
        /\ WF_vars(ValidateEpochBeforeWalFenceRetry(w))
        /\ WF_vars(ValidateEpochBeforeReplay(w))
        /\ WF_vars(LoadSnapshot(w))
        /\ WF_vars(ReplayWAL(w))
        /\ WF_vars(ValidateBeforeNotFound(w))
        \* Established writer steady state
        /\ \A v \in Values : WF_vars(AppendEntryToWAL(w, v))
        /\ WF_vars(WriteSnapshot(w))
        /\ WF_vars(CommitSnapshot(w))
    /\ \A gc \in GarbageCollectors :
        /\ WF_vars(StartGC(gc))
        /\ WF_vars(LoadGcBoundary(gc))
        /\ WF_vars(ComputeMaxManifestId(gc))
        /\ WF_vars(AdvanceGcBoundary(gc))
        /\ WF_vars(DeleteManifest(gc))
        /\ WF_vars(FindLastWalId(gc))
        /\ WF_vars(DeleteWalEntry(gc))
        /\ WF_vars(DeleteSnapshot(gc))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
