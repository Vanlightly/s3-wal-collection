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
      firstReplayWalId (which is the snapshot id + 1).
    * a set of garbage collector processes that can execute either
      manifest GC or WAL GC.
        
    NOTE: ConsistentMachineData is violated when EnableFix = FALSE.
    See: https://github.com/Vanlightly/s3-wal-collection/issues/2
    This spec has been updated since this issue was created (but 
    the issue still applies to this spec), see 
    SlateDBWAL_TLAPSBENCHBUG.tla for a copy of the original spec.
*)

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,           \* The set of writer processes
          GarbageCollectors, \* The set of garbage collector processes
          Values,            \* The set of values to append
          MaxWriterRestarts  \* How many times fenced writers can restart

CONSTANTS EnableFix

\* writer states
CONSTANTS INITIAL_MANIFEST_LOAD, FIND_NEXT_WAL_ID, CLAIM_EPOCH,
          REFRESH_BEFORE_CLAIM, CHECK_BOUNDARY, CHECK_WAL_ID,
          VALIDATE_AFTER_RECOMPUTE, WRITE_FENCE, VALIDATE_BEFORE_RETRY,
          VALIDATE_BEFORE_REPLAY, VALIDATE_BEFORE_NOT_FOUND,
          VALIDATE_AFTER_REPLAY, LOAD_SNAPSHOT, REPLAY_WAL, READY,
          FENCED, NOT_FOUND

\* Manifest refresh phases
CONSTANTS REFRESH_LOAD, REFRESH_CHECK, REFRESH_DONE

\* GC tasks
CONSTANTS MANIFEST_GC, WAL_GC

\* GC states
CONSTANTS IDLE, LOAD_BOUNDARY, COMPUTE_BOUNDARY, 
          ADVANCE_BOUNDARY, DELETE, DONE

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
          wRefreshState,    \* Writer -> manifest refresh state
          wNextWalId,       \* Writer -> the next WAL Id to write to
          wMachineData,     \* Writer -> State-machine data (a sequence of Values)
          wReplayId,        \* Writer -> Current position in WAL replay
          wSnapshotId,      \* Writer -> snapshot awaiting manifest commit (0 if none)
          gcType,           \* GC -> type of GC task
          gcState,          \* GC -> state
          gcBoundary,       \* GC -> local copy of the boundary file
          gcManifest        \* GC -> local copy of a manifest

VARIABLES auxUsedValues,    
          auxWrittenEntries, \* Successful write history
          auxRestarts \* The number of fenced writer restarts

storeVars == <<manifest, boundary, wal, snapshot>>
writerVars == <<wState, wEpoch, wManifest, wRefreshState, wNextWalId,
                wMachineData, wReplayId, wSnapshotId>>
gcVars == <<gcType, gcState, gcBoundary, gcManifest>>
auxVars == <<auxUsedValues, auxWrittenEntries, auxRestarts>>
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
    RefreshManifest (sub-action, called by actions)

    Each writer has a separate manifest refresh phase:
    1. REFRESH_LOAD reads the latest manifest.
    2. REFRESH_CHECK checks its id against the GC boundary.
       An id at or below the boundary returns to REFRESH_LOAD.
       An id above the boundary advances to REFRESH_DONE.
    3. The caller consumes the checked manifest, checks its
       epoch if required, and resets the phase to REFRESH_LOAD.

    The load and boundary check are separate steps so GC
    can run between them. REFRESH_DONE records a successful
    boundary check; it does not guarantee epoch ownership.
-----------------------------------------------------------*)

ManifestRefreshDone(w) ==
    wRefreshState[w] = REFRESH_DONE

RefreshManifest(w) ==
    /\ wRefreshState[w] \in {REFRESH_LOAD, REFRESH_CHECK}
    /\ IF wRefreshState[w] = REFRESH_LOAD
       THEN /\ wManifest' = [wManifest EXCEPT ![w] = ReadLastManifest]
            /\ wRefreshState' = [wRefreshState EXCEPT ![w] = REFRESH_CHECK]
       ELSE /\ wRefreshState' = [wRefreshState EXCEPT ![w] =
                    IF wManifest[w].id > boundary.manifestId
                    THEN REFRESH_DONE
                    ELSE REFRESH_LOAD]
            /\ UNCHANGED wManifest

ResetManifestRefresh(w) ==
    /\ ManifestRefreshDone(w)
    /\ wRefreshState' = [wRefreshState EXCEPT ![w] = REFRESH_LOAD]
    /\ UNCHANGED wManifest

\* Writer actions ------------------------------------------------------

(* ---------------------------------------------------------
    ACTION: WriterInitialManifestLoad

    A writer starts initialization by loading the manifest.
    If the manifest is valid (above the boundary), it 
    transitions to FIND_NEXT_WAL_ID.

    This action will repeat until the manifest refresh
    steps are complete.
-----------------------------------------------------------*)

WriterInitialManifestLoad(w) ==
    /\ wState[w] = INITIAL_MANIFEST_LOAD
    /\ IF ManifestRefreshDone(w)
       THEN /\ ResetManifestRefresh(w)
            /\ wState' = [wState EXCEPT ![w] = FIND_NEXT_WAL_ID]
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED wState
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId, 
                   wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: FindNextWalId

    Abstract the non-atomic HEAD probe with a nondeterministic estimate.
    It cannot return below the starting manifest's replay point, but
    concurrent appends, flushes and GC can make it lower than the tip.
    The estimate survives all retries of the epoch claim.
-----------------------------------------------------------*)

FindNextWalId(w) ==
    /\ wState[w] = FIND_NEXT_WAL_ID
    /\ wState' = [wState EXCEPT ![w] = CLAIM_EPOCH]
    /\ \E id \in wManifest[w].firstReplayWalId..(LastWalId + 1) :
        wNextWalId' = [wNextWalId EXCEPT ![w] = id]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, 
                   wRefreshState, wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ClaimEpoch

    The writer attempts to write a new manifest to the
    next manifest Id using put-if-absent. If an object
    already exists, the writer refreshes and retries the claim,
    keeping the WAL id it already discovered. If it succeeds
    in writing the new manifest it transitions to
    CHECK_BOUNDARY.
-----------------------------------------------------------*)

ClaimEpoch(w) ==
    /\ wState[w] = CLAIM_EPOCH
    /\ LET newManifestId == wManifest[w].id + 1 
           newManifest == [wManifest[w] EXCEPT !.id = newManifestId,
                                               !.writerEpoch = @ + 1]
       IN \/ /\ newManifestId \in DOMAIN manifest
             /\ wState' = [wState EXCEPT ![w] = REFRESH_BEFORE_CLAIM]
             /\ UNCHANGED <<manifest, wManifest>>
          \/ /\ newManifestId \notin DOMAIN manifest
             /\ manifest' =  manifest @@ (newManifestId :> newManifest)
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = CHECK_BOUNDARY]
    /\ UNCHANGED <<gcVars, auxVars, wal, snapshot, boundary, wNextWalId,  
                   wEpoch, wRefreshState, wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: RefreshBeforeClaim

    The writer refreshes its manifest after an epoch claim
    conflict or a failed boundary check. It remains in
    REFRESH_BEFORE_CLAIM while the refresh is incomplete.
    Once it has a valid manifest, it transitions to
    CLAIM_EPOCH to retry the claim. It keeps the WAL id
    it discovered earlier throughout this process.
-----------------------------------------------------------*)

RefreshBeforeClaim(w) ==
    /\ wState[w] = REFRESH_BEFORE_CLAIM
    /\ IF ManifestRefreshDone(w)
       THEN /\ wState' = [wState EXCEPT ![w] = CLAIM_EPOCH]
            /\ ResetManifestRefresh(w)
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED wState
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId,
                   wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: CheckBoundary

    The writer reads the boundary file and checks if the
    manifest id it just wrote is valid (above the boundary).
    If it is not valid, it refreshes and retries the claim without
    rediscovering the WAL id. If the manifest is still
    valid, it assumes the new writer epoch and transitions
    to CHECK_WAL_ID to check its earlier estimate.
-----------------------------------------------------------*)

CheckBoundary(w) ==
    /\ wState[w] = CHECK_BOUNDARY
    /\ LET currBoundary == boundary.manifestId
       IN
            \/ /\ wManifest[w].id <= currBoundary
               /\ wState' = [wState EXCEPT ![w] = REFRESH_BEFORE_CLAIM]
               /\ UNCHANGED wEpoch
            \/ /\ wManifest[w].id > currBoundary
               /\ wEpoch' = [wEpoch EXCEPT ![w] = wManifest[w].writerEpoch]
               /\ wState' = [wState EXCEPT ![w] = CHECK_WAL_ID]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wManifest, wRefreshState,
                   wNextWalId, wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: CheckWalId

    After claiming an epoch, the writer checks its earlier
    WAL id estimate against the manifest's firstReplayWalId.
    An old writer may have flushed between discovery and
    the successful claim, advancing the replay point.
    If the estimate is below that point, the writer probes
    again and transitions to VALIDATE_AFTER_RECOMPUTE.
    Otherwise, it keeps the estimate and transitions to
    WRITE_FENCE.
-----------------------------------------------------------*)

CheckWalId(w) ==
    /\ wState[w] = CHECK_WAL_ID
    /\ IF wNextWalId[w] < wManifest[w].firstReplayWalId
       THEN /\ \E id \in wManifest[w].firstReplayWalId..(LastWalId + 1) :
                    wNextWalId' = [wNextWalId EXCEPT ![w] = id]
            /\ wState' = [wState EXCEPT ![w] = VALIDATE_AFTER_RECOMPUTE]
       ELSE /\ wState' = [wState EXCEPT ![w] = WRITE_FENCE]
            /\ UNCHANGED wNextWalId
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest,
                   wRefreshState, wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ValidateAfterRecompute

    The writer refreshes its manifest after recomputing the
    WAL id. Another writer may have claimed an epoch between
    the probe and this refresh. A newer stored epoch causes
    the writer to transition to FENCED. A lower stored epoch
    causes it to transition to ILLEGAL_STATE.

    If the epoch is still current, the recomputed WAL id must
    be at or above firstReplayWalId. If it is, the writer
    transitions to WRITE_FENCE. Otherwise, it transitions to
    ILLEGAL_STATE, modeling SlateDB's assertion failure.
-----------------------------------------------------------*)

ValidateAfterRecompute(w) ==
    /\ wState[w] = VALIDATE_AFTER_RECOMPUTE
    /\ IF ManifestRefreshDone(w)
       THEN /\ \/ /\ wEpoch[w] < wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = FENCED]
               \/ /\ wEpoch[w] > wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
               \/ /\ wEpoch[w] = wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] =
                                   IF wNextWalId[w] >= wManifest[w].firstReplayWalId
                                   THEN WRITE_FENCE
                                   ELSE ILLEGAL_STATE]
            /\ ResetManifestRefresh(w)
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED wState
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId,
                   wMachineData, wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: WriteFenceWalEntry

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

    After a successful fence write, an ID below the replay point
    yields ILLEGAL_STATE, modeling SlateDB's assertion failure.
    Otherwise, the writer transitions to VALIDATE_BEFORE_REPLAY
    to validate its manifest before replay.
-----------------------------------------------------------*)

WriteFenceWalEntry(w) ==
    /\ wState[w] = WRITE_FENCE
    /\ \/ /\ wNextWalId[w] \in DOMAIN wal
          /\ wState' = [wState EXCEPT ![w] = VALIDATE_BEFORE_RETRY]
          /\ UNCHANGED <<wal>>
       \/ /\ wNextWalId[w] \notin DOMAIN wal
          /\ LET entry == [kind  |-> FENCE, 
                           epoch |-> wEpoch[w]]
             IN
                /\ wal' = wal @@ (wNextWalId[w] :> entry)
                /\ wState' = [wState EXCEPT ![w] =
                                IF wNextWalId[w] >= wManifest[w].firstReplayWalId
                                THEN VALIDATE_BEFORE_REPLAY
                                ELSE ILLEGAL_STATE]
    /\ UNCHANGED <<gcVars, auxVars, manifest, snapshot, boundary, wEpoch, 
                   wManifest, wRefreshState, wNextWalId, wMachineData, 
                   wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ValidateEpochBeforeWalFenceRetry

    The writer refreshes its manifest. If the manifest
    is still valid, then the writer did not get fenced
    and it bumps its next WAL Id and transitions to 
    WRITE_FENCE.
    If the refreshed epoch is newer, the writer transitions
    to FENCED. It can restart while the configured
    restart budget permits.
-----------------------------------------------------------*)

ValidateEpochBeforeWalFenceRetry(w) ==
    /\ wState[w] = VALIDATE_BEFORE_RETRY
    /\ IF ManifestRefreshDone(w)
       THEN /\ \/ /\ wEpoch[w] < wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = FENCED]
                  /\ UNCHANGED wNextWalId
               \/ /\ wEpoch[w] > wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
                  /\ UNCHANGED wNextWalId
               \/ /\ wEpoch[w] = wManifest[w].writerEpoch
                  /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
                  /\ wState' = [wState EXCEPT ![w] = WRITE_FENCE]
            /\ ResetManifestRefresh(w)
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED <<wState, wNextWalId>>
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wMachineData, 
                   wReplayId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ValidateEpochBeforeReplay

    After the fencing write, the writer refreshes its manifest. 
    A newer epoch fences the writer. If the epoch is still 
    current, it transitions to LOAD_SNAPSHOT, which is the
    first step in rebuilding the state machine data. This
    is not strictly part of SlateDB, but a minor tweak to
    make the spec work like the others in this repo.

    NOTE: With EnableFix enabling ValidateEpochAfterReplay,
    we shouldn't actually need ValidateEpochBeforeReplay,
    for correctness anyway.
-----------------------------------------------------------*)

ValidateEpochBeforeReplay(w) ==
    /\ wState[w] = VALIDATE_BEFORE_REPLAY
    /\ IF ManifestRefreshDone(w)
       THEN /\ \/ /\ wEpoch[w] < wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = FENCED]
                  /\ UNCHANGED <<wNextWalId, wReplayId>>
               \/ /\ wEpoch[w] > wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
                  /\ UNCHANGED <<wNextWalId, wReplayId>>
               \/ /\ wEpoch[w] = wManifest[w].writerEpoch
                  /\ wNextWalId' = [wNextWalId EXCEPT ![w] = @ + 1]
                  /\ wReplayId' = [wReplayId EXCEPT ![w] = wManifest[w].firstReplayWalId]
                  /\ wState' = [wState EXCEPT ![w] = LOAD_SNAPSHOT]
            /\ ResetManifestRefresh(w)
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED <<wState, wNextWalId, wReplayId>>
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wMachineData, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: LoadSnapshot

    The writer loads the snapshot file whose Id is
    the firstReplayWalId - 1 (as the firstReplayWalId
    is advanced based on flushing snapshots).
    Again, not strictly part of SlateDB WAL protocol,
    just a minor tweak.
-----------------------------------------------------------*)

LoadSnapshot(w) ==
    /\ wState[w] = LOAD_SNAPSHOT
    /\ LET snapshotId == wManifest[w].firstReplayWalId - 1
           readSnapshot == IF snapshotId = 0
                           THEN <<>> 
                           ELSE ReadSnapshot(snapshotId)
       IN
          \/ /\ readSnapshot = NIL
             /\ wState' = [wState EXCEPT ![w] = FENCED]
             /\ UNCHANGED <<wMachineData, wReplayId>>
          \/ /\ readSnapshot /= NIL
             /\ wMachineData' = [wMachineData EXCEPT ![w] = readSnapshot]
             /\ wReplayId' = [wReplayId EXCEPT ![w] = wManifest[w].firstReplayWalId]
             /\ wState' = [wState EXCEPT ![w] = REPLAY_WAL]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wManifest, wRefreshState,
                   wNextWalId, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ReplayWAL

    The writer replays the WAL entries in the range of
    [firstReplayWalId -> written fenced object id].
    This spec maintains a cursor position wReplayId
    which was set to firstReplayWalId in the previous step.
    Each DATA object read is applied to the machine data.

    Once the writer has replayed this fixed range, it
    transitions to VALIDATE_AFTER_REPLAY, where it must
    verify that it has not been fenced (after that it
    can start serving writes).

    In the case that the object does not exist, the writer
    transitions to VALIDATE_BEFORE_NOT_FOUND. It needs
    to detect whether it is stale or whether the object
    erroneously does not exist (should never happen).
-----------------------------------------------------------*)

PostReplayState ==
    IF EnableFix THEN VALIDATE_AFTER_REPLAY ELSE READY

ReplayWAL(w) ==
    /\ wState[w] = REPLAY_WAL
    /\ LET id   == wReplayId[w]
           read == ReadWalEntry(id)
       IN
          IF id = wNextWalId[w]
          THEN /\ wState' = [wState EXCEPT ![w] = PostReplayState]
               /\ wReplayId' = [wReplayId EXCEPT ![w] = 0]
               /\ UNCHANGED wMachineData
          ELSE IF read = NIL
          THEN /\ wState' = [wState EXCEPT ![w] = VALIDATE_BEFORE_NOT_FOUND]
               /\ UNCHANGED <<wReplayId, wMachineData>>
          ELSE IF read.kind = DATA
          THEN /\ wMachineData' = [wMachineData EXCEPT ![w] = Append(@, read.value)]
               /\ wReplayId' = [wReplayId EXCEPT ![w] = @ + 1]
               /\ UNCHANGED wState
          ELSE /\ read.kind = FENCE
               /\ wReplayId' = [wReplayId EXCEPT ![w] = @ + 1]
               /\ UNCHANGED <<wState, wMachineData>>
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId, 
                   wManifest, wRefreshState, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ValidateBeforeNotFound

    The writer was unable to read a WAL object. It refreshes
    its manifest. A newer epoch fences the writer.
    If the epoch is still current, then something very bad has
    happened! NOT_FOUND should never happen.
-----------------------------------------------------------*)

ValidateBeforeNotFound(w) ==
    /\ wState[w] = VALIDATE_BEFORE_NOT_FOUND
    /\ IF ManifestRefreshDone(w)
       THEN /\ \/ /\ wEpoch[w] < wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = FENCED]
               \/ /\ wEpoch[w] > wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
               \/ /\ wEpoch[w] = wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = NOT_FOUND]
            /\ ResetManifestRefresh(w)
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED wState
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, 
                   wNextWalId, wReplayId, wMachineData, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: ValidateEpochAfterReplay

    Post-replay, the writer refreshes its manifest again.
    If the manifest epoch is higher than the writer's epoch,
    the writer transitions to FENCED; a lower epoch yields 
    ILLEGAL_STATE. If the epoch is unchanged, the writer 
    transitions to READY.

    Without this post-replay validation, the following trace
    is possible (from https://arxiv.org/pdf/2611.02849):
    1. Writer w1 becomes ready with a fence at WAL ID 1.
    2. Writer w2 chooses WAL ID 2 as its fence position. Before it claims its epoch,
    w1 appends v1 at ID 2 and v2 at ID 3.
    3. w2 claims epoch 2 and passes the boundary check, but delays writing its fence.
    4. w3 claims epoch 3, writes its fence at ID 4, validates successfully, and
    starts replaying. Pause it before replaying ID 2.
    5. w4 claims epoch 4, writes its fence at ID 5, replays the full log, and commits
    snapshot 5 containing <<v1, v2>>. The latest manifest now has ID 6 and
    replayAfterWalId = 6.
    6. The garbage collector deletes the data entry at ID 2, leaving ID 3 present.
    7. The delayed w2 writes a fence at the now-vacant ID 2.
    8. w3 skips the new fence at ID 2, reads v2 at ID 3, skips its own fence at
    ID 4, and reaches READY with machine data <<v2>>.
-----------------------------------------------------------*)

ValidateEpochAfterReplay(w) ==
    /\ wState[w] = VALIDATE_AFTER_REPLAY
    /\ IF ManifestRefreshDone(w)
       THEN /\ \/ /\ wEpoch[w] < wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = FENCED]
               \/ /\ wEpoch[w] > wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = ILLEGAL_STATE]
               \/ /\ wEpoch[w] = wManifest[w].writerEpoch
                  /\ wState' = [wState EXCEPT ![w] = READY]
            /\ ResetManifestRefresh(w)
       ELSE /\ RefreshManifest(w)
            /\ UNCHANGED wState
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wEpoch, wNextWalId,
                   wReplayId, wMachineData, wSnapshotId>>

(* ---------------------------------------------------------
    ACTION: RestartFencedWriter

    A fenced writer that has closed (and wiped all state)
    restarts. Only MaxWriterRestarts allowed to limit
    state space.
-----------------------------------------------------------*)
RestartFencedWriter(w) ==
    /\ auxRestarts < MaxWriterRestarts
    /\ wState[w] = FENCED
    /\ wState' = [wState EXCEPT ![w] = INITIAL_MANIFEST_LOAD]
    /\ wEpoch' = [wEpoch EXCEPT ![w] = 0]
    /\ wManifest' = [wManifest EXCEPT ![w] =  NIL]
    /\ wRefreshState' = [wRefreshState EXCEPT ![w] = REFRESH_LOAD]
    /\ wNextWalId' = [wNextWalId EXCEPT ![w] =  1]
    /\ wMachineData' = [wMachineData EXCEPT ![w] =  <<>>]
    /\ wReplayId' = [wReplayId EXCEPT ![w] =  0]
    /\ wSnapshotId' = [wSnapshotId EXCEPT ![w] =  0]
    /\ auxRestarts' = auxRestarts + 1
    /\ UNCHANGED <<storeVars, gcVars, auxUsedValues, auxWrittenEntries>>

(* ---------------------------------------------------------
    ACTION: AppendEntryToWAL

    A writer is the READY state accepts a write.
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
                   wEpoch, wManifest, wRefreshState, wReplayId,
                   wSnapshotId, auxRestarts>>

(* ---------------------------------------------------------
    ACTION: WriteSnapshot

    WriteSnapshot + CommitSnapshot are equivalent of Flush
    in the original Fizzbee spec.

    The flusher can run during replay or normal writes. It 
    captures the applied prefix and its WAL id, then commits
    that fixed snapshot independently of later replay or appends.
-----------------------------------------------------------*)

WriteSnapshot(w) ==
    /\ wState[w] \in {REPLAY_WAL, READY}
    /\ wSnapshotId[w] = 0
    /\ wMachineData[w] /= <<>>
    /\ LET lastSnapshotId == wManifest[w].firstReplayWalId - 1
           nextSnapshotId == IF wState[w] = REPLAY_WAL
                             THEN wReplayId[w] - 1
                             ELSE wNextWalId[w] - 1
       IN
          /\ nextSnapshotId > lastSnapshotId
          /\ nextSnapshotId \notin DOMAIN snapshot
          /\ snapshot' = snapshot @@ (nextSnapshotId :> wMachineData[w])
          /\ wSnapshotId' = [wSnapshotId EXCEPT ![w] = nextSnapshotId]
    /\ UNCHANGED <<gcVars, auxVars, wal, manifest, boundary, 
                   wState, wEpoch, wManifest, wRefreshState, wNextWalId,
                   wMachineData, wReplayId>>

(* ---------------------------------------------------------
    ACTION: CommitSnapshot

    A writer that just uploaded a snapshot writes the new manifest 
    with the updated firstReplayWalId. Because the WAL so far has
    been flushed (in this case as a machine data snapshot),
    the firstReplayWalId can be advanced to the next
    Id after this snapshot. 
    SlateDB checks the boundary after every sequenced manifest write.
    This model omits that check here as a safety overapproximation:
    a stale writer may continue after publishing a manifest below the
    boundary, but readers cannot accept that manifest.
    With compactor writes excluded, a conflicting manifest write means
    that another writer has claimed an epoch, so this writer is fenced.
-----------------------------------------------------------*)

CommitSnapshot(w) ==
    /\ wState[w] \in {REPLAY_WAL, READY}
    /\ wSnapshotId[w] > 0
    /\ LET snapshotId    == wSnapshotId[w]
           newManifestId == wManifest[w].id + 1
           newManifest == [wManifest[w] EXCEPT !.id = newManifestId,
                                               !.firstReplayWalId = snapshotId + 1]
       IN
          \/ /\ newManifestId \in DOMAIN manifest
             /\ wState' = [wState EXCEPT ![w] = FENCED]
             /\ UNCHANGED <<manifest, wManifest>>
          \/ /\ newManifestId \notin DOMAIN manifest
             /\ manifest' = manifest @@ (newManifestId :> newManifest)
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ UNCHANGED wState
    /\ wSnapshotId' = [wSnapshotId EXCEPT ![w] = 0]
    /\ UNCHANGED <<gcVars, auxVars, wal, snapshot, boundary, wRefreshState,
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
        /\ UNCHANGED <<storeVars, writerVars, auxVars, gcBoundary>>

(* ---------------------------------------------------------
    ACTION: LoadGcBoundary

    A new GC process has loaded a manifest and must now
    check that the manifest is valid (by loading and
    checking the GC boundary). If the manifest is invalid,
    the GC process transitions back to IDLE where it
    can start again.
    If the manifest is valid then, as a manifest-GC task
    it transitions to COMPUTE_BOUNDARY, else it transitions
    directly to DELETE.
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
                            ELSE DELETE]
    /\ UNCHANGED <<storeVars, writerVars, auxVars,
                   gcManifest, gcType>>
    
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
                   gcType>>

(* ---------------------------------------------------------
    ACTION: AdvanceGcBoundary

    The manifest GC task attempts a CAS write to the boundary
    file. If the CAS fails (another GC process already updated
    the file), the GC process goes back to IDLE where it can
    start again.
-----------------------------------------------------------*)

AdvanceGcBoundary(gc) ==
    /\ gcState[gc] = ADVANCE_BOUNDARY
    /\ IF gcBoundary[gc].version < boundary.version
       THEN /\ gcState' = [gcState EXCEPT ![gc] = IDLE]
            /\ UNCHANGED <<boundary, gcBoundary>>
       ELSE IF gcBoundary[gc].version > boundary.version
       THEN /\ gcState' = [gcState EXCEPT ![gc] = ILLEGAL_STATE]
            /\ UNCHANGED <<boundary, gcBoundary>>
       ELSE IF gcBoundary[gc].manifestId > boundary.manifestId
       THEN LET newBoundary == [gcBoundary[gc] EXCEPT !.version = @ + 1]
            IN /\ boundary' = newBoundary
               /\ gcBoundary' = [gcBoundary EXCEPT ![gc] = newBoundary]
               /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
       ELSE /\ gcState' = [gcState EXCEPT ![gc] = DONE]
            /\ UNCHANGED <<boundary, gcBoundary>>
    /\ UNCHANGED <<writerVars, auxVars, manifest, wal, snapshot, 
                   gcManifest, gcType>>

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
        /\ UNCHANGED <<boundary, wal, snapshot,
                       writerVars, gcVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: DeleteWalEntry

    A WAL GC task deletes a DATA object in the WAL whose
    Id is strictly below SlateDB's replay_after_wal_id, which is
    firstReplayWalId - 1 here. Keep that boundary object and all fences.
-----------------------------------------------------------*)

DeletableWalEntry(gc, id) ==
    /\ id < gcManifest[gc].firstReplayWalId - 1
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
    id < gcManifest[gc].firstReplayWalId - 1

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
     firstReplayWalId: Nat]

BoundaryType == [manifestId: Nat, version: Nat]

MachineDataType == Seq(Values)
HistoryEntryType == [walId: Nat, value: Values]

WriterStates ==
    {INITIAL_MANIFEST_LOAD, FIND_NEXT_WAL_ID, CLAIM_EPOCH, REFRESH_BEFORE_CLAIM,
     CHECK_BOUNDARY, CHECK_WAL_ID, VALIDATE_AFTER_RECOMPUTE, WRITE_FENCE,
     VALIDATE_BEFORE_RETRY, VALIDATE_BEFORE_REPLAY, VALIDATE_BEFORE_NOT_FOUND,
     VALIDATE_AFTER_REPLAY, LOAD_SNAPSHOT, REPLAY_WAL, READY, FENCED, NOT_FOUND, 
     ILLEGAL_STATE}

TypeOK ==
    /\ \A id \in DOMAIN manifest : 
        id \in Nat /\ manifest[id] \in ManifestType /\ manifest[id].id = id
    /\ \A id \in DOMAIN wal : 
        id \in Nat /\ wal[id] \in WALObjectType
    /\ \A id \in DOMAIN snapshot : 
        id \in Nat /\ snapshot[id] \in Seq(Values)
    /\ boundary \in BoundaryType
    /\ wState \in [Writers -> WriterStates]
    /\ wEpoch \in [Writers -> Nat]
    /\ wManifest \in [Writers -> ManifestType \union {NIL}]
    /\ wRefreshState \in [Writers -> {REFRESH_LOAD, REFRESH_CHECK, REFRESH_DONE}]
    /\ wNextWalId \in [Writers -> Nat]
    /\ wMachineData \in [Writers -> MachineDataType]
    /\ wReplayId \in [Writers -> Nat]
    /\ wSnapshotId \in [Writers -> Nat]
    /\ gcType \in [GarbageCollectors -> {MANIFEST_GC, WAL_GC, NIL}]
    /\ gcState \in [GarbageCollectors -> {IDLE, LOAD_BOUNDARY, COMPUTE_BOUNDARY, 
                                          ADVANCE_BOUNDARY,
                                          DELETE, DONE, ILLEGAL_STATE}]
    /\ gcBoundary \in [GarbageCollectors -> BoundaryType \union {NIL}] 
    /\ gcManifest \in [GarbageCollectors -> ManifestType \union {NIL}]
    /\ auxUsedValues \in SUBSET Values
    /\ auxWrittenEntries \in Seq(HistoryEntryType)
    /\ auxRestarts \in Nat

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

ValidGarbageCollectors ==
    \A gc \in GarbageCollectors : gcState[gc] /= ILLEGAL_STATE

\* INV: ConsistentMachineData
\* The state machine data of each READY writer matches the
\* history of successful writes.
\* If the writer is stale, it matches a prefix of write history.
\* If the writer is current, it perfectly matches the write history.
\* This is required for read consistency.
\* We only test this in READY state as the machine data can
\* become inconsistent during replay, but the post replay
\* validation detects that and fences the writer.
PrefixOf(machineData, hist) ==
    /\ Len(machineData) <= Len(hist)
    /\ \A pos \in DOMAIN machineData :
            machineData[pos] = hist[pos].value

ConsistentMachineData ==
    \A w \in Writers :
        wState[w] = READY =>
            /\ PrefixOf(wMachineData[w], auxWrittenEntries)
            /\ wManifest[w].id = LastManifestId =>
                Len(wMachineData[w]) = Len(auxWrittenEntries)

\* INV: ManifestRepresentsCommittedLog
\* Central WAL safety property: every committed value remains
\* reconstructible from the current manifest.
ManifestRepresentsCommittedLog ==
    LET m          == ReadLastManifest 
        snapshotId == m.firstReplayWalId - 1
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
                \/ /\ histEntry.walId < m.firstReplayWalId
                   /\ snapEntry = histEntry.value
                \* or the id is in the WAL id range and thus exists
                \* in the WAL
                \/ /\ histEntry.walId >= m.firstReplayWalId
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
\* Writers refresh and retry the epoch claim while retaining their WAL
\* estimate. After claiming an epoch, a newer epoch fences the writer.
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
    /\ manifest = <<>> @@ (1 :> [id               |-> 1,
                                 writerEpoch      |-> 0, 
                                 firstReplayWalId |-> 1])
    /\ wal = <<>>
    /\ snapshot = <<>>
    /\ boundary = [manifestId |-> 0, version |-> 0]
    /\ wState = [w \in Writers |-> INITIAL_MANIFEST_LOAD]
    /\ wEpoch = [w \in Writers |-> 0]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ wRefreshState = [w \in Writers |-> REFRESH_LOAD]
    /\ wNextWalId = [w \in Writers |-> 1]
    /\ wMachineData = [w \in Writers |-> <<>>]
    /\ wReplayId = [w \in Writers |-> 0]
    /\ wSnapshotId = [w \in Writers |-> 0]
    /\ gcType = [gc \in GarbageCollectors |-> NIL]
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ gcBoundary = [gc \in GarbageCollectors |-> NIL]
    /\ gcManifest = [gc \in GarbageCollectors |-> NIL]
    /\ auxRestarts = 0
    /\ auxUsedValues = {}
    /\ auxWrittenEntries = <<>>

Next ==
    \/ \E w \in Writers :
        \* Writer initialization
        \/ WriterInitialManifestLoad(w)
        \/ FindNextWalId(w)
        \/ ClaimEpoch(w)
        \/ RefreshBeforeClaim(w)
        \/ CheckBoundary(w)
        \/ CheckWalId(w)
        \/ ValidateAfterRecompute(w)
        \/ WriteFenceWalEntry(w)
        \/ ValidateEpochBeforeWalFenceRetry(w)
        \/ ValidateEpochBeforeReplay(w)
        \/ LoadSnapshot(w)
        \/ ReplayWAL(w)
        \/ ValidateBeforeNotFound(w)
        \/ ValidateEpochAfterReplay(w)
        \/ RestartFencedWriter(w)
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
        \/ DeleteWalEntry(gc)
        \/ DeleteSnapshot(gc)
        
Fairness ==
    \A w \in Writers :
        \* Writer initialization
        /\ WF_vars(WriterInitialManifestLoad(w))
        /\ WF_vars(FindNextWalId(w))
        /\ WF_vars(ClaimEpoch(w))
        /\ WF_vars(RefreshBeforeClaim(w))
        /\ WF_vars(CheckBoundary(w))
        /\ WF_vars(CheckWalId(w))
        /\ WF_vars(ValidateAfterRecompute(w))
        /\ WF_vars(WriteFenceWalEntry(w))
        /\ WF_vars(ValidateEpochBeforeWalFenceRetry(w))
        /\ WF_vars(ValidateEpochBeforeReplay(w))
        /\ WF_vars(LoadSnapshot(w))
        /\ WF_vars(ReplayWAL(w))
        /\ WF_vars(ValidateBeforeNotFound(w))
        /\ WF_vars(ValidateEpochAfterReplay(w))
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
        /\ WF_vars(DeleteWalEntry(gc))
        /\ WF_vars(DeleteSnapshot(gc))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
