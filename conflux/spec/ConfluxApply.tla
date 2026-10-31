---------------- MODULE ConfluxApply ----------------

(*
    This module represents the application, or state-machine,
    that sits atop the virtual log, reading and applying
    log entries to its state.
    The abstractions of the VirtualLog, AtomicLog and LogDrive 
    are not explicitly modeled as modularized components.
*)

EXTENDS ConfluxCommon

notApplyVars == <<rAppend, rGC, rReconf>>

\**********************************************************
\* DATA MODEL and Task Init
\**********************************************************

\* tail and candidate are exclusive global indexes; 0 means unset.
EmptyApply == [state        |-> REFRESH_MANIFEST,
               data         |-> <<>>,
               tail         |-> 0,
               candidate    |-> 0,
               tailResponse |-> None]

\* A response in flight: an exclusive local tail or an unavailable result.
TailResponseType ==
    [logletId: LogletIds,
     tail: (1..(MaxLogletLength + 1)) \union {Down}]

ApplyType ==
    [state: {REFRESH_MANIFEST, REFRESH_AFTER_MISSING, LOAD_SNAPSHOT, CHECKTAIL,
             RECEIVE_TAIL, CHECK_SEAL, READ_NEXT, AWAIT_RECONFIG, ENTRY_NOT_FOUND},
     data: Seq(Values),
     tail: 0..(MaxIndex + 1),
     candidate: 0..(MaxIndex + 1),
     tailResponse: TailResponseType \union {None}]

ApplyTypeOK == rApply \in [Replicas -> ApplyType]

ApplyInit == rApply = [r \in Replicas |-> EmptyApply]

\* Helpers -------

TransitionTo(r, state) == 
    [EmptyApply EXCEPT !.state = state, 
                       !.data = rApply[r].data]

\**********************************************************
\* TASK ACTIONS
\**********************************************************

(* ---------------------------------------------------------
    ACTION: ApplyCrash

    Lose the replica's application state and pending response.
    Late responses to the abandoned request are discarded.
    Restart at REFRESH_MANIFEST to recover from durable data.
-----------------------------------------------------------*)

ApplyCrash(r) == 
    rApply' = [rApply EXCEPT ![r] = EmptyApply]

(* ---------------------------------------------------------
    ACTION: RefreshManifest

    GET the manifest from S3, updating the shared cache (shared
    between tasks in a replica).
    If applied data trails the trim point, load the snapshot.
    Otherwise a missing expected entry leads to ENTRY_NOT_FOUND;
    normal refreshes proceed to CHECKTAIL. While awaiting
    reconfiguration, refresh only when the version changes.
-----------------------------------------------------------*)

RefreshManifest(r) ==
    /\ \/ rApply[r].state \in {REFRESH_MANIFEST, REFRESH_AFTER_MISSING}
       \/ /\ rApply[r].state = AWAIT_RECONFIG
          /\ rManifest[r].version /= manifest.version
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rApply' = [rApply EXCEPT ![r] = TransitionTo(r,
                    IF Len(rApply[r].data) < manifest.trimIndex
                    THEN LOAD_SNAPSHOT
                    ELSE IF rApply[r].state = REFRESH_AFTER_MISSING
                         THEN ENTRY_NOT_FOUND ELSE CHECKTAIL)]
    /\ UNCHANGED <<notApplyVars, storeVars, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: LoadSnapshot

    Restore application data from the cached manifest's
    snapshot and transition to CHECKTAIL.
-----------------------------------------------------------*)

LoadSnapshot(r) ==
    /\ rApply[r].state = LOAD_SNAPSHOT
    /\ LET data == snapshots[rManifest[r].snapshot]
       IN rApply' = [rApply EXCEPT ![r] =
                        [EmptyApply EXCEPT !.data = data, 
                                           !.state = CHECKTAIL]]
    /\ UNCHANGED <<notApplyVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: FastCheckTail

    Send the tail request using the cached active loglet.
    Request handling produces a response containing the local
    tail or an unavailable result, then enters RECEIVE_TAIL.
    Delivery occurs separately; later sequencer changes do
    not alter the response already in flight.
-----------------------------------------------------------*)

FastCheckTail(r) ==
    /\ rApply[r].state = CHECKTAIL
    /\ LET lRef == CachedActiveLogletRef(r) IN
        rApply' = [rApply EXCEPT
            ![r].tailResponse = [logletId |-> lRef.id,
                                 tail |-> IF SequencerAvailable(lRef)
                                          THEN SequencerTail(lRef) 
                                          ELSE Down],
            ![r].state = RECEIVE_TAIL]
    /\ UNCHANGED <<notApplyVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: FastCheckTailResponse

    Receive the sequencer tail response.
    Translate a returned local tail using cached metadata and
    proceed to CHECK_SEAL. An unavailable result transitions
    to AWAIT_RECONFIG. Both outcomes consume the response.
-----------------------------------------------------------*)

FastCheckTailResponse(r) ==
    /\ rApply[r].state = RECEIVE_TAIL
    /\ LET response == rApply[r].tailResponse IN
        IF response.tail = Down
        THEN rApply' = [rApply EXCEPT ![r] = TransitionTo(r, AWAIT_RECONFIG)]
        ELSE LET lRef == CachedLogletRef(r, response.logletId) IN
            rApply' = [rApply EXCEPT ![r].candidate = GlobalIndex(lRef, response.tail),
                                     ![r].tailResponse = None,
                                     ![r].state = CHECK_SEAL]
    /\ UNCHANGED <<notApplyVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: CheckSealBeforeRead

    Read the active loglet's seal bit after checking its tail.
    A set bit discards the candidate and awaits reconfiguration.
    Otherwise accept the tail, record the committed entries
    below it in ghost history, and transition to READ_NEXT.
-----------------------------------------------------------*)

CheckSealBeforeRead(r) ==
    /\ rApply[r].state = CHECK_SEAL
    /\ IF IsSealed(CachedActiveLogletId(r))
       THEN /\ rApply' = [rApply EXCEPT ![r] = TransitionTo(r, AWAIT_RECONFIG)]
            /\ UNCHANGED auxHistory
       ELSE /\ rApply' = [rApply EXCEPT ![r].tail = rApply[r].candidate,
                                        ![r].candidate = 0,
                                        ![r].state = READ_NEXT]
            /\ RecordHistory(rApply[r].candidate - 1)
    /\ UNCHANGED <<notApplyVars, storeVars, rManifest, rSequencer, auxUsedValues, auxAckOK>>

(* ---------------------------------------------------------
    ACTION: ReadNext

    Read and apply the next entry using cached routing.
    When the next index equals the exclusive tail, transition
    to CHECKTAIL to continue tailing with the cached manifest.
    A missing entry transitions to REFRESH_AFTER_MISSING
    so refreshed metadata can distinguish trimming from loss.
-----------------------------------------------------------*)

ReadNext(r) ==
    /\ rApply[r].state = READ_NEXT
    /\ IF Len(rApply[r].data) + 1 = rApply[r].tail
       THEN rApply' = [rApply EXCEPT ![r] = TransitionTo(r, CHECKTAIL)]
       ELSE LET index == Len(rApply[r].data) + 1
                lRef == GetLogletAt(rManifest[r], index)
                value == ReadEntry(lRef.id, index - lRef.first + 1)
            IN IF value = U
               \* The cache may predate GC. Refresh before deciding whether
               \* this entry was trimmed or a promised entry has been lost.
               THEN rApply' = [rApply EXCEPT ![r] = TransitionTo(r, REFRESH_AFTER_MISSING)]
               ELSE rApply' = [rApply EXCEPT ![r].data = Append(@, value)]
    /\ UNCHANGED <<notApplyVars, storeVars, rManifest, rSequencer, auxVars>>

=============================================================================
