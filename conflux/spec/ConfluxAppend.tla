---------------- MODULE ConfluxAppend ----------------

(*
    This module represents the log writer. Models only one
    append at a time per replica. The abstractions of the
    VirtualLog, AtomicLog and LogDrive are not explicitly
    modeled as modularized components.
*)

EXTENDS ConfluxCommon

notAppendVars == <<rApply, rGC, rReconf>>

\**********************************************************
\* DATA MODEL and Task Init
\**********************************************************

EmptyAppend == [state     |-> READY,
                value     |-> None,
                logletId  |-> 0,
                slot      |-> 0]

AppendTaskType ==
    [state: {READY, ACQUIRE_SLOT, WRITE, COMPLETE_SLOT,
             CHECK_SEAL, AWAIT_RECONFIG},
     value: Values \union {None},
     logletId: 0..MaxLoglets,
     slot: 0..MaxLogletLength]

AppendTypeOK == 
    rAppend \in [Replicas -> AppendTaskType]

AppendInit == 
    rAppend = [r \in Replicas |-> EmptyAppend]

\**********************************************************
\* ACTIONS
\**********************************************************

(* ---------------------------------------------------------
    ACTION: AppendCrash

    Discard the replica's pending append and return to READY.
    An entry already written to storage may survive the crash.
-----------------------------------------------------------*)

AppendCrash(r) == 
    rAppend' = [rAppend EXCEPT ![r] = EmptyAppend]

(* ---------------------------------------------------------
    ACTION: AcceptWrite

    Accept a new value and target the cached active loglet,
    and transition to ACQUIRE_SLOT.
-----------------------------------------------------------*)

AcceptWrite(r, v) ==
    /\ rAppend[r].state = READY
    /\ rManifest[r] /= None
    /\ v \notin auxUsedValues
    /\ rAppend' = [rAppend EXCEPT ![r] =
                        [state     |-> ACQUIRE_SLOT, 
                         value     |-> v,
                         logletId  |-> CachedActiveLogletId(r), 
                         slot      |-> 0]]
    /\ auxUsedValues' = auxUsedValues \union {v}
    /\ UNCHANGED <<notAppendVars, storeVars, rManifest, rSequencer, auxAckOK, auxHistory>>

(* ---------------------------------------------------------
    ACTION: AcquireSlot

    Acquire the next free slot from the cached loglet's
    sequencer and transition to WRITE. An unavailable
    sequencer or a full loglet transitions to AWAIT_RECONFIG.
-----------------------------------------------------------*)

AcquireSlot(r) ==
    /\ rAppend[r].state = ACQUIRE_SLOT
    /\ LET lId == rAppend[r].logletId
           lRef == CachedLogletRef(r, lId) 
       IN
          IF ~SequencerAvailable(lRef)
          THEN /\ rAppend' = [rAppend EXCEPT ![r].state = AWAIT_RECONFIG]
               /\ UNCHANGED rSequencer
          ELSE 
               LET slot == NextSlot(lRef) IN
                  IF slot > MaxLogletLength
                  THEN /\ rAppend' = [rAppend EXCEPT ![r].state = AWAIT_RECONFIG]
                       /\ UNCHANGED rSequencer
                  ELSE /\ AcquireSequencerSlot(lRef.seq, slot)
                       /\ rAppend' = [rAppend EXCEPT ![r].slot = slot,
                                                     ![r].state = WRITE]
    /\ UNCHANGED <<notAppendVars, storeVars, rManifest, auxVars>>

(* ---------------------------------------------------------
    ACTION: WriteValue

    PUT the pending value at its acquired slot and
    transition to COMPLETE_SLOT. The PUT may arrive after
    sealing, reconfiguration, or garbage collection.
-----------------------------------------------------------*)

WriteValue(r) ==
    /\ rAppend[r].state = WRITE
    /\ PutEntry(rAppend[r].logletId, rAppend[r].slot, rAppend[r].value)
    /\ rAppend' = [rAppend EXCEPT ![r].state = COMPLETE_SLOT]
    /\ UNCHANGED <<notAppendVars, manifest, sealbits, snapshots, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: CompleteSlot

    Complete the acquired slot once all earlier slots
    have completed, then transition to CHECK_SEAL.
    An unavailable sequencer transitions to AWAIT_RECONFIG.
-----------------------------------------------------------*)

CompleteSlot(r) ==
    /\ rAppend[r].state = COMPLETE_SLOT
    /\ LET lId == rAppend[r].logletId
           lRef == CachedLogletRef(r, lId)
           slot == rAppend[r].slot
       IN IF ~SequencerAvailable(lRef)
          THEN /\ rAppend' = [rAppend EXCEPT ![r].state = AWAIT_RECONFIG]
               /\ UNCHANGED rSequencer
          ELSE /\ CanCompleteSlot(lRef.seq, slot)
               /\ CompleteSequencerSlot(lRef.seq, slot)
               /\ rAppend' = [rAppend EXCEPT ![r].state = CHECK_SEAL]
    /\ UNCHANGED <<notAppendVars, storeVars, rManifest, auxVars>>

(* ---------------------------------------------------------
    ACTION: CheckSealBeforeAck

    Read the target loglet's seal bit after slot completion.
    An unset bit permits acknowledgment. A set bit transitions
    to AWAIT_RECONFIG to where the result of the write
    can be resolved.
-----------------------------------------------------------*)

AppendFinish(r) ==
    \* Acknowledge the pending value at its global index
    \* and return to READY. Record the write to history.
    \* Application state is advanced separately by Apply.
    /\ LET lId == rAppend[r].logletId
           lRef == CachedLogletRef(r, lId)
           index == GlobalIndex(lRef, rAppend[r].slot)
       IN \* auxHistory records the committed prefix observed so far.
          \* The history is maintained by both writer (Append) and
          \* log reader (Apply). Whoever gets there first extends 
          \* the history;
          /\ RecordHistory(index)
          \* Check that the value being acknowledged at the given
          \* global index matches the updated history. For example,
          \* if a reader read this entry before the writer got here,
          \* do the reader and writer agree on the value at this
          \* slot/index?
          /\ auxAckOK' = /\ auxAckOK
                         /\ index \in DOMAIN auxHistory'
                         /\ auxHistory'[index] = rAppend[r].value
    /\ rAppend' = [rAppend EXCEPT ![r] = EmptyAppend]

CheckSealBeforeAck(r) ==
    /\ rAppend[r].state = CHECK_SEAL
    /\ IF IsSealed(rAppend[r].logletId)
       THEN /\ rAppend' = [rAppend EXCEPT ![r].state = AWAIT_RECONFIG]
            /\ UNCHANGED <<auxAckOK, auxHistory>>
       ELSE AppendFinish(r)
    /\ UNCHANGED <<notAppendVars, storeVars, rManifest, rSequencer, auxUsedValues>>

(* ---------------------------------------------------------
    ACTION: AppendTimeout

    Treat an unfinished append's outcome as ambiguous and
    transition to AWAIT_RECONFIG. Keep its value and slot
    until the cached sealed tail determines the outcome.
-----------------------------------------------------------*)

AppendTimeout(r) ==
    /\ rAppend[r].state \in {ACQUIRE_SLOT, WRITE, COMPLETE_SLOT, CHECK_SEAL}
    /\ rAppend' = [rAppend EXCEPT ![r].state = AWAIT_RECONFIG]
    /\ UNCHANGED <<notAppendVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: CheckManifest

    Wait until a manifest refresh includes the appender's 
    loglet as sealed.
    If the appender has acquired the slot and the slot is 
    below the tail, the append can be acknowledged.
    Else, the appender resets to retry the append again,
    in the new active loglet.
-----------------------------------------------------------*)

CheckManifest(r) ==
    /\ rAppend[r].state = AWAIT_RECONFIG
    /\ rManifest[r] /= None
    /\ LET lId == rAppend[r].logletId
           lRef == CachedLogletRef(r, lId)
           slot == rAppend[r].slot
       IN /\ lRef.tail /= 0
          /\ IF slot > 0 /\ slot < lRef.tail
             THEN AppendFinish(r)
             ELSE /\ rAppend' = [rAppend EXCEPT
                                    ![r].logletId = CachedActiveLogletId(r),
                                    ![r].slot = 0, 
                                    ![r].state = ACQUIRE_SLOT]
                  /\ UNCHANGED <<auxAckOK, auxHistory>>
    /\ UNCHANGED <<notAppendVars, storeVars, rManifest, rSequencer, auxUsedValues>>

=============================================================================
