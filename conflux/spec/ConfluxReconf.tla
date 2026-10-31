---------------- MODULE ConfluxReconf ----------------

(*
    This module represents the reconfiguration logic
    inside virtual log.
    The abstractions of the VirtualLog, AtomicLog and LogDrive 
    are not explicitly modeled as modularized components.
*)

EXTENDS ConfluxCommon

notReconVars == <<rApply, rAppend, rGC>>

\**********************************************************
\* DATA MODEL and Task Init
\**********************************************************

EmptyReconf == [state     |-> IDLE, 
                base      |-> None, 
                remaining |-> {},
                observed  |-> {}, 
                tail      |-> 0]

ReconfBaseType ==
    [version: Nat,
     logletRef: LogletRefType,
     trimIndex: 0..MaxIndex]

ReconfType ==
    [state: {IDLE, SEAL, SLOW_CHECKTAIL, COMMIT_RECONFIG},
     base: ReconfBaseType \union {None},
     remaining: SUBSET Slots,
     observed: SUBSET Slots,
     tail: 0..(MaxLogletLength + 1)] \* Exclusive local cutoff; 0 means unset.

ReconfTypeOK == 
    rReconf \in [Replicas -> ReconfType]

(* ---------------------------------------------------------
    ACTION: ReconfInit

    Initialize every replica with no reconfiguration
    in progress.
-----------------------------------------------------------*)

ReconfInit == 
    rReconf = [r \in Replicas |-> EmptyReconf]

\**********************************************************
\* TASK ACTIONS
\**********************************************************

(* ---------------------------------------------------------
    ACTION: ReconfCrash

    Discard the replica's in-progress reconfiguration.
    Any seal or manifest update already stored survives.
-----------------------------------------------------------*)

ReconfCrash(r) == 
    rReconf' = [rReconf EXCEPT ![r] = EmptyReconf]

(* ---------------------------------------------------------
    ACTION: StartReconfig

    Capture the cached manifest version and active loglet,
    then transition to SEAL if the loglet bound permits
    (MaxLoglets is a state-space limiter, not a protocol concept).
    An idle task may start proactively; it does not require
    a waiting append or reader. A stale base later fails CAS.
-----------------------------------------------------------*)

StartReconfig(r) ==
    /\ rReconf[r].state = IDLE
    /\ rManifest[r] /= None
    /\ CachedActiveLogletId(r) < MaxLoglets
    /\ rReconf' = [rReconf EXCEPT ![r] =
                        [EmptyReconf EXCEPT !.state = SEAL,
                                            !.base = ReconfigBase(rManifest[r])]]
    /\ UNCHANGED <<notReconVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: Seal

    Set the captured loglet's seal bit and transition to
    SLOW_CHECKTAIL. Schedule a scan of slots after the
    captured trim point; entry PUTs can still arrive
    concurrently with the unordered scan.
-----------------------------------------------------------*)

Seal(r) ==
    /\ rReconf[r].state = SEAL
    /\ LET m    == rReconf[r].base
           lRef == m.logletRef
           scanRange == GetScanStart(m, lRef)..MaxLogletLength
       IN /\ SealLoglet(lRef.id)
          /\ rReconf' = [rReconf EXCEPT ![r].state = SLOW_CHECKTAIL,
                                        ![r].remaining = scanRange]
    /\ UNCHANGED <<notReconVars, manifest, entries, snapshots, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: SlowCheckTail

    Read one remaining slot in arbitrary order and record
    whether its entry exists. Other PUTs and deletions may
    interleave, so the scan is not an atomic storage snapshot.
    See https://github.com/Vanlightly/log-drive-specs/blob/main/tlaplus/AtomicLog.tla
    for a linearizability spec.
-----------------------------------------------------------*)

SlowCheckTail(r) ==
    /\ rReconf[r].state = SLOW_CHECKTAIL
    /\ rReconf[r].remaining /= {}
    /\ \E slot \in rReconf[r].remaining :
        /\ rReconf' = [rReconf EXCEPT
                ![r].remaining = @ \ {slot},
                ![r].observed  = IF ReadEntry(rReconf[r].base.logletRef.id, slot) /= U
                                 THEN @ \union {slot} ELSE @]
    /\ UNCHANGED <<notReconVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: FinishSlowCheckTail

    After every scheduled slot has been observed, choose
    the first missing slot as the loglet tail.
    Discard scan observations and transition to COMMIT_RECONFIG.
-----------------------------------------------------------*)

FinishSlowCheckTail(r) ==
    /\ rReconf[r].state = SLOW_CHECKTAIL
    /\ rReconf[r].remaining = {}
    /\ LET m == rReconf[r].base IN
        rReconf' = [rReconf EXCEPT
            ![r].tail = FirstHole(rReconf[r].observed, GetScanStart(m, m.logletRef)),
            ![r].observed = {},
            ![r].state = COMMIT_RECONFIG]
    /\ UNCHANGED <<notReconVars, storeVars, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: CommitReconfig

    CAS the manifest using the captured version.
    Success fixes the old loglet's tail and installs a new
    loglet with empty storage, an unset seal, and a sequencer.
    A conflict leaves durable state unchanged. Both outcomes
    return to IDLE; this write does not refresh the cache.
-----------------------------------------------------------*)

CommitReconfig(r) ==
    /\ rReconf[r].state = COMMIT_RECONFIG
    /\ LET m == rReconf[r].base
           oldLRef == m.logletRef
           tail == rReconf[r].tail
           lId == oldLRef.id + 1
           closed == [manifest.loglets EXCEPT ![oldLRef.id].tail = tail]
           lRef == [id    |-> lId, 
                    first |-> GlobalIndex(oldLRef, tail),
                    tail  |-> 0, 
                    seq   |-> r]
           successor == [manifest EXCEPT !.loglets = Append(closed, lRef),
                                         !.version = @ + 1]
       IN IF m.version = manifest.version
          THEN /\ manifest' = successor
               /\ CreateDrive(lId)
               /\ CreateSeal(lId)
               /\ CreateSequencer(r, lId)
          ELSE UNCHANGED <<manifest, entries, sealbits, rSequencer>>
    /\ rReconf' = [rReconf EXCEPT ![r] = EmptyReconf]
    /\ UNCHANGED <<notReconVars, snapshots, rManifest, auxVars>>

=============================================================================
