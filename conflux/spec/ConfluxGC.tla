---------------- MODULE ConfluxGC ----------------

(*
    This module represents the garbage collection task
    (per replica). It creates snapshots and performs
    prefix trims.
    The abstractions of the VirtualLog, AtomicLog and LogDrive 
    are not explicitly modeled as modularized components.
*)

EXTENDS ConfluxCommon

notGcVars == <<rApply, rAppend, rReconf>>

\**********************************************************
\* DATA MODEL and Task Init
\**********************************************************

EmptyGC == [state    |-> IDLE, 
            version  |-> 0, 
            snapshot |-> None]

GCType ==
    [state: {IDLE, COMMIT_TRIM},
     version: Nat,
     snapshot: SnapshotIdType \union {None}]

GCTypeOK == 
    rGC \in [Replicas -> GCType]

(* ---------------------------------------------------------
    ACTION: GCInit

    Initialize every replica with no prefix trim in progress.
-----------------------------------------------------------*)

GCInit == 
    rGC = [r \in Replicas |-> EmptyGC]

\**********************************************************
\* TASK ACTIONS
\**********************************************************

(* ---------------------------------------------------------
    ACTION: GCCrash

    Discard the replica's pending trim publication.
    Already uploaded snapshots and published trims survive.
-----------------------------------------------------------*)

GCCrash(r) == 
    rGC' = [rGC EXCEPT ![r] = EmptyGC]

(* ---------------------------------------------------------
    ACTION: StartPrefixTrim

    If the applied prefix exceeds the cached trim point,
    upload it as a snapshot and capture the cached version.
    Transition to COMMIT_TRIM.
-----------------------------------------------------------*)

StartPrefixTrim(r) ==
    LET appliedData == rApply[r].data
        id == Len(appliedData) 
    IN
        /\ rGC[r].state = IDLE
        /\ rManifest[r] /= None
        /\ Len(appliedData) > rManifest[r].trimIndex
        /\ snapshots' = snapshots @@ (id :> appliedData)
        /\ rGC' = [rGC EXCEPT ![r] =
                        [state    |-> COMMIT_TRIM, 
                         version  |-> rManifest[r].version,
                         snapshot |-> id]]
        /\ UNCHANGED <<notGcVars, manifest, entries, sealbits, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: CommitPrefixTrim

    CAS-write the manifest with the snapshot ref and trim point.
    A conflict leaves the manifest unchanged.
    Once the prefixTrim has executed, a GC task can 
    asynchronously start collecting (deleting) log entry
    objects on S3.
-----------------------------------------------------------*)

CommitPrefixTrim(r) ==
    /\ rGC[r].state = COMMIT_TRIM
    /\ IF rGC[r].version = manifest.version
       THEN manifest' = [manifest EXCEPT !.version = @ + 1,
                                         !.snapshot = rGC[r].snapshot,
                                         !.trimIndex = rGC[r].snapshot]
       ELSE UNCHANGED manifest
    /\ rGC' = [rGC EXCEPT ![r] = EmptyGC]
    /\ UNCHANGED <<notGcVars, entries, sealbits, snapshots, rManifest, rSequencer, auxVars>>

(* ---------------------------------------------------------
    ACTION: CollectEntry

    Delete an existing entry allowed by the cached trim point:
    a trimmed slot, or an entry in a fully trimmed sealed loglet.
    A newer trim is usable only after a manifest refresh.
    A delayed PUT may recreate the object after deletion, but
    Conflux requires no conditional puts for correctness
    anyway and guarantees a given address can only ever be
    written to with a single value (see LogDrive paper).
-----------------------------------------------------------*)

CollectEntry(r, lId, slot) ==
    /\ rManifest[r] /= None
    /\ lId \in DOMAIN rManifest[r].loglets
    /\ LET lRef == CachedLogletRef(r, lId) IN
        /\ EntryCollectable(rManifest[r].trimIndex, lRef, slot)
        /\ ReadEntry(lId, slot) /= U
        /\ DeleteEntry(lId, slot)
        /\ UNCHANGED <<notGcVars, manifest, sealbits, snapshots, rManifest, rSequencer, rGC, auxVars>>

=============================================================================
