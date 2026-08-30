----------------------------- MODULE Oswald -----------------------------
\* A state-machine specification of OSWALD (Object Storage Write-Ahead Log
\* Device), based on the P model at github.com/nvartolomei/oswald.
\*
\* The modeled application is the P model's replicated increment-only counter.
\* Object-store requests are atomic and linearizable here.  Client-side calls
\* that must be separated by a concurrency boundary (notably PUT chunk followed
\* by GET manifest) remain separate actions.

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS Writers,
          GarbageCollectors,
          Values

CONSTANTS SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, 
          VALIDATE, UPDATE_MANIFEST, READY, DELETE

CONSTANTS NIL

\*ASSUME MaxLsn \in Nat
\*
WritableLsns == 0..Cardinality(Values)

VARIABLES manifest,
          chunk,
          snapshot,
          wState,
          wManifestVersion,
          wSafeLsn,
          wNextLsn,
          wSnapshot,
          wSnapshottedLsns,
          wPendingApply,
          gcState,
          gcWm,
          auxUsedValues

storeVars == <<manifest, chunk, snapshot>>
writerVars == <<wState, wManifestVersion, wSafeLsn, wNextLsn, 
                wSnapshot, wSnapshottedLsns, wPendingApply>>
gcVars == <<gcState, gcWm>>
auxVars == <<auxUsedValues>>
vars == <<storeVars, writerVars, gcVars, auxVars>>

SnapshotRecovery(w) ==
    /\ wState[w] = SNAPSHOT_RECOVERY
    /\ wManifestVersion' = [wManifestVersion EXCEPT ![w] = manifest.version]
    /\ wSafeLsn' = [wSafeLsn EXCEPT ![w] = manifest.snapshotLsn]
    /\ wNextLsn' = [wNextLsn EXCEPT ![w] = manifest.snapshotLsn + 1]
    /\ wSnapshot' = [wSnapshot EXCEPT ![w] = IF manifest.snapshotLsn \notin DOMAIN snapshot
                                             THEN <<>>
                                             ELSE snapshot[manifest.snapshotLsn]]
    /\ wState' = [wState EXCEPT ![w] = CATCHUP_RECOVERY]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wSnapshottedLsns, wPendingApply>>

CatchupRecovery(w) ==
    /\ wState[w] = CATCHUP_RECOVERY
    /\ LET read == IF wNextLsn[w] \in DOMAIN chunk
                   THEN chunk[wNextLsn[w]]ELSE NIL
       IN \/ /\ read /= NIL
             /\ wSnapshot' = [wSnapshot EXCEPT ![w] = read]
             /\ wNextLsn' = [wNextLsn EXCEPT ![w] = @ + 1]
             /\ UNCHANGED <<wState, wManifestVersion>>
          \/ /\ read = NIL
             /\ wState' = [wState EXCEPT ![w] = VALIDATE]
             /\ UNCHANGED <<wSnapshot, wNextLsn, wManifestVersion>>
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wSafeLsn, wSnapshottedLsns, wPendingApply>>

Validate(w) ==
    /\ wState[w] = VALIDATE
    /\ IF /\ wManifestVersion[w] /= manifest.version
          /\ wSafeLsn[w] <= manifest.gcWatermark
       THEN /\ wState' = [wState EXCEPT ![w] = SNAPSHOT_RECOVERY]
            /\ UNCHANGED wSafeLsn
       ELSE /\ wState' = [wState EXCEPT ![w] = READY]
            /\ wSafeLsn' = [wSafeLsn EXCEPT ![w] = wNextLsn[w]]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wSnapshot, wNextLsn, 
                   wManifestVersion, wSnapshottedLsns, wPendingApply>>

AppendChunk(w, v) ==
    LET newSnap == Append(wSnapshot[w], v) 
    IN
        /\ wState[w] = READY
        /\ wPendingApply[w] = NIL
        /\ v \notin auxUsedValues
        /\ \/ /\ wNextLsn[w] \notin DOMAIN chunk
              /\ chunk' = chunk @@ (wNextLsn[w] :> newSnap)
              /\ wNextLsn' = [wNextLsn EXCEPT ![w] = @ + 1]
              /\ wPendingApply' = [wPendingApply EXCEPT ![w] = newSnap]
              /\ wState' = [wState EXCEPT ![w] = VALIDATE]
              /\ auxUsedValues' = auxUsedValues \union {v}
           \/ /\ wNextLsn[w] \in DOMAIN chunk
              /\ wState' = [wState EXCEPT ![w] = CATCHUP_RECOVERY]
              /\ UNCHANGED <<chunk, wSnapshot, wNextLsn, wPendingApply, auxUsedValues>>
        /\ UNCHANGED <<manifest, snapshot, wSnapshot, wManifestVersion, 
                       wSafeLsn, wSnapshottedLsns, gcVars>>

ApplyChunk(w) ==
    /\ wState[w] = READY
    /\ wPendingApply[w] /= NIL
    /\ wSnapshot' = [wSnapshot EXCEPT ![w] = wPendingApply[w]]
    /\ wPendingApply' = [wPendingApply EXCEPT ![w] = NIL]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wState, wManifestVersion, wSafeLsn, 
                   wNextLsn, wSnapshottedLsns>>
    

WriteSnapshot(w) ==
    /\ wState[w] = READY
    /\ wPendingApply[w] = NIL
    /\ wNextLsn[w] > 1 \* at one, it means that the writer has read/written nothing
    /\ LET lsn == wNextLsn[w] - 1 IN
        /\ lsn \notin DOMAIN snapshot
        /\ lsn \notin wSnapshottedLsns[w] 
        /\ snapshot' = snapshot @@ (lsn :> wSnapshot[w])
        /\ wState' = [wState EXCEPT ![w] = UPDATE_MANIFEST]
        /\ wSnapshottedLsns' = [wSnapshottedLsns EXCEPT ![w] = @ \union {lsn}]
    /\ UNCHANGED <<chunk, manifest, wManifestVersion, wSafeLsn, 
                   wNextLsn, wSnapshot, wPendingApply, gcVars, auxVars>>

UpdateManifest(w) ==
    /\ wState[w] = UPDATE_MANIFEST
    /\ wManifestVersion[w] = manifest.version
    /\ LET lsn == wNextLsn[w] - 1
           newVersion == wManifestVersion[w] + 1
       IN
        /\ manifest' = [manifest EXCEPT !.snapshotLsn = lsn,
                                        !.version = newVersion]
        /\ wState' = [wState EXCEPT ![w] = READY]
        /\ wManifestVersion' = [wManifestVersion EXCEPT ![w] = newVersion]
        /\ UNCHANGED <<snapshot, chunk, wSafeLsn, wNextLsn, 
                       wSnapshot, wSnapshottedLsns, wPendingApply,
                       gcVars, auxVars>>

AdvanceGcWatermark(gc) ==
    /\ \/ gcState[gc] = READY
       \/ /\ gcState[gc] = DELETE
          /\ ~\E lsn \in DOMAIN chunk : lsn <= gcWm[gc]
          /\ ~\E lsn \in DOMAIN snapshot : lsn <= gcWm[gc]
    /\ manifest.snapshotLsn /= manifest.gcWatermark
    /\ manifest' = [manifest EXCEPT !.gcWatermark = manifest.snapshotLsn,
                                    !.version = @ + 1]
    /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ gcWm' = [gcWm EXCEPT ![gc] = manifest.snapshotLsn]
    /\ UNCHANGED <<chunk, snapshot, writerVars, auxVars>>

DeleteChunk(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E lsn \in DOMAIN chunk :
        /\ lsn <= gcWm[gc]
        /\ chunk' = [l \in (DOMAIN chunk \ {lsn}) |-> chunk[l]]
        /\ UNCHANGED <<manifest, snapshot, writerVars, gcVars, auxVars>>

DeleteSnapshot(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E lsn \in DOMAIN snapshot :
        /\ lsn < gcWm[gc]
        /\ snapshot' = [l \in (DOMAIN snapshot \ {lsn}) |-> snapshot[l]]
        /\ UNCHANGED <<chunk, manifest, writerVars, gcVars, auxVars>>

TypeOK ==
    /\ manifest \in [snapshotLsn: Nat, gcWatermark: Nat, version: Nat]
    /\ \A lsn \in DOMAIN chunk :
        /\ lsn \in WritableLsns
        /\ chunk[lsn] \in Seq(Values)
    /\ \A lsn \in DOMAIN snapshot :
        /\ lsn \in WritableLsns
        /\ snapshot[lsn] \in Seq(Values)
    /\ wState \in [Writers -> {SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, VALIDATE,
                               READY, UPDATE_MANIFEST}]
    /\ wManifestVersion \in [Writers -> Nat]
    /\ wSafeLsn \in [Writers -> Nat]
    /\ wNextLsn \in [Writers -> Nat]
    /\ wSnapshot \in [Writers -> Seq(Values)]
    /\ wSnapshottedLsns \in [Writers -> SUBSET WritableLsns]
    /\ gcState \in [GarbageCollectors -> {READY, DELETE}]
    /\ gcWm \in [GarbageCollectors -> Nat]
    /\ auxUsedValues \in SUBSET Values

ConsistentLog ==
    \A lsn \in WritableLsns :
        \A w1, w2 \in Writers :
            (/\ wState[w1] = READY
             /\ wState[w2] = READY
             /\ wPendingApply[w1] = NIL
             /\ wPendingApply[w2] = NIL
             /\ lsn \in DOMAIN wSnapshot[w1] 
             /\ lsn \in DOMAIN wSnapshot[w2])
                => wSnapshot[w1][lsn] = wSnapshot[w2][lsn] 

Test ==
    TLCGet("level") < 100

Init ==
    /\ manifest = [snapshotLsn |-> 0, gcWatermark |-> 0, version |-> 0]
    /\ chunk = <<>>
    /\ snapshot = <<>>
    /\ wState = [w \in Writers |-> SNAPSHOT_RECOVERY]
    /\ wManifestVersion = [w \in Writers |-> 0]
    /\ wSafeLsn= [w \in Writers |-> 0]
    /\ wNextLsn = [w \in Writers |-> 1]
    /\ wSnapshot = [w \in Writers |-> <<>>]
    /\ wSnapshottedLsns = [w \in Writers |-> {}]
    /\ wPendingApply = [w \in Writers |-> NIL]
    /\ gcState = [gc \in GarbageCollectors |-> READY]
    /\ gcWm = [gc \in GarbageCollectors |-> 0]
    /\ auxUsedValues = {}

Next ==
    \/ \E w \in Writers :
        \/ SnapshotRecovery(w)
        \/ CatchupRecovery(w)
        \/ Validate(w)
        \/ \E v \in Values : AppendChunk(w, v)
        \/ ApplyChunk(w)
        \/ WriteSnapshot(w)
        \/ UpdateManifest(w)
    \/ \E gc \in GarbageCollectors :
        \/ AdvanceGcWatermark(gc)
        \/ DeleteChunk(gc)
        \/ DeleteSnapshot(gc)

Spec == Init /\ [][Next]_vars
=============================================================================|