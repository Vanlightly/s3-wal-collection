----------------------------- MODULE BufferAsWAL -------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,           \* The set of writer processes
          GarbageCollectors, \* The set of garbage collector processes
          Values             \* The set of values to append

\* writer/gc states
CONSTANTS IDLE, SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, READY,
          CLAIM_MANIFEST, APPEND_TO_MANIFEST, COMMIT_SNAPSHOT, 
          PREEMPTED, DELETE

CONSTANTS NIL

WritableSeqNos == 1..Cardinality(Values)
NextSeqNos == 1..Cardinality(Values) + 1
MaxOrDef(set, def) == IF set = {} THEN def ELSE Max(set)
MinOrDef(set, def) == IF set = {} THEN def ELSE Min(set)

VARIABLES batch,            \* The batch objects in S3 (one value per object in this spec)
          manifest,         \* The manifest file in S3
          snapshot,         \* Snapshot files in S3
          wState,           \* Writer -> state
          wPendingBatch,    \* Writer -> pending commit batch id
          wManifest,        \* Writer -> local copy of the manifest
          wNextSeq,         \* Writer -> the next seqno to write
          wMachineData,     \* Writer -> state machine data (a sequence of Values)
          wSnapshottedSeq,  \* Writer -> the set of snapshot seq nos it has written
          gcState,          \* GC -> state
          gcManifest        \* GC -> local copy of the manifest

\* Auxilliary variables for invariants
VARIABLES auxUsedValues, 
          auxWrittenValues,
          auxTsId

writerVars == <<wState, wPendingBatch, wManifest, wNextSeq, 
                wMachineData, wSnapshottedSeq>>
storeVars == <<batch, manifest, snapshot>>
gcVars == <<gcState, gcManifest>>
auxVars == <<auxUsedValues, auxWrittenValues, auxTsId>>
vars == <<storeVars, writerVars, gcVars, auxVars>>

Symmetry ==
    Permutations(Writers)
        \union Permutations(GarbageCollectors)
        \union Permutations(Values)

Read(id) == IF id \in DOMAIN batch 
            THEN batch[id] ELSE NIL
Snapshot(id) == snapshot[id]

\***********************************************************************
\* ACTIONS
\***********************************************************************

Initialize(w) ==
    /\ wState[w] = IDLE
    /\ wManifest' = [wManifest EXCEPT ![w] = manifest]
    /\ wState' = [wState EXCEPT ![w] = CLAIM_MANIFEST]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wNextSeq, wPendingBatch, 
                   wMachineData, wSnapshottedSeq>>

ClaimManifest(w) ==
    /\ wState[w] = CLAIM_MANIFEST
    /\ \/ /\ manifest.version > wManifest[w].version
          /\ wState' = [wState EXCEPT ![w] = IDLE] 
          /\ UNCHANGED <<manifest, wManifest>>
       \/ /\ manifest.version = wManifest[w].version
          /\ LET newManifest == [wManifest[w] EXCEPT !.version = @ + 1]
             IN /\ manifest' = newManifest
                /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
                /\ wState' = [wState EXCEPT ![w] = SNAPSHOT_RECOVERY]
    /\ UNCHANGED <<gcVars, auxVars, batch, snapshot, wPendingBatch,
                   wNextSeq, wMachineData, wSnapshottedSeq>>

SnapshotRecovery(w) ==
    /\ wState[w] = SNAPSHOT_RECOVERY
    /\ LET seq  == wManifest[w].snapshotSeq
           snap == snapshot[seq]
       IN IF seq > 0 /\ seq \notin DOMAIN snapshot THEN
             /\ wState' = [wState EXCEPT ![w] = IDLE]
             /\ UNCHANGED <<wMachineData, wNextSeq>> 
          ELSE
             /\ wMachineData' = [wMachineData EXCEPT ![w] =
                                   IF seq = 0 THEN <<>> ELSE snap]
             /\ wNextSeq' = [wNextSeq EXCEPT ![w] = seq + 1]
             /\ wState' = [wState EXCEPT ![w] = CATCHUP_RECOVERY]
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wManifest, wPendingBatch, 
                   wSnapshottedSeq>>

CatchupRecovery(w) ==
    /\ wState[w] = CATCHUP_RECOVERY
    /\ \/ /\ wNextSeq[w] > MaxOrDef(DOMAIN wManifest[w].entries, 0)
          /\ wState' = [wState EXCEPT ![w] = READY]
          /\ UNCHANGED <<wMachineData, wNextSeq>>
       \/ \E seq \in DOMAIN wManifest[w].entries :
            /\ seq = wNextSeq[w]
            /\ LET id == wManifest[w].entries[seq]
                   read  == Read(id)
               IN
                    \/ /\ read = NIL
                       /\ wState' = [wState EXCEPT ![w] = IDLE]
                       /\ UNCHANGED <<wMachineData, wNextSeq>>
                    \/ /\ read /= NIL
                       /\ wMachineData' = [wMachineData EXCEPT ![w] = Append(@, read)]
                       /\ wNextSeq' = [wNextSeq EXCEPT ![w] = @ + 1]
                       /\ UNCHANGED wState
    /\ UNCHANGED <<storeVars, gcVars, auxVars, wManifest, wPendingBatch,
                   wSnapshottedSeq>>

WriteBatch(w, v) ==
    /\ wState[w] = READY
    /\ v \notin auxUsedValues
    /\ batch' = batch @@ (auxTsId :> v)
    /\ wState' = [wState EXCEPT ![w] = APPEND_TO_MANIFEST]
    /\ wPendingBatch' = [wPendingBatch EXCEPT ![w] = [id   |-> auxTsId,
                                                      data |-> v]]
    /\ auxUsedValues' = auxUsedValues \union {v}
    /\ auxTsId' = auxTsId + 1
    /\ UNCHANGED <<gcVars, manifest, snapshot, wManifest, wNextSeq, 
                   wMachineData, wSnapshottedSeq, auxWrittenValues>>

MinTs(entries) ==
    MinOrDef({entries[e] : e \in DOMAIN entries}, 0)

AppendToManifest(w) ==
    /\ wState[w] = APPEND_TO_MANIFEST
    /\ LET newEntries  == wManifest[w].entries @@ 
                            (wNextSeq[w] :> wPendingBatch[w].id)
           currVersion == wManifest[w].version
           newManifest == [wManifest[w] EXCEPT !.entries = newEntries,
                                               !.tsFloor = MinTs(newEntries),
                                               !.version = @ + 1]
       IN \/ /\ manifest.version /= currVersion
             /\ wState' = [wState EXCEPT ![w] = PREEMPTED]
             /\ UNCHANGED <<storeVars, auxVars, wManifest, wPendingBatch,
                            wMachineData, wNextSeq, wSnapshottedSeq, auxWrittenValues>>
          \/ /\ manifest.version = currVersion 
             /\ manifest' = newManifest
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = READY]
             /\ wNextSeq' = [wNextSeq EXCEPT ![w] = @ + 1]
             /\ wPendingBatch' = [wPendingBatch EXCEPT ![w] = NIL]
             /\ wMachineData' = [wMachineData EXCEPT ![w] = Append(@, wPendingBatch[w].data)]
             /\ auxWrittenValues' = Append(auxWrittenValues, wPendingBatch[w].data)
    /\ UNCHANGED <<gcVars, auxUsedValues, auxTsId, batch, snapshot,
                   wSnapshottedSeq>>

WriteSnapshot(w) ==
    /\ wState[w] = READY
    /\ wNextSeq[w] > 1 \* at one, it means that the writer has written nothing
    /\ LET seq == wNextSeq[w] - 1 IN
        /\ seq \notin DOMAIN snapshot
        /\ seq \notin wSnapshottedSeq[w]
        /\ snapshot' = snapshot @@ (seq :> wMachineData[w])
        /\ wState' = [wState EXCEPT ![w] = COMMIT_SNAPSHOT]
        /\ wSnapshottedSeq' = [wSnapshottedSeq EXCEPT ![w] = @ \union {seq}]
    /\ UNCHANGED <<gcVars, auxVars, batch, manifest, wManifest, wNextSeq, 
                   wPendingBatch, wMachineData>>

PrefixTrimmedEntries(w) ==
     LET seqNos == { seq \in DOMAIN wManifest[w].entries : seq >= wNextSeq[w] }
     IN [seq \in seqNos |-> wManifest[w].entries[seq]]

MaxTs(entries) ==
    MaxOrDef({entries[e] : e \in DOMAIN entries}, 0)

TsFloorAfterTrim(w, newEntries) ==
    IF Cardinality(DOMAIN newEntries) = 0
    THEN MaxTs(wManifest[w].entries)
    ELSE MinTs(newEntries)

CommitSnapshot(w) ==
    /\ wState[w] = COMMIT_SNAPSHOT
    /\ LET newEntries  == PrefixTrimmedEntries(w)
           currVersion == wManifest[w].version
           newManifest == [wManifest[w] EXCEPT !.snapshotSeq = wNextSeq[w] - 1,
                                               !.entries = newEntries,
                                               !.tsFloor = TsFloorAfterTrim(w, newEntries),
                                               !.version = @ + 1]
       IN \/ /\ manifest.version > currVersion
             /\ wState' = [wState EXCEPT ![w] = PREEMPTED]
             /\ UNCHANGED <<manifest, wManifest>>
          \/ /\ manifest.version = currVersion
             /\ manifest' = newManifest
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = READY]
    /\ UNCHANGED <<gcVars, auxVars, batch, snapshot, wNextSeq,
                   wMachineData, wPendingBatch, wSnapshottedSeq>>

GcStart(gc) ==
    /\ \/ gcState[gc] = IDLE
       \* or we're deleting artifacts and there's nothing left to delete
       \/ /\ gcState[gc] = DELETE
          /\ ~\E id \in DOMAIN batch : id < gcManifest[gc].tsFloor
          /\ ~\E id \in DOMAIN snapshot : id < gcManifest[gc].snapshotSeq
    /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ gcManifest' = [gcManifest EXCEPT ![gc] = manifest]
    /\ UNCHANGED <<storeVars, writerVars, auxVars>>

DeleteBatch(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN batch :
        /\ id < gcManifest[gc].tsFloor
        /\ batch' = [i \in (DOMAIN batch \ {id}) |-> batch[i]]
    /\ UNCHANGED <<manifest, snapshot, writerVars, gcVars, auxVars>>

DeleteSnapshot(gc) ==
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN snapshot :
        /\ id < gcManifest[gc].snapshotSeq
        /\ snapshot' = [i \in (DOMAIN snapshot \ {id}) |-> snapshot[i]]
        /\ UNCHANGED <<batch, manifest, writerVars, gcVars, auxVars>>

\***********************************************************************
\* TYPE correctness
\***********************************************************************

ManifestOK(m) ==
    /\ \A seq \in DOMAIN m.entries : 
        /\ seq \in WritableSeqNos
        /\ m.entries[seq] \in Nat
    /\ m.snapshotSeq \in WritableSeqNos \union {0}
    /\ m.tsFloor \in Nat
    /\ m.version \in Nat
    
LocalManifestOK(lManifest) ==
    \/ lManifest = NIL
    \/ ManifestOK(lManifest)
    
PendingBatchType ==
    [id: Nat, data: Values]    
    
TypeOK ==
    /\ \A id \in DOMAIN batch :
        /\ id \in Nat
        /\ batch[id] \in Values
    /\ ManifestOK(manifest)
    /\ \A seq \in DOMAIN snapshot :
        /\ seq \in WritableSeqNos
        /\ snapshot[seq] \in Seq(Values)
    /\ wState \in [Writers -> 
            {IDLE, CLAIM_MANIFEST, SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, 
             READY, APPEND_TO_MANIFEST, COMMIT_SNAPSHOT, PREEMPTED}]
    /\ \A w \in Writers : LocalManifestOK(wManifest[w])
    /\ wNextSeq \in [Writers -> NextSeqNos]
    /\ wPendingBatch \in [Writers -> PendingBatchType \union {NIL}]
    /\ wMachineData \in [Writers -> Seq(Values)]
    /\ wSnapshottedSeq \in [Writers -> SUBSET WritableSeqNos]
    /\ gcState \in [GarbageCollectors -> {IDLE, DELETE}]
    /\ \A gc \in GarbageCollectors : LocalManifestOK(gcManifest[gc])                
    /\ auxUsedValues \in SUBSET Values
    /\ auxWrittenValues \in Seq(Values)
    /\ auxTsId \in Nat
    \* Local manifest version cannot jump ahead of stored manifest
    /\ \A w \in Writers :
        wManifest[w] /= NIL =>
            wManifest[w].version <= manifest.version
    /\ \A gc \in GarbageCollectors :
        gcManifest[gc] /= NIL =>
            gcManifest[gc].version <= manifest.version

\***********************************************************************
\* INVARIANTS
\***********************************************************************

\* INV: ValidWriters
\* There must be at least one functional writer
ValidWriters ==
    \E w \in Writers : wState[w] /= PREEMPTED

\* INV: ConsistentMachineData
\* The state machine data of each READY writer matches the
\* history of successful writes.
\* If the writer is stale, it matches a prefix of write history.
\* If the writer is current, it perfectly matches the write history.
SeqPrefixOf(s1, s2) ==
    /\ Len(s1) <= Len(s2)
    /\ \A pos \in DOMAIN s1 :
            s1[pos] = s2[pos]

ConsistentMachineData ==
    \A w \in Writers :
        wState[w] = READY =>
            IF wManifest[w].version < manifest.version
            THEN SeqPrefixOf(wMachineData[w], auxWrittenValues)
            ELSE wMachineData[w] = auxWrittenValues

\* INV: ManifestRepresentsCommittedLog
\* Central WAL safety property: every committed value remains reconstructible,
\* in order, from the snapshot plus manifest entries.
ManifestRepresentsCommittedLog ==
    \* The snapshot seq corresponds to a seq in the write history
    /\ manifest.snapshotSeq <= Len(auxWrittenValues)
    \* The manifest entries correspond to the write history above the snapshot seq
    /\ DOMAIN manifest.entries =
            (manifest.snapshotSeq + 1)..Len(auxWrittenValues)
    \* Each manifest entry has a corresponding batch in storage
    \* And the value stored in each such batch exists in the write history 
    /\ \A seq \in DOMAIN manifest.entries :
        LET id == manifest.entries[seq]
        IN  /\ id \in DOMAIN batch
            /\ batch[id] = auxWrittenValues[seq]
    \* The stored snapshot at `seq` is the prefix of the write history up to `seq`
    /\ \/ manifest.snapshotSeq = 0
       \/ /\ manifest.snapshotSeq \in DOMAIN snapshot
          /\ snapshot[manifest.snapshotSeq] =
                SubSeq(auxWrittenValues, 1, manifest.snapshotSeq)

\* INV: StoredSnapshotsAreValid
\* Every stored snapshot is a prefix (of the write history)
StoredSnapshotsAreValid ==
    \A seq \in DOMAIN snapshot :
        /\ seq <= Len(auxWrittenValues)
        /\ snapshot[seq] = SubSeq(auxWrittenValues, 1, seq)

\* INV: SingleAuthoritativeWriter
\* There can be only one writer with the authoritative
\* manifest version number.
Authoritative(w) ==
    /\ wState[w] \in {SNAPSHOT_RECOVERY, CATCHUP_RECOVERY, READY,
                      APPEND_TO_MANIFEST, COMMIT_SNAPSHOT}
    /\ wManifest[w] /= NIL
    /\ wManifest[w].version = manifest.version

SingleAuthoritativeWriter ==
    Quantify(Writers, LAMBDA w : Authoritative(w)) <= 1

\***********************************************************************
\* LIVENESS
\***********************************************************************

AllValuesAttempted ==
    <>[](auxUsedValues = Values)

\* There are only two terminal states:
\* - READY: when there are no more values to append
\* - PREEMPTED: when another writer preempts this one
\* Writers keep restarting (reverting to IDLE) when encountering
\* conflicts during initialization, but go to PREEMPTED once established.
WritersReachReadyOrPreempted ==
    \A w \in Writers :
        <>[](wState[w] \in {READY, PREEMPTED})

\***********************************************************************
\* INIT, NEXT and SPEC
\***********************************************************************

Init ==
    /\ batch = <<>>
    /\ snapshot = <<>>
    /\ manifest = [entries     |-> <<>>, 
                   snapshotSeq |-> 0, 
                   tsFloor     |-> 0,
                   version     |-> 0]
    /\ wState = [w \in Writers |-> IDLE]
    /\ wPendingBatch = [w \in Writers |-> NIL]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ wNextSeq = [w \in Writers |-> 1]
    /\ wMachineData = [w \in Writers |-> <<>>]
    /\ wSnapshottedSeq = [w \in Writers |-> {}]
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ gcManifest = [gc \in GarbageCollectors |-> NIL]
    /\ auxUsedValues = {}
    /\ auxWrittenValues = <<>>
    /\ auxTsId = 1

Next ==
    \/ \E w \in Writers :
        \/ Initialize(w)
        \/ ClaimManifest(w)
        \/ SnapshotRecovery(w)
        \/ CatchupRecovery(w)
        \/ \E v \in Values : WriteBatch(w, v)
        \/ AppendToManifest(w)
        \/ WriteSnapshot(w)
        \/ CommitSnapshot(w)
    \/ \E gc \in GarbageCollectors :
        \/ GcStart(gc)
        \/ DeleteBatch(gc)
        \/ DeleteSnapshot(gc)

Fairness ==
    /\ \A w \in Writers :
        /\ WF_vars(Initialize(w))
        /\ WF_vars(ClaimManifest(w))
        /\ WF_vars(SnapshotRecovery(w))
        /\ WF_vars(CatchupRecovery(w))
        /\ \A v \in Values : WF_vars(WriteBatch(w, v))
        /\ WF_vars(AppendToManifest(w))
        /\ WF_vars(WriteSnapshot(w))
        /\ WF_vars(CommitSnapshot(w))
    /\ \A gc \in GarbageCollectors :
        /\ WF_vars(GcStart(gc))
        /\ WF_vars(DeleteBatch(gc))
        /\ WF_vars(DeleteSnapshot(gc))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
