----------------------------- MODULE Buffer -------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,  \* The set of writer processes
          Readers,  \* The set of reader processes
          GarbageCollectors, \* The set of garbage collector processes
          Values,   \* The set of values to append
          EnableGC  \* Whether GC is enabled or not

\* Reader/writer/GC states
CONSTANTS IDLE, READ_MANIFEST, APPEND_TO_MANIFEST, 
          CLAIM_MANIFEST, CLAIM_CURSOR, READ_ENTRY, START_ACK,  
          COMMIT, PREFIX_TRIM, PREEMPTED, INVALID_STATE, DELETE

CONSTANTS NIL

WritableBatchIds == 1..Cardinality(Values)
WritableSeqNos == 1..Cardinality(Values)
NextSeqNos == 1..Cardinality(Values) + 1
MaxOrDef(set, def) == IF set = {} THEN def ELSE Max(set)
MinOrDef(set, def) == IF set = {} THEN def ELSE Min(set)

VARIABLES batch,            \* The batch objects written to S3 (one value per object in this spec)
          manifest,         \* The manifest file in S3
          cursor,           \* The reader cursor in S3
          wState,           \* Writer -> state
          wPendingBatch,    \* Writer -> pending commit batch id
          wManifest,        \* Writer -> local copy of the manifest
          rState,           \* Reader -> state
          rCursor,          \* Reader -> local copy of the cursor
          rManifest,        \* Reader -> local copy of the manifest
          gcState,          \* GC -> state
          gcManifest        \* GC -> local copy of the manifest

\* Auxilliary variables for invariants
VARIABLES auxUsedValues,    \* The set of proposed values
          auxWrittenValues, \* The sequence of successful writes (of values)
          auxReadValues,    \* The sequence of successful reads (of values)
          auxTsId           \* The equivalent of a ULID for batch ids

writerVars == <<wState, wPendingBatch, wManifest>>
readerVars == <<rState, rCursor, rManifest>>
storeVars == <<batch, manifest, cursor>>
gcVars == <<gcState, gcManifest>>
auxVars == <<auxUsedValues, auxReadValues, auxWrittenValues, auxTsId>>
vars == <<storeVars, writerVars, readerVars, gcVars, auxVars>>

Symmetry ==
    Permutations(Writers)
        \union Permutations(Readers)
        \union Permutations(GarbageCollectors)
        \union Permutations(Values)

Read(id) == batch[id]

\***********************************************************************
\* ACTIONS
\***********************************************************************

(* WRITER ACTIONS --------------------------------------*)

WriteBatch(w, v) ==
    /\ wState[w] = IDLE
    /\ v \notin auxUsedValues
    /\ batch' = batch @@ (auxTsId :> v)
    /\ wState' = [wState EXCEPT ![w] = READ_MANIFEST]
    /\ wPendingBatch' = [wPendingBatch EXCEPT ![w] = [id   |-> auxTsId,
                                                      data |-> v]]
    /\ auxUsedValues' = auxUsedValues \union {v}
    /\ auxTsId' = auxTsId + 1
    /\ UNCHANGED <<readerVars, gcVars, manifest, cursor, wManifest,
                   auxReadValues, auxWrittenValues>>

ReadManifest(w) ==
    /\ wState[w] = READ_MANIFEST
    /\ wManifest' = [wManifest EXCEPT ![w] = manifest]
    /\ wState' = [wState EXCEPT ![w] = APPEND_TO_MANIFEST]
    /\ UNCHANGED <<storeVars, readerVars, gcVars, auxVars, wPendingBatch>>

MinTs(entries) ==
    MinOrDef({entries[e] : e \in DOMAIN entries}, 0)

AppendToManifest(w) ==
    /\ wState[w] = APPEND_TO_MANIFEST
    /\ LET newEntries  == wManifest[w].entries @@ 
                            (wManifest[w].nextSeq :> wPendingBatch[w].id)
           currVersion == wManifest[w].version 
           newVersion  == wManifest[w].version + 1
           newManifest == [wManifest[w] EXCEPT !.entries = newEntries,
                                               !.nextSeq = @ + 1,
                                               !.tsFloor = MinTs(newEntries),
                                               !.version = newVersion]
       IN \/ /\ manifest.version = currVersion
             /\ manifest' = newManifest
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = IDLE]
             /\ wPendingBatch' = [wPendingBatch EXCEPT ![w] = NIL]
             /\ auxWrittenValues' = Append(auxWrittenValues, wPendingBatch[w].data)
          \/ /\ manifest.version /= currVersion
             /\ wState' = [wState EXCEPT ![w] = READ_MANIFEST]
             /\ UNCHANGED <<manifest, wManifest, wPendingBatch, auxWrittenValues>>
    /\ UNCHANGED <<readerVars, gcVars, batch, cursor, auxUsedValues, auxTsId, auxReadValues>>

(* READER ACTIONS --------------------------------------*)

ReaderInitialize(r) ==
    /\ rState[r] = IDLE
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rCursor' = [rCursor EXCEPT ![r] = cursor]
    /\ rState' = [rState EXCEPT ![r] = CLAIM_MANIFEST]
    /\ UNCHANGED <<storeVars, gcVars, writerVars, auxVars>>

ClaimManifest(r) ==
    /\ rState[r] = CLAIM_MANIFEST
    /\ \/ /\ manifest.version > rManifest[r].version
          /\ rState' = [rState EXCEPT ![r] = IDLE] 
          /\ UNCHANGED <<manifest, rManifest>>
       \/ /\ manifest.version = rManifest[r].version
          /\ LET newManifest == [rManifest[r] EXCEPT !.epoch = @ + 1,
                                                     !.version = @ + 1]
             IN /\ manifest' = newManifest
                /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
                /\ rState' = [rState EXCEPT ![r] = CLAIM_CURSOR]
    /\ UNCHANGED <<writerVars, gcVars, auxVars, batch, cursor, rCursor>>

ClaimCursor(r) ==
    /\ rState[r] = CLAIM_CURSOR
    /\ \/ /\ rCursor[r].version /= cursor.version
          /\ rState' = [rState EXCEPT ![r] = IDLE]
          /\ UNCHANGED <<cursor, rCursor>>
       \/ /\ rCursor[r].version = cursor.version
          /\ LET newCursor == [cursor EXCEPT !.version = @ + 1]
             IN 
                /\ cursor' = newCursor
                /\ rCursor' = [rCursor EXCEPT ![r] = newCursor]
                /\ rState' = [rState EXCEPT ![r] = READ_ENTRY]
    /\ UNCHANGED <<writerVars, gcVars, auxVars, manifest, batch, rManifest>>

InvalidCursor(r) ==
    \/ /\ Cardinality(DOMAIN rManifest[r].entries) = 0
       /\ rCursor[r].nextSeq < rManifest[r].nextSeq
    \/ /\ Cardinality(DOMAIN rManifest[r].entries) > 0
       /\ rCursor[r].nextSeq < Min(DOMAIN rManifest[r].entries)

ReadEntry(r, id) ==
    /\ rState[r] = READ_ENTRY
    /\ IF InvalidCursor(r) THEN
            /\ rState' = [rState EXCEPT ![r] = INVALID_STATE]
            /\ UNCHANGED <<auxReadValues, rCursor>>
       ELSE
            \E seq \in DOMAIN rManifest[r].entries :
                /\ seq = rCursor[r].nextSeq
                /\ id = rManifest[r].entries[seq]
                /\ auxReadValues' = Append(auxReadValues, Read(id))
                /\ rCursor' = [rCursor EXCEPT ![r].nextSeq = @ + 1]
                /\ UNCHANGED rState
    /\ UNCHANGED <<storeVars, writerVars, gcVars, auxTsId, auxUsedValues,
                   auxWrittenValues, rManifest>>

AckNeeded(r) ==
    \E seq \in DOMAIN manifest.entries :
        seq < rCursor[r].nextSeq

AckPersistCursor(r) ==
    /\ rState[r] = READ_ENTRY
    /\ AckNeeded(r)
    /\ \/ /\ rCursor[r].version /= cursor.version
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED]
          /\ UNCHANGED <<cursor, rCursor>>
       \/ /\ rCursor[r].version = cursor.version
          /\ rState' = [rState EXCEPT ![r] = START_ACK]
          /\ LET newCursor == [rCursor[r] EXCEPT !.version = @ + 1]
             IN /\ cursor' = newCursor
                /\ rCursor' = [rCursor EXCEPT ![r] = newCursor]
    /\ UNCHANGED <<writerVars, gcVars, auxVars, batch, manifest, rManifest>>

AckReadManifest(r) ==
    /\ rState[r] = START_ACK
    /\ \/ /\ manifest.epoch > rManifest[r].epoch
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED]
          /\ UNCHANGED rManifest
       \/ /\ manifest.epoch = rManifest[r].epoch
          /\ rState' = [rState EXCEPT ![r] = PREFIX_TRIM]
          /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ UNCHANGED <<storeVars, writerVars, gcVars, auxVars, rCursor>>


PrefixTrimmedEntries(r) ==
     LET seqNos == { seq \in DOMAIN rManifest[r].entries : seq >= rCursor[r].nextSeq }
     IN [seq \in seqNos |-> rManifest[r].entries[seq]]

MaxTs(entries) ==
    MaxOrDef({entries[e] : e \in DOMAIN entries}, 0)

TsFloorAfterTrim(r, newEntries) ==
    IF Cardinality(DOMAIN newEntries) = 0
    THEN MaxTs(rManifest[r].entries)
    ELSE MinTs(newEntries)

AckPrefixTrim(r) ==
    /\ rState[r] = PREFIX_TRIM
    /\ LET newEntries == PrefixTrimmedEntries(r) 
           newFloor   == TsFloorAfterTrim(r, newEntries)
       IN /\ rManifest' = [rManifest EXCEPT ![r].entries = newEntries,
                                            ![r].tsFloor = newFloor]
          /\ rState' = [rState EXCEPT ![r] = COMMIT]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, gcVars, rCursor>>

AckCommit(r) ==
    /\ rState[r] = COMMIT
    /\ LET newManifest == [rManifest[r] EXCEPT !.version = @ + 1]
           ackSeq      == rCursor[r].nextSeq - 1
       IN
            \/ /\ manifest.version /= rManifest[r].version
               /\ rState' = [rState EXCEPT ![r] = START_ACK]
               /\ UNCHANGED <<manifest, rManifest>>
            \/ /\ manifest.version = rManifest[r].version
               /\ manifest' = newManifest
               /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
               /\ rState' = [rState EXCEPT ![r] = READ_ENTRY]
    /\ UNCHANGED <<writerVars, gcVars, auxVars, batch, cursor, rCursor>>

ManifestHasMoreEntries(m, nseq) ==
    \E seq \in DOMAIN m.entries : seq >= nseq

RefreshManifest(r) ==
    /\ rState[r] = READ_ENTRY
    /\ ~ManifestHasMoreEntries(rManifest[r], rCursor[r].nextSeq)
    /\ manifest /= rManifest[r]
    /\ \/ /\ manifest.epoch > rManifest[r].epoch
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED]
          /\ UNCHANGED rManifest
       \/ /\ manifest.epoch = rManifest[r].epoch
          /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
          /\ UNCHANGED rState
    /\ UNCHANGED <<storeVars, writerVars, gcVars, auxVars, rCursor>>

GcStart(gc) ==
    /\ EnableGC
    /\ \/ gcState[gc] = IDLE
       \* or we're deleting artifacts and there's nothing left to delete
       \/ /\ gcState[gc] = DELETE
          /\ ~\E id \in DOMAIN batch : id < gcManifest[gc].tsFloor
    /\ gcState' = [gcState EXCEPT ![gc] = DELETE]
    /\ gcManifest' = [gcManifest EXCEPT ![gc] = manifest]
    /\ UNCHANGED <<storeVars, writerVars, readerVars, auxVars>>

\* The pending batch check is impossible in reality, and Buffer 
\* avoids deleting written batches which haven't yet been added
\* to the manifest via a grace period (i.e. these batches should
\* be pretty new, but batches that need GC should be older)
\* However, even with this check, it isn't enough for this
\* to be safe. See the Buffer_notes.md for a discussion of
\* GC correctness.
DeleteBatch(gc) ==
    /\ EnableGC
    /\ gcState[gc] = DELETE
    /\ \E id \in DOMAIN batch :
        /\ id < gcManifest[gc].tsFloor
        /\ ~\E w \in Writers : 
            /\ wPendingBatch[w] /= NIL
            /\ wPendingBatch[w].id = id
        /\ batch' = [i \in (DOMAIN batch \ {id}) |-> batch[i]]
    /\ UNCHANGED <<manifest, cursor, readerVars, writerVars, gcVars, auxVars>>

\***********************************************************************
\* TYPE correctness
\***********************************************************************

ManifestOK(m) ==
    /\ \A seq \in DOMAIN m.entries : 
        /\ seq \in WritableSeqNos
        /\ m.entries[seq] \in WritableBatchIds
    /\ m.nextSeq \in NextSeqNos
    /\ m.epoch \in Nat
    /\ m.version \in Nat
    
LocalManifestOK(lManifest) ==
    \/ lManifest = NIL
    \/ ManifestOK(lManifest)
    
CursorType ==
    [nextSeq: NextSeqNos, version: Nat]

PendingBatchType ==
    [id: Nat, data: Values]

TypeOK ==
    /\ \A id \in DOMAIN batch : batch[id] \in Values
    /\ ManifestOK(manifest)
    /\ cursor \in CursorType
    /\ wState \in [Writers -> {IDLE, READ_MANIFEST, APPEND_TO_MANIFEST}]
    /\ wPendingBatch \in [Writers -> PendingBatchType \union {NIL}]
    /\ \A w \in Writers : LocalManifestOK(wManifest[w])
    /\ rState \in [Readers -> {IDLE, CLAIM_MANIFEST, CLAIM_CURSOR,
                               READ_ENTRY, START_ACK, PREFIX_TRIM, COMMIT, PREEMPTED}]
    /\ rCursor \in [Readers -> CursorType]
    /\ \A r \in Readers : LocalManifestOK(rManifest[r])
    /\ gcState \in [GarbageCollectors -> {IDLE, DELETE}]
    /\ \A gc \in GarbageCollectors : LocalManifestOK(gcManifest[gc])                
    /\ auxUsedValues \in SUBSET Values
    /\ auxReadValues \in Seq(Values)
    /\ auxWrittenValues \in Seq(Values)
    /\ auxTsId \in Nat

\***********************************************************************
\* INVARIANTS
\***********************************************************************

\* INV: ValidReaders
\* No reader got into an illegal state and at least one is functional
ValidReaders ==
    /\ \A r \in Readers : rState[r] /= INVALID_STATE
    /\ \E r \in Readers : rState[r] /= PREEMPTED
        

\* INV: ReadValuesPrefixOfWrittenValues
\* Reading a value requires every earlier-written value
\* to have already been read
ReadValuesCompatibleWithWrittenValues ==
    \A readPos \in DOMAIN auxReadValues :
        \E writePos \in DOMAIN auxWrittenValues :
            \* Every read value was written
            /\ auxReadValues[readPos] = auxWrittenValues[writePos]
            \* Every written value that was written beforehand, has also been read
            /\ \A earlierWritePos \in 1..writePos :
                \E earlierReadPos \in 1..readPos :
                    auxReadValues[earlierReadPos] = auxWrittenValues[earlierWritePos]

\* INV: ManifestConsistentWithStoredBatches
\* THIS GETS VIOLATED WHEN EnableGC=TRUE
\* Each manifest entry has a corresponding batch in storage
ManifestConsistentWithStoredBatches ==
    \A seq \in DOMAIN manifest.entries :
        LET id == manifest.entries[seq]
        IN id \in DOMAIN batch

\* INV: ReadValuesPrefixOfWrittenValues
\* THIS GETS VIOLATED, DO NOT ENABLE IT. USED FOR EXPLANATORY REASONS
\* This gets violated due to at-least-once guarantees.
\* Checks where the read values are a prefix of the write values
\* which would be needed if this were used for SMR (which it isn't)
\* But it's interesting to keep the invariant anyway.
ReadValuesPrefixOfWrittenValues ==
    /\ Len(auxReadValues) <= Len(auxWrittenValues)
    /\ \A seq \in DOMAIN auxReadValues : 
        auxReadValues[seq] = auxWrittenValues[seq]

\* INV: ReadValuesOrderingCompatibleWithWrittenValues
\* THIS GETS VIOLATED, DO NOT ENABLE IT. USED FOR EXPLANATORY REASONS
\* This gets violated due to at-least-once guarantees, plus a stale
\* reader can continue reading, it just can't successfully ack due to the epoch.
\* Checks whether the read values are a prefix, with repeats, of the write values
\* Basically, is the read history compatible with an ordered consumption
\* of the entries, with a cursor that can jump backwards, but can't jump
\* multiple positions forwards.
ReadValuesOrderingCompatibleWithWrittenValues ==
    \* Every value read occurs in the committed write history.
    /\ \A readPos \in DOMAIN auxReadValues :
        \E writePos \in DOMAIN auxWrittenValues :
            auxReadValues[readPos] = auxWrittenValues[writePos]

    /\ \/ Len(auxReadValues) = 0
       \/ /\ Len(auxReadValues) > 0
          /\ auxReadValues[1] = auxWrittenValues[1]
          \* Each subsequent read either advances exactly one
          \* written position or jumps backward.
          /\ \A readPos \in 2..Len(auxReadValues) :
                \E prevWritePos \in DOMAIN auxWrittenValues :
                \E currWritePos \in DOMAIN auxWrittenValues :
                    /\ auxReadValues[readPos-1] = auxWrittenValues[prevWritePos]
                    /\ auxReadValues[readPos] = auxWrittenValues[currWritePos]
                    /\ \/ currWritePos = prevWritePos + 1
                       \/ currWritePos <= prevWritePos

\***********************************************************************
\* LIVENESS
\***********************************************************************

\* There are only two terminal states:
\* - READ_ENTRY: ready to read the next entry (but no more coming)
\* - PREEMPTED: when another reader preempts this one by taking control of the manifest
\* Readers keep restarting (reverting to IDLE) when encountering
\* conflicts during initialization, but go to PREEMPTED once established.
ReaderReachesTailOrPreempts ==
    \A r \in Readers :
        <>[](\/ /\ rCursor[r].nextSeq = Cardinality(Values) + 1
                /\ rState[r] = READ_ENTRY
             \/ rState[r] = PREEMPTED)

\***********************************************************************
\* INIT, NEXT and SPEC
\***********************************************************************

Init ==
    /\ batch = <<>>
    /\ manifest = [entries |-> <<>>, 
                   nextSeq |-> 1, 
                   epoch   |-> 0, 
                   tsFloor |-> 0,
                   version |-> 0]
    /\ cursor = [nextSeq |-> 1, version |-> 0]
    /\ wState = [w \in Writers |-> IDLE]
    /\ wPendingBatch = [w \in Writers |-> NIL]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ rState = [r \in Readers |-> IDLE]
    /\ rCursor = [r \in Readers |-> [nextSeq |-> 1, version |-> 0]]
    /\ rManifest = [r \in Readers |-> NIL]
    /\ gcState = [gc \in GarbageCollectors |-> IDLE]
    /\ gcManifest = [gc \in GarbageCollectors |-> NIL]
    /\ auxUsedValues = {}
    /\ auxReadValues = <<>>
    /\ auxWrittenValues = <<>>
    /\ auxTsId = 1

Next ==
    \/ \E w \in Writers :
        \/ \E v \in Values : WriteBatch(w, v)              
        \/ ReadManifest(w)
        \/ AppendToManifest(w)
    \/ \E r \in Readers :
        \* Initialize
        \/ ReaderInitialize(r)
        \/ ClaimManifest(r)
        \/ ClaimCursor(r)
        \* Tailing
        \/ \E id \in WritableBatchIds : ReadEntry(r, id)
        \/ RefreshManifest(r)
        \* Ack
        \/ AckPersistCursor(r)
        \/ AckReadManifest(r)
        \/ AckPrefixTrim(r)
        \/ AckCommit(r)
    \/ \E gc \in GarbageCollectors :
        \/ GcStart(gc)
        \/ DeleteBatch(gc)

Fairness ==
    /\ \A w \in Writers :
         /\ \A v \in Values : WF_vars(WriteBatch(w, v))
        /\ WF_vars(ReadManifest(w))
        /\ WF_vars(AppendToManifest(w))
    /\ \A r \in Readers :
        /\ WF_vars(ReaderInitialize(r))
        /\ WF_vars(ClaimManifest(r))
        /\ WF_vars(ClaimCursor(r))
        /\ \A id \in WritableBatchIds : WF_vars(ReadEntry(r, id))
        /\ WF_vars(AckPersistCursor(r))
        /\ WF_vars(RefreshManifest(r))
        /\ WF_vars(AckReadManifest(r))
        /\ WF_vars(AckPrefixTrim(r))
        /\ WF_vars(AckCommit(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
