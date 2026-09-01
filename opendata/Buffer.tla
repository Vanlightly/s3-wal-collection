----------------------------- MODULE Buffer -------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,  \* The set of writer processes
          Readers,  \* The set of reader processes
          Ids,      \* The set of object ids
          Values    \* The set of values to append

\* Reader/writer states
CONSTANTS IDLE, READ_MANIFEST, APPEND_TO_MANIFEST, 
          INCREMENT_EPOCH, READ_CURSOR, CLAIM_CURSOR, READ_ENTRY, START_ACK,  
          COMMIT, PREFIX_TRIM, PREEMPTED, INVALID_STATE

CONSTANTS NIL

ASSUME Cardinality(Ids) = Cardinality(Values)

WritableSeqNos == 1..Cardinality(Values)
NextSeqNos == 1..Cardinality(Values) + 1

VARIABLES batches,          \* The batch objects written to S3 (one value per object in this spec)
          manifest,         \* The manifest file in S3
          cursor,           \* The reader cursor in S3
          wState,           \* Writer -> state
          wPendingBatch,    \* Writer -> pending commit batch id
          wManifest,        \* Writer -> local copy of the manifest
          rState,           \* Reader -> state
          rCursor,          \* Reader -> local copy of the cursor
          rManifest         \* Reader -> local copy of the manifest

\* Auxilliary variables for invariants
VARIABLES auxUsedValues, 
          auxUsedIds,
          auxWrittenValues,
          auxReadValues

writerVars == <<wState, wPendingBatch, wManifest>>
readerVars == <<rState, rCursor, rManifest>>
storeVars == <<batches, manifest, cursor>>
auxVars == <<auxUsedValues, auxUsedIds, auxReadValues, auxWrittenValues>>
vars == <<storeVars, writerVars, readerVars, auxVars>>

Symmetry ==
    Permutations(Writers)
        \union Permutations(Readers)
        \union Permutations(Ids)
        \union Permutations(Values)

Read(id) == batches[id]

\***********************************************************************
\* ACTIONS
\***********************************************************************

(* WRITER ACTIONS --------------------------------------*)

WriteBatch(w, v) ==
    /\ wState[w] = IDLE
    /\ v \notin auxUsedValues
    /\ \E id \in Ids :
        /\ id \notin auxUsedIds
        /\ batches' = batches @@ (id :> v)
        /\ wState' = [wState EXCEPT ![w] = READ_MANIFEST]
        /\ wPendingBatch' = [wPendingBatch EXCEPT ![w] = id]
        /\ auxUsedIds' = auxUsedIds \union {id}
        /\ auxUsedValues' = auxUsedValues \union {v}
    /\ UNCHANGED <<readerVars, manifest, cursor, wManifest,
                   auxReadValues, auxWrittenValues>>

ReadManifest(w) ==
    /\ wState[w] = READ_MANIFEST
    /\ wManifest' = [wManifest EXCEPT ![w] = manifest]
    /\ wState' = [wState EXCEPT ![w] = APPEND_TO_MANIFEST]
    /\ UNCHANGED <<storeVars, readerVars, auxVars, wPendingBatch>>

AppendToManifest(w) ==
    /\ wState[w] = APPEND_TO_MANIFEST
    /\ LET newEntries  == wManifest[w].entries @@ 
                            (wManifest[w].nextSeq :> wPendingBatch[w])
           currVersion == wManifest[w].version 
           newVersion  == wManifest[w].version + 1
           newManifest == [wManifest[w] EXCEPT !.entries = newEntries,
                                               !.nextSeq = @ + 1,
                                               !.version = newVersion]
       IN \/ /\ manifest.version = currVersion
             /\ manifest' = newManifest
             /\ wManifest' = [wManifest EXCEPT ![w] = newManifest]
             /\ wState' = [wState EXCEPT ![w] = IDLE]
             /\ wPendingBatch' = [wPendingBatch EXCEPT ![w] = NIL]
             /\ auxWrittenValues' = Append(auxWrittenValues, batches[wPendingBatch[w]])
          \/ /\ manifest.version /= currVersion
             /\ wState' = [wState EXCEPT ![w] = READ_MANIFEST]
             /\ UNCHANGED <<manifest, wManifest, wPendingBatch, auxWrittenValues>>
    /\ UNCHANGED <<readerVars, batches, cursor, auxUsedValues, auxUsedIds, auxReadValues>>

(* READER ACTIONS --------------------------------------*)

ReaderInitialize(r) ==
    /\ rState[r] = IDLE
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rCursor' = [rCursor EXCEPT ![r] = cursor]
    /\ rState' = [rState EXCEPT ![r] = INCREMENT_EPOCH]
    /\ UNCHANGED <<storeVars, writerVars, auxVars>>

IncrementManifestEpoch(r) ==
    /\ rState[r] = INCREMENT_EPOCH
    /\ \/ /\ manifest.version > rManifest[r].version
          /\ rState' = [rState EXCEPT ![r] = IDLE] 
          /\ UNCHANGED <<manifest, rManifest>>
       \/ /\ manifest.version = rManifest[r].version
          /\ LET newManifest == [rManifest[r] EXCEPT !.epoch = @ + 1,
                                                     !.version = @ + 1]
             IN /\ manifest' = newManifest
                /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
                /\ rState' = [rState EXCEPT ![r] = CLAIM_CURSOR]
    /\ UNCHANGED <<writerVars, auxVars, batches, cursor, rCursor>>

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
    /\ UNCHANGED <<writerVars, auxVars, manifest, batches, rManifest>>

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
    /\ UNCHANGED <<storeVars, writerVars, auxUsedIds, auxUsedValues,
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
    /\ UNCHANGED <<writerVars, auxVars, batches, manifest, rManifest>>

AckReadManifest(r) ==
    /\ rState[r] = START_ACK
    /\ \/ /\ manifest.epoch > rManifest[r].epoch
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED]
          /\ UNCHANGED rManifest
       \/ /\ manifest.epoch = rManifest[r].epoch
          /\ rState' = [rState EXCEPT ![r] = PREFIX_TRIM]
          /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, rCursor>>

TrimmedSeqNos(r) ==
     { seq \in DOMAIN rManifest[r].entries : seq >= rCursor[r].nextSeq }

AckPrefixTrim(r) ==
    /\ rState[r] = PREFIX_TRIM
    /\ rManifest' = [rManifest EXCEPT ![r].entries = 
                        [seq \in TrimmedSeqNos(r) |-> rManifest[r].entries[seq]]]
    /\ rState' = [rState EXCEPT ![r] = COMMIT]
    /\ UNCHANGED <<storeVars, writerVars, auxVars, rCursor>>

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
    /\ UNCHANGED <<writerVars, auxVars, batches, cursor, rCursor>>

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
    /\ UNCHANGED <<storeVars, writerVars, auxVars, rCursor>>

\***********************************************************************
\* TYPE correctness
\***********************************************************************

ManifestOK(m) ==
    /\ \A seq \in DOMAIN m.entries : 
        /\ seq \in WritableSeqNos
        /\ m.entries[seq] \in Ids
    /\ m.nextSeq \in NextSeqNos
    /\ m.epoch \in Nat
    /\ m.version \in Nat
    
LocalManifestOK(lManifest) ==
    \/ lManifest = NIL
    \/ ManifestOK(lManifest)
    
CursorType ==
    [nextSeq: NextSeqNos, version: Nat]

TypeOK ==
    /\ \A id \in DOMAIN batches : batches[id] \in Values
    /\ ManifestOK(manifest)
    /\ cursor \in CursorType
    /\ wState \in [Writers -> {IDLE, READ_MANIFEST, APPEND_TO_MANIFEST}]
    /\ wPendingBatch \in [Writers -> Ids \union {NIL}]
    /\ \A w \in Writers : LocalManifestOK(wManifest[w])
    /\ rState \in [Readers -> {IDLE, INCREMENT_EPOCH, READ_CURSOR, CLAIM_CURSOR,
                               READ_ENTRY, START_ACK, PREFIX_TRIM, COMMIT, PREEMPTED}]
    /\ rCursor \in [Readers -> CursorType]
    /\ \A r \in Readers : LocalManifestOK(rManifest[r])
    /\ auxUsedValues \in SUBSET Values
    /\ auxUsedIds \in SUBSET Ids
    /\ auxReadValues \in Seq(Values)
    /\ auxWrittenValues \in Seq(Values)

\***********************************************************************
\* INVARIANTS
\***********************************************************************

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

ReaderReachesTailOrPreempts ==
    \A r \in Readers :
        []<>(\/ rCursor[r].nextSeq = Cardinality(Values) + 1
             \/ rState[r] \in {IDLE, PREEMPTED})

\***********************************************************************
\* INIT, NEXT and SPEC
\***********************************************************************

Init ==
    /\ batches = <<>>
    /\ manifest = [entries |-> <<>>, nextSeq |-> 1, epoch |-> 0, version |-> 0]
    /\ cursor = [nextSeq |-> 1, version |-> 0]
    /\ wState = [w \in Writers |-> IDLE]
    /\ wPendingBatch = [w \in Writers |-> NIL]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ rState = [r \in Readers |-> IDLE]
    /\ rCursor = [r \in Readers |-> [nextSeq |-> 1, version |-> 0]]
    /\ rManifest = [r \in Readers |-> NIL]
    /\ auxUsedValues = {}
    /\ auxUsedIds = {}
    /\ auxReadValues = <<>>
    /\ auxWrittenValues = <<>>

Next ==
    \/ \E w \in Writers :
        \/ \E v \in Values : WriteBatch(w, v)              
        \/ ReadManifest(w)
        \/ AppendToManifest(w)
    \/ \E r \in Readers :
        \* Initialize
        \/ ReaderInitialize(r)
        \/ IncrementManifestEpoch(r)
        \/ ClaimCursor(r)
        \* Tailing
        \/ \E id \in Ids : ReadEntry(r, id)
        \/ RefreshManifest(r)
        \* Ack
        \/ AckPersistCursor(r)
        \/ AckReadManifest(r)
        \/ AckPrefixTrim(r)
        \/ AckCommit(r)

Fairness ==
    /\ \A w \in Writers :
         /\ \A v \in Values : WF_vars(WriteBatch(w, v))
        /\ WF_vars(ReadManifest(w))
        /\ WF_vars(AppendToManifest(w))
    /\ \A r \in Readers :
        /\ WF_vars(ReaderInitialize(r))
        /\ WF_vars(IncrementManifestEpoch(r))
        /\ WF_vars(ClaimCursor(r))
        /\ \A id \in Ids : WF_vars(ReadEntry(r, id))
        /\ WF_vars(AckPersistCursor(r))
        /\ WF_vars(RefreshManifest(r))
        /\ WF_vars(AckReadManifest(r))
        /\ WF_vars(AckPrefixTrim(r))
        /\ WF_vars(AckCommit(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
