----------------------------- MODULE Buffer -------------------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Writers,
          Readers,
          Ids,
          Values

CONSTANTS IDLE, READ_MANIFEST, APPEND_TO_MANIFEST, 
          READ_ENTRY, INCREMENT_EPOCH, RETRY_ACK, COMMIT, 
          PREFIX_TRIM, PREEMPTED

CONSTANTS NIL

ASSUME Cardinality(Ids) = Cardinality(Values)

WritableSeqNos == 1..Cardinality(Values)
NextSeqNos == 1..Cardinality(Values) + 1

VARIABLES batches,
          manifest,
          cursor,
          wState,
          wPendingBatch,
          wManifest,
          rState,
          rCursor,
          rManifest,
          auxUsedValues,
          auxUsedIds,
          auxWrittenValues,
          auxReadValues

writerVars == <<wState, wPendingBatch, wManifest>>
readerVars == <<rState, rCursor, rManifest>>
storeVars == <<batches, manifest, cursor>>
auxVars == <<auxUsedValues, auxUsedIds, auxReadValues, auxWrittenValues>>
vars == <<storeVars, writerVars, readerVars, auxVars>>

Read(id) == batches[id]

\***********************************************************************
\* ACTIONS
\***********************************************************************

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

ReaderInitialize(r) ==
    /\ rState[r] = IDLE
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rCursor' = [rCursor EXCEPT ![r] = cursor]
    /\ rState' = [rState EXCEPT ![r] = INCREMENT_EPOCH]
    /\ UNCHANGED <<storeVars, writerVars, auxVars>>

IncrementManifestEpoch(r) ==
    /\ rState[r] = INCREMENT_EPOCH
    /\ \/ /\ manifest.version > rManifest[r].version
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED] 
          /\ UNCHANGED <<manifest, rManifest>>
       \/ /\ manifest.version = rManifest[r].version
          /\ LET newManifest == [rManifest[r] EXCEPT !.epoch = @ + 1,
                                                     !.version = @ + 1]
             IN
                /\ manifest' = newManifest
                /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
                /\ rState' = [rState EXCEPT ![r] = READ_ENTRY]
    /\ UNCHANGED <<writerVars, auxVars, batches, cursor, rCursor>>

ReadEntry(r, id) ==
    /\ rState[r] = READ_ENTRY
    /\ \E seq \in DOMAIN rManifest[r].entries :
        /\ seq = rCursor[r].nextSeq
        /\ id = rManifest[r].entries[seq]
        /\ auxReadValues' = Append(auxReadValues, Read(id))
        /\ rCursor' = [rCursor EXCEPT ![r].nextSeq = @ + 1]
    /\ UNCHANGED <<storeVars, writerVars, auxUsedIds, auxUsedValues,
                   auxWrittenValues, rManifest, rState>>

SaveCursor(r) ==
    /\ rState[r] = READ_ENTRY
    /\ \/ /\ rCursor[r].version /= cursor.version
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED]
          /\ UNCHANGED <<cursor, rCursor>>
       \/ /\ rCursor[r].version = cursor.version
          /\ \/ rCursor[r].nextSeq > cursor.nextSeq
             \/ rCursor[r].ackSeq > cursor.ackSeq
          /\ LET newCursor == [rCursor[r] EXCEPT !.version = @ + 1]
             IN /\ cursor' = newCursor 
                /\ rCursor' = [rCursor EXCEPT ![r] = newCursor]
                /\ UNCHANGED rState
    /\ UNCHANGED <<writerVars, auxVars, batches, manifest, rManifest>>

AckReadManifest(r) ==
    /\ rState[r] \in {READ_ENTRY, RETRY_ACK}
    /\ rCursor[r].nextSeq - rCursor[r].ackSeq > 1
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
               /\ rState' = [rState EXCEPT ![r] = RETRY_ACK]
               /\ UNCHANGED <<manifest, rManifest, rCursor>>
            \/ /\ manifest.version = rManifest[r].version
               /\ manifest' = newManifest
               /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
               /\ rCursor' = [rCursor EXCEPT ![r].ackSeq = ackSeq]
               /\ rState' = [rState EXCEPT ![r] = READ_ENTRY]
    /\ UNCHANGED <<writerVars, auxVars, batches, cursor>>

ManifestHasMoreEntries(m, nseq) ==
    \E seq \in DOMAIN m.entries : seq >= nseq

RefreshManifest(r) ==
    /\ rState[r] = READ_ENTRY
    /\ ~ManifestHasMoreEntries(rManifest[r], rCursor[r].nextSeq)
    /\ ManifestHasMoreEntries(manifest, rCursor[r].nextSeq)
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
    [nextSeq: NextSeqNos, ackSeq: WritableSeqNos \union {0}, version: Nat]

TypeOK ==
    /\ \A id \in DOMAIN batches : batches[id] \in Values
    /\ ManifestOK(manifest)
    /\ cursor \in CursorType
    /\ wState \in [Writers -> {IDLE, READ_MANIFEST, APPEND_TO_MANIFEST}]
    /\ wPendingBatch \in [Writers -> Ids \union {NIL}]
    /\ \A w \in Writers : LocalManifestOK(wManifest[w])
    /\ rState \in [Readers -> {IDLE, INCREMENT_EPOCH, READ_ENTRY,
                               RETRY_ACK, PREFIX_TRIM, COMMIT, PREEMPTED}]
    /\ rCursor \in [Readers -> CursorType]
    /\ \A r \in Readers : LocalManifestOK(rManifest[r])
    /\ auxUsedValues \in SUBSET Values
    /\ auxUsedIds \in SUBSET Ids
    /\ auxReadValues \in Seq(Values)
    /\ auxWrittenValues \in Seq(Values)

\***********************************************************************
\* INVARIANTS
\***********************************************************************

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
                    auxReadValues[earlierReadPos] =
                        auxWrittenValues[earlierWritePos]
        

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
\* INIT, NEXT and SPEC
\***********************************************************************

Init ==
    /\ batches = <<>>
    /\ manifest = [entries |-> <<>>, nextSeq |-> 1, epoch |-> 0, version |-> 0]
    /\ cursor = [nextSeq |-> 1, ackSeq |-> 0, version |-> 0]
    /\ wState = [w \in Writers |-> IDLE]
    /\ wPendingBatch = [w \in Writers |-> NIL]
    /\ wManifest = [w \in Writers |-> NIL]
    /\ rState = [r \in Readers |-> IDLE]
    /\ rCursor = [r \in Readers |-> [nextSeq |-> 1, ackSeq |-> 0, version |-> 0]]
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
        \/ ReaderInitialize(r)
        \/ IncrementManifestEpoch(r)
        \/ \E id \in Ids : ReadEntry(r, id)
        \/ SaveCursor(r)
        \/ RefreshManifest(r)
        \/ AckReadManifest(r)
        \/ AckPrefixTrim(r)
        \/ AckCommit(r)

Spec == Init /\ [][Next]_vars

========================================================================