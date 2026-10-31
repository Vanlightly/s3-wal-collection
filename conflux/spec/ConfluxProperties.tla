---------------- MODULE ConfluxProperties ----------------

EXTENDS ConfluxApply, ConfluxAppend, ConfluxReconf, ConfluxGC

TypeOK ==
    /\ CommonTypeOK
    /\ ApplyTypeOK
    /\ AppendTypeOK
    /\ ReconfTypeOK
    /\ GCTypeOK

\* INV: ValidManifest
\* Checks that each loglet has valid data, according to the data model
\* and protocol. 
ValidManifest ==
    \* The first addr of the first loglet is 1 (using 1-based scheme)
    /\ manifest.loglets[1].first = 1
    \* The active loglet has no tail value
    /\ GetActiveLogletRef(manifest).tail = 0
    \* For every loglet prior to the active loglet, it is sealed,
    \* has a tail with within correct bounds and its tail matches
    \* the first addr of the next loglet
    /\ \A lId \in DOMAIN manifest.loglets :
        LET lRef == GetLogletRef(manifest, lId) IN
            /\ lRef.id = lId
            /\ lId < GetActiveLogletRef(manifest).id =>
                /\ lRef.tail \in 1..(MaxLogletLength + 1)
                /\ IsSealed(lId)
                /\ GetLogletRef(manifest, lId + 1).first = GlobalIndex(lRef, lRef.tail)
    \* If the manifest has a snapshot, that snapshot exists and the
    \* trim boundary corresponds to a stored snapshot
    /\ IF manifest.snapshot = None
       THEN manifest.trimIndex = 0
       ELSE /\ manifest.snapshot \in DOMAIN snapshots
            /\ manifest.trimIndex = Len(snapshots[manifest.snapshot])

\* INV: ValidSequencers
\* For every replica that has (what it thinks is) a live, functional
\* sequencer, the sequencer has valid state. Each loglet only ever
\* has one sequencer, so a given loglet's sequencer state is immutable.
\* So even if a live sequencer is stale, it should still match the
\* manifest.
ValidSequencers ==
    \A r \in Replicas :
        rSequencer[r] \notin {None, Down} =>
            LET seq == rSequencer[r]
                lId == seq.logletId
                lRef == GetLogletRef(manifest, lId)
            IN \* the sequencer's loglet exists in the manifest
               /\ lId \in DOMAIN manifest.loglets
               \* the manifest agrees that the replica should own the sequencer
               /\ lRef.seq = r
               /\ \A slot \in Slots :
                   \* If a slot is completed, then all prior slots must be completed
                   \* and if a slot is not collectable (GC) then it must be written 
                   /\ seq.slots[slot] = COMPLETED =>
                       /\ \A prior \in 1..(slot - 1) : seq.slots[prior] = COMPLETED
                       /\ ~EntryCollectable(manifest.trimIndex, lRef, slot) =>
                               ReadEntry(lId, slot) /= U
                   \* If a slot is free, then all subsequent slots must be free
                   /\ seq.slots[slot] = FREE =>
                       \A later \in (slot + 1)..MaxLogletLength : seq.slots[later] = FREE

\* INV: ValidApplyState
\* No replica has entered ENTRY_NOT_FOUND (meaning a committed
\* entry has been deleted above the trim index)
\* When reading entries, a replica's machine data must not
\* get ahead of the cached tail and the cached tail cannot
\* get ahead of the committed history.
ValidApplyState ==
    \A r \in Replicas :
        /\ rApply[r].state /= ENTRY_NOT_FOUND
        /\ rApply[r].state = READ_NEXT =>
            /\ Len(rApply[r].data) < rApply[r].tail
            /\ rApply[r].tail <= Len(auxHistory) + 1

\* INV: ManifestRepresentsCommittedLog
\* Replaying the entries based on the manifest returns a
\* sequences of values and the committed history (values
\* that have been observed as a successful read or write),
\* are a prefix of the actual log on storage. The reason that
\* the auxHistory is a prefix is because it is appended to
\* upon observation by readers/writers, which comes after
\* a value lands in storage.
ManifestRepresentsCommittedLog ==
    /\ RecoverableLog \in Seq(Values)
    /\ IsPrefix(auxHistory, RecoverableLog)
    /\ auxAckOK

\* INV: ConsistentMachineData
\* The machine data on each replica is a prefix of committed history.
\* Every written snapshot is a prefix of committed history.
ConsistentMachineData ==
    /\ \A r \in Replicas : IsPrefix(rApply[r].data, auxHistory)
    /\ \A id \in DOMAIN snapshots :
            /\ id = Len(snapshots[id])
            /\ IsPrefix(snapshots[id], auxHistory)

\* INV: NoDuplicateValues
\* Without client retries being modeled, this spec should allow no
\* duplicates, even after a failed seal check, as an ambiguous write
\* result is checked against refreshed metadata which definitively
\* tells the writer if its write is included or excluded from the
\* loglet, and on exclusion, the writer tries the same value again
\* against the new active loglet.
NoDuplicateValues ==
    /\ Cardinality(SeqToSet(RecoverableLog)) = Len(RecoverableLog)
    /\ SeqToSet(RecoverableLog) \subseteq auxUsedValues

\* LIVENESS: ReconfigurationCompletes
\* Once a reconfiguration task has kicked off, it eventually returns to IDLE
ReconfigurationCompletes ==
    \A r \in Replicas : rReconf[r].state /= IDLE ~> rReconf[r].state = IDLE

\* LIVENESS: PrefixTrimCompletes
\* Once a prefixTrim (GC) task has kicked off, it eventually returns to IDLE
PrefixTrimCompletes ==
    \A r \in Replicas : rGC[r].state /= IDLE ~> rGC[r].state = IDLE

=============================================================================
