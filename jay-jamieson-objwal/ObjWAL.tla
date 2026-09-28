----------------------------- MODULE ObjWAL -------------------------

(*
    This module specifies a stateful replicated application built on
    https://github.com/JayJamieson/objwal.  Here, a "replica" means a
    complete application instance, not just objwal's wal.Replica reader.

    Each replica is modeled as three cooperating logical components:

    * Producer: claims the manifest epoch and, while it remains the current
      writer, uploads segments and appends their references to the manifest.
    * Application state machine: restores a base snapshot, replays the WAL,
      and applies committed values to the replica's local machine state.
    * Snapshotter: checkpoints that local state, publishes the snapshot in
      the manifest, and trims the manifest entries covered by the snapshot.

    The actions for these components are separated to make their individual
    responsibilities and interleavings explicit.  They are nevertheless parts
    of the same replica, may run in the same process, and share that replica's
    local state.  Every replica is capable of performing all three roles: it
    can recover by reading, become the producer by claiming a newer epoch, and
    snapshot its state while it is the current writer.

    This reflects the boundaries exposed by objwal: wal.Producer implements
    fenced WAL publication, wal.Replica/Applier implement replay, and the
    manifest contains the primitives needed to publish and truncate through a
    snapshot.  The application supplies the state machine, snapshot encoding,
    and the orchestration that combines those primitives into this protocol.

    Garbage collection is omitted.  Assuming a collector deletes only objects
    no longer reachable from the committed manifest, deletion does not change
    the logical WAL (unlike protocols where the WAL address space defines
    the WAL, such as SlateDB). Therefore a lack of GC is a lack of housekeeping,
    and any naive GC **shouldn't** impact correctness.
*)

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences, TLC

CONSTANTS Replicas, \* The set of stateful application replicas
          Values    \* The set of values to append

\* replica states
CONSTANTS IDLE, SNAPSHOT_RECOVERY, REPLAY_WAL, READY,
          CLAIM_MANIFEST, PREAPPEND_VALIDATE, PRESNAPSHOT_VALIDATE,
          APPEND_TO_MANIFEST, WRITE_SNAPSHOT, COMMIT_SNAPSHOT, PREEMPTED

CONSTANTS None

\* Durable state on S3
VARIABLES segment,          \* Replica ID -> A sequence of values
          manifest,         \* The manifest file
          snapshot          \* Snapshot ID -> Snapshot file

VARIABLES rState,        \* Replica -> state
          rPendingSeg,   \* Replica -> pending commit batch id
          rSegOrdinal,   \* Replica -> The current segment ordinal
          rManifest,     \* Replica -> local copy of the manifest
          rMachineData,  \* Replica -> state machine data (a sequence of Values)
          rReplaySeq     \* Replica -> its WAL replay position

\* Auxilliary variables for invariants
VARIABLES auxUsedValues, 
          auxCommitted   \* The sequence of committed values

replicaVars == <<rState, rPendingSeg, rManifest, rReplaySeq,
                 rSegOrdinal, rMachineData>>
storeVars == <<segment, manifest, snapshot>>
auxVars == <<auxUsedValues, auxCommitted>>
vars == <<storeVars, replicaVars, auxVars>>

Symmetry ==
    Permutations(Replicas)
        \union Permutations(Values)

WritableSeqNos == 1..Cardinality(Values)
NextSeqNos == 1..Cardinality(Values) + 1

ReadSegment(id) == IF id.ordinal \in DOMAIN segment[id.replica]
                   THEN segment[id.replica][id.ordinal] ELSE None
SegmentId(r) == [replica |-> r, ordinal |-> rSegOrdinal[r]]
NextSeq(r) == rManifest[r].nextSeq

ValidateManifestBeforeNextState(r, nextState) ==
    /\ \/ /\ rManifest[r].epoch /= manifest.epoch
          /\ rState' = [rState EXCEPT ![r] = PREEMPTED]
          /\ UNCHANGED rManifest
       \/ /\ rManifest[r].epoch = manifest.epoch
          /\ rState' = [rState EXCEPT ![r] = nextState]
          /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ UNCHANGED <<storeVars, auxVars, rPendingSeg, rReplaySeq,
                   rSegOrdinal, rMachineData>>

\***********************************************************************
\* ACTIONS
\***********************************************************************

(* ---------------------------------------------------------
    ACTION: InitializeProducer (producer component)

    A replica starts by initializing its producer which
    gets the latest manifest and transitions to 
    CLAIM_MANIFEST.
-----------------------------------------------------------*)

InitializeProducer(r) ==
    /\ rState[r] = IDLE
    /\ rManifest' = [rManifest EXCEPT ![r] = manifest]
    /\ rState' = [rState EXCEPT ![r] = CLAIM_MANIFEST]
    /\ UNCHANGED <<storeVars, auxVars, rSegOrdinal, rReplaySeq,
                   rPendingSeg, rMachineData>>

(* ---------------------------------------------------------
    ACTION: ClaimManifest (producer component)

    A replica bumps the epoch and version of its
    cached manifest then attempts a CAS write (based on
    version). If the write succeeds then the producer
    is now started and the replica can start accepting
    writes.
    If the CAS fails, the replica reverts to IDLE where
    it can try and start again.
-----------------------------------------------------------*)

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
                /\ rState' = [rState EXCEPT ![r] = SNAPSHOT_RECOVERY]
    /\ UNCHANGED <<auxVars, segment, snapshot, rPendingSeg, rReplaySeq,
                   rSegOrdinal, rMachineData>>

(* ---------------------------------------------------------
    ACTION: SnapshotRecovery (application component)

    The application state machine starts recovery by
    downloading the current snapshot if one exists and
    writing its local machine data.
    It then transitions to CATCHUP_RECOVERY to replay the
    WAL.
-----------------------------------------------------------*)

SnapshotRecovery(r) ==
    /\ rState[r] = SNAPSHOT_RECOVERY
    /\ LET seq  == rManifest[r].snapshotSeq
           snap == snapshot[seq]
       IN /\ rState' = [rState EXCEPT ![r] = REPLAY_WAL]
          /\ IF seq = 0 
             THEN UNCHANGED <<rMachineData, rReplaySeq>>
             ELSE /\ rMachineData' = [rMachineData EXCEPT ![r] = snap]
                  /\ rReplaySeq' = [rReplaySeq EXCEPT ![r] = seq + 1]
    /\ UNCHANGED <<storeVars, auxVars, rManifest, rPendingSeg, 
                   rSegOrdinal>>

(* ---------------------------------------------------------
    ACTION: ReplayWAL (application component)

    The application state machine replays the WAL entries
    (which are the committed values above the snapshot seq).

    Each invocation replays one WAL entry. Once the 
    replay seq has reached the manigest nextSeq, replay
    is over and the replica transitions to READY.
-----------------------------------------------------------*)

ReplayWAL(r) ==
    /\ rState[r] = REPLAY_WAL
    /\ \/ /\ rReplaySeq[r] = rManifest[r].nextSeq
          /\ rState' = [rState EXCEPT ![r] = READY]
          /\ UNCHANGED <<rMachineData, rReplaySeq>>
       \/ \E pos \in DOMAIN rManifest[r].entries :
            LET entry == rManifest[r].entries[pos]
                read == ReadSegment(entry.id)
            IN 
               /\ entry.seq = rReplaySeq[r]
               /\ rMachineData' = [rMachineData EXCEPT ![r] = @ \o read]
               /\ rReplaySeq' = [rReplaySeq EXCEPT ![r] = @ + entry.count]
               /\ UNCHANGED rState
    /\ UNCHANGED <<storeVars, auxVars, rManifest, rPendingSeg,
                   rSegOrdinal>>

(* ---------------------------------------------------------
    ACTION: ReplayWAL (app/producer component)

    An application accepts a write and the producer
    buffers it locally.
-----------------------------------------------------------*)

AppendValueLocally(r, v) ==
    /\ rState[r] = READY
    /\ v \notin auxUsedValues
    /\ rPendingSeg' = [rPendingSeg EXCEPT ![r] = Append(@, v)]
    /\ auxUsedValues' = auxUsedValues \union {v}
    /\ UNCHANGED <<storeVars, rState, rManifest, rReplaySeq, rSegOrdinal,
                   rMachineData, auxCommitted>>

(* ---------------------------------------------------------
    ACTION: WriteSegment (producer component)

    The producer writes a segment file containing the
    sequence of buffered writes (to address
    seg-prefix/replica-run-id/ordinal, 
    e.g. wal/seg/01K8XYZABC123/0000000000000007. Which in
    this spec is modeled as the funcion [replica -> [nat -> segment]]
-----------------------------------------------------------*)
WriteSegment(r) ==
    /\ rState[r] = READY
    /\ Len(rPendingSeg[r]) > 0
    /\ segment' = [segment EXCEPT ![r] = @ 
                        @@ (rSegOrdinal[r] :> rPendingSeg[r])]
    /\ rState' = [rState EXCEPT ![r] = PREAPPEND_VALIDATE]
    /\ UNCHANGED <<manifest, snapshot, auxVars, rPendingSeg, rManifest,
                   rSegOrdinal, rReplaySeq, rMachineData>>

(* ---------------------------------------------------------
    ACTION: PreAppendValidate (producer component)

    Before attempting a manifest CASE write, the producer
    refreshes its manifest to check its epoch is still
    valid. If so it then transitions to APPEND_TO_MANIFEST,
    else it stops in PREEMPTED.
-----------------------------------------------------------*)

PreAppendValidate(r) ==
    /\ rState[r] = PREAPPEND_VALIDATE
    /\ ValidateManifestBeforeNextState(r, APPEND_TO_MANIFEST)

(* ---------------------------------------------------------
    ACTION: AppendToManifest (producer component)

    The producer creates a new segment entry and appends
    it to the entries list. It attempts a manifest
    CASE write. If it succeeds, the write is complete.
    If the write condition fails, the replica transitions
    back to PREAPPEND_VALIDATE where it will recheck its
    epoch is still valid. If the epoch is valid, the producer
    will try and append a new segment entry again. If the
    epoch is invalid, the replica stops (in PREEMPTED).
-----------------------------------------------------------*)

AppendToManifest(r) ==
    /\ rState[r] = APPEND_TO_MANIFEST
    /\ LET m     == rManifest[r]
           entry == [seq   |-> m.nextSeq, 
                     count |-> Len(rPendingSeg[r]),
                     id    |-> SegmentId(r)]
           newEntries  == Append(m.entries, entry)
           currVersion == m.version
           newManifest == [m EXCEPT !.entries = newEntries,
                                    !.nextSeq = @ + entry.count, 
                                    !.version = @ + 1]
       IN \/ /\ manifest.version /= currVersion
             /\ rState' = [rState EXCEPT ![r] = PREAPPEND_VALIDATE]
             /\ UNCHANGED <<storeVars, auxVars, rManifest, rPendingSeg,
                            rMachineData, rReplaySeq, 
                            rSegOrdinal, auxCommitted>>
          \/ /\ manifest.version = currVersion 
             /\ manifest' = newManifest
             /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
             /\ rState' = [rState EXCEPT ![r] = READY]
             /\ rPendingSeg' = [rPendingSeg EXCEPT ![r] = <<>>]
             /\ rSegOrdinal' = [rSegOrdinal EXCEPT ![r] = @ + 1]
             /\ rMachineData' = [rMachineData EXCEPT ![r] = @ \o rPendingSeg[r]]
             /\ auxCommitted' = auxCommitted \o rPendingSeg[r]
    /\ UNCHANGED <<auxUsedValues, segment, snapshot, rReplaySeq>>

(* ---------------------------------------------------------
    ACTION: PrepareSnapshot (snapshotter component)

    The snapshotter sees that the next snapshottable
    seq is beyond the current snapshot and that no
    existing snapshot has been written for that seq.
    
    The snapshotter runs when there is no append commit
    in progress, and it also blocks a concurrent
    commit (mostly for spec simplicity, it could be made
    to be concurrent).
-----------------------------------------------------------*)

PrepareSnapshot(r) ==
    /\ rState[r] = READY
    /\ LET snapshotSeq == rManifest[r].nextSeq - 1 IN
        /\ snapshotSeq > rManifest[r].snapshotSeq
        /\ snapshotSeq \notin DOMAIN snapshot 
        /\ rState' = [rState EXCEPT ![r] = PRESNAPSHOT_VALIDATE]
        /\ UNCHANGED <<storeVars, auxVars, rPendingSeg, rManifest,
                       rReplaySeq, rSegOrdinal, rMachineData>>

(* ---------------------------------------------------------
    ACTION: PreSnapshotValidate (snapshotter component)

    Before attempting a snapshot, the producer
    refreshes its manifest to check its epoch is still
    valid. If so it then transitions to WRITE_SNAPSHOT,
    else it stops in PREEMPTED.
-----------------------------------------------------------*)

PreSnapshotValidate(r) ==
    /\ rState[r] = PRESNAPSHOT_VALIDATE
    /\ ValidateManifestBeforeNextState(r, WRITE_SNAPSHOT)

(* ---------------------------------------------------------
    ACTION: WriteSnapshot (snapshotter component)

    The replica attempts to write its current machine 
    data as a snapshot using put-if-absent. If a 
    snapshot already exists at that address (the 
    address is determined by its snapshotSeq), it discards
    the snapshot and reverts to READY.
    If the write succeeds it transitions to COMMIT_SNAPSHOT
-----------------------------------------------------------*)

WriteSnapshot(r) ==
    /\ rState[r] = WRITE_SNAPSHOT
    /\ LET snapshotSeq == NextSeq(r) - 1 IN
        /\ \/ /\ snapshotSeq \in DOMAIN snapshot
              /\ rState' = [rState EXCEPT ![r] = READY]
              /\ UNCHANGED <<snapshot>>
           \/ /\ snapshotSeq \notin DOMAIN snapshot 
              /\ snapshot' = snapshot @@ (snapshotSeq :> rMachineData[r])
              /\ rState' = [rState EXCEPT ![r] = COMMIT_SNAPSHOT]
    /\ UNCHANGED <<auxVars, segment, manifest, rManifest, rReplaySeq, 
                   rSegOrdinal, rPendingSeg, rMachineData>>

(* ---------------------------------------------------------
    ACTION: CommitSnapshot (snapshotter component)

    The replica snapshotter trims the its local manifest
    entry list to remove those entries covered by the
    written snapshot. It also sets the snapshot seq
    which both identifies its address but also its upper
    seq range.
    If the CAS write succeeds, the snapshot process is
    complete. If it fails the replica transitions to
    PRESNAPSHOT_VALIDATE where it will refresh the manifest
    and check its epoch is still valid. If valid, it will
    return here to retry the snapshot commit, else it 
    will stop in PREEMPTED.
-----------------------------------------------------------*)

PrefixTrimmedEntries(r, snapshotSeq) ==
     LET entries  == rManifest[r].entries
         remaming == { pos \in DOMAIN entries : entries[pos].seq > snapshotSeq }
     IN [pos \in remaming |-> entries[pos]]

CommitSnapshot(r) ==
    /\ rState[r] = COMMIT_SNAPSHOT
    /\ LET snapshotSeq == NextSeq(r) - 1
           newEntries  == PrefixTrimmedEntries(r, snapshotSeq)
           currVersion == rManifest[r].version
           newManifest == [rManifest[r] EXCEPT !.snapshotSeq = snapshotSeq,
                                               !.entries = newEntries,
                                               !.version = @ + 1]
       IN \/ /\ manifest.version > currVersion
             /\ rState' = [rState EXCEPT ![r] = PRESNAPSHOT_VALIDATE]
             /\ UNCHANGED <<manifest, rManifest>>
          \/ /\ manifest.version = currVersion
             /\ manifest' = newManifest
             /\ rManifest' = [rManifest EXCEPT ![r] = newManifest]
             /\ rState' = [rState EXCEPT ![r] = READY]
    /\ UNCHANGED <<auxVars, segment, snapshot, rReplaySeq, rSegOrdinal,
                   rMachineData, rPendingSeg>>

\***********************************************************************
\* TYPE correctness
\***********************************************************************

\* Segments are written to an address based on the replica id and
\* a per-replica incrementing ordinal
SegmentIdType == [replica: Replicas, ordinal: Nat]
EntryType == [seq: Nat, count: Nat, id: SegmentIdType]
ManifestType ==
    [epoch: Nat,
     entries: Seq(EntryType),
     nextSeq: NextSeqNos,
     snapshotSeq: Nat,
     version: Nat]

TypeOK ==
    /\ \A r \in Replicas :
        \A ordinal \in DOMAIN segment[r] :
            /\ ordinal \in Nat
            /\ segment[r][ordinal] \in Seq(Values)
    /\ manifest \in ManifestType
    /\ \A seq \in DOMAIN snapshot :
        /\ seq \in WritableSeqNos
        /\ snapshot[seq] \in Seq(Values)
    /\ rState \in [Replicas -> 
            {IDLE, SNAPSHOT_RECOVERY, REPLAY_WAL, READY,
             CLAIM_MANIFEST, PREAPPEND_VALIDATE, PRESNAPSHOT_VALIDATE,
             APPEND_TO_MANIFEST, WRITE_SNAPSHOT, COMMIT_SNAPSHOT, PREEMPTED}]
    /\ rManifest \in [Replicas -> ManifestType \union {None}]
    /\ rReplaySeq \in [Replicas -> NextSeqNos \union {0}]
    /\ rPendingSeg \in [Replicas -> Seq(Values)]
    /\ rMachineData \in [Replicas -> Seq(Values)]
    /\ auxUsedValues \in SUBSET Values
    /\ auxCommitted \in Seq(Values)

\***********************************************************************
\* INVARIANTS
\***********************************************************************

\* INV: ValidWriters
\* There must be at least one functional writer
ValidWriters ==
    \E r \in Replicas : rState[r] /= PREEMPTED

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
    \A r \in Replicas :
        rState[r] = READY =>
            IF rManifest[r].version < manifest.version
            THEN SeqPrefixOf(rMachineData[r], auxCommitted)
            ELSE rMachineData[r] = auxCommitted

\* INV: ManifestRepresentsCommittedLogV2
\* A future replica can recover the complete committed history by loading the
\* manifest snapshot and then replaying its entries in order. The invariant
\* also checks the recovery metadata (entry boundaries, counts, and nextSeq).
ManifestRepresentsCommittedLog ==
    LET m          == manifest
        hist       == auxCommitted
        entries    == m.entries
        entryCount == Len(entries)
    IN
        \* nextSeq identifies the end of the recorded committed history.
        /\ m.nextSeq = Len(hist) + 1
        \* The snapshot is exactly the recoverable committed prefix.
        /\ m.snapshotSeq < m.nextSeq
        /\ \/ m.snapshotSeq = 0
           \/ /\ m.snapshotSeq \in DOMAIN snapshot
              /\ snapshot[m.snapshotSeq] = SubSeq(hist, 1, m.snapshotSeq)
        \* The entries cover every sequence number after the snapshot, with
        \* neither gaps nor overlaps.  Adjacent-boundary checks keep this
        \* linear in the number of entries.
        /\ IF entryCount = 0
           THEN m.nextSeq = m.snapshotSeq + 1
           ELSE /\ entries[1].seq = m.snapshotSeq + 1
                /\ entries[entryCount].seq + entries[entryCount].count =
                      m.nextSeq
        \* Valid segments
        /\ \A pos \in DOMAIN entries :
            LET entry        == entries[pos]
                segmentFound == entry.id.ordinal \in DOMAIN segment[entry.id.replica]
                seg          == IF segmentFound
                                THEN segment[entry.id.replica][entry.id.ordinal]
                                ELSE <<>>
            IN
                \* The segment exists
                /\ segmentFound
                \* Segment seq range within global log bounds
                /\ entry.count > 0
                /\ entry.seq >= m.snapshotSeq + 1
                /\ entry.seq + entry.count <= m.nextSeq
                \* The segment file contains the same number of entries as the seg ref says
                /\ Len(seg) = entry.count
                \* The segment data matches the corresponding slice of recorded committed values
                /\ seg = SubSeq(hist,
                                entry.seq,
                                entry.seq + entry.count - 1)
                \* There is no overlap between segments
                /\ \/ pos = entryCount
                   \/ entries[pos + 1].seq = entry.seq + entry.count

\* INV: ValidSnapshots
\* Every stored snapshot is a prefix (of the write history)
ValidSnapshots ==
    \A seq \in DOMAIN snapshot :
        /\ seq <= Len(auxCommitted)
        /\ snapshot[seq] = SubSeq(auxCommitted, 1, seq)

\* INV: UniqueEpochs
\* Two replicas cannot have the same epoch
UniqueEpochs ==
    ~\E r1, r2 \in Replicas :
        /\ r1 /= r2
        /\ rState[r1] \notin {IDLE, CLAIM_MANIFEST}
        /\ rState[r2] \notin {IDLE, CLAIM_MANIFEST}
        /\ rManifest[r1].epoch = rManifest[r2].epoch

\***********************************************************************
\* LIVENESS
\***********************************************************************

AllValuesAttempted ==
    <>[](auxUsedValues = Values)

\* There are only two terminal states:
\* - READY: when there are no more values to append
\* - PREEMPTED: when another writer preempts this one
\* Replicas keep restarting (reverting to IDLE) when encountering
\* conflicts during initialization, but go to PREEMPTED once established.
WritersReachReadyOrPreempted ==
    \A r \in Replicas :
        <>[](rState[r] \in {READY, PREEMPTED})

\***********************************************************************
\* INIT, NEXT and SPEC
\***********************************************************************

Init ==
    /\ segment = [r \in Replicas |-> <<>>]
    /\ snapshot = <<>>
    /\ manifest = [epoch       |-> 0,
                   entries     |-> <<>>,
                   nextSeq     |-> 1,
                   snapshotSeq |-> 0,
                   version     |-> 1]
    /\ rState = [r \in Replicas |-> IDLE]
    /\ rPendingSeg = [r \in Replicas |-> <<>>]
    /\ rSegOrdinal = [r \in Replicas |-> 0]
    /\ rManifest = [r \in Replicas |-> None]
    /\ rReplaySeq = [r \in Replicas |-> 1]
    /\ rMachineData = [r \in Replicas |-> <<>>]
    /\ auxUsedValues = {}
    /\ auxCommitted = <<>>

Next ==
    \E r \in Replicas :
        \* Producer 
        \/ InitializeProducer(r)
        \/ ClaimManifest(r)
        \/ \E v \in Values : AppendValueLocally(r, v)
        \/ WriteSegment(r)
        \/ PreAppendValidate(r)
        \/ AppendToManifest(r)
        \* Machine state
        \/ SnapshotRecovery(r)
        \/ ReplayWAL(r)
        \* Snapshotter
        \/ PrepareSnapshot(r)
        \/ PreSnapshotValidate(r)
        \/ WriteSnapshot(r)
        \/ CommitSnapshot(r)

Fairness ==
    \A r \in Replicas :
        /\ WF_vars(InitializeProducer(r))
        /\ WF_vars(ClaimManifest(r))
        /\ WF_vars(SnapshotRecovery(r))
        /\ WF_vars(ReplayWAL(r))
        /\ \A v \in Values : SF_vars(AppendValueLocally(r, v))
        /\ WF_vars(PreAppendValidate(r))
        /\ WF_vars(AppendToManifest(r))
        /\ WF_vars(PreSnapshotValidate(r))
        /\ WF_vars(WriteSnapshot(r))
        /\ WF_vars(CommitSnapshot(r))

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Fairness

========================================================================
