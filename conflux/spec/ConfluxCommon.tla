---------------- MODULE ConfluxCommon ----------------

EXTENDS Naturals, Integers, FiniteSets, FiniteSetsExt, Sequences,
        SequencesExt, TLC

CONSTANTS Replicas,         \* The set of replica processes
          Values,           \* The set of values to append
          MaxLogletLength,  \* Max number of appends per loglet
          MaxLoglets,       \* Max number of loglets to create
          FailuresEnabled   \* Allow replica crashes

CONSTANTS IDLE, READY, REFRESH_MANIFEST, REFRESH_AFTER_MISSING, LOAD_SNAPSHOT, CHECKTAIL,
          RECEIVE_TAIL, CHECK_SEAL, READ_NEXT, AWAIT_RECONFIG, ACQUIRE_SLOT, WRITE,
          COMPLETE_SLOT, SEAL, SLOW_CHECKTAIL, COMMIT_RECONFIG,
          COMMIT_TRIM, ENTRY_NOT_FOUND

CONSTANTS FREE, ACQUIRED, COMPLETED, None, Down, U

ASSUME /\ IsFiniteSet(Replicas) /\ Replicas /= {}
       /\ IsFiniteSet(Values) /\ Values /= {}
       /\ MaxLogletLength \in Nat \ {0}
       /\ MaxLoglets \in Nat \ {0}
       /\ FailuresEnabled \in BOOLEAN
       /\ U \notin Values /\ None \notin Values

Symmetry == Permutations(Replicas) \union Permutations(Values)

\* Durable state on S3
VARIABLES manifest, \* Contains the loglet chain metadata, trim position, snapshot id
          entries,  \* The set of S3 objects containing log entries (one obj per entry in this spec)
          sealbits, \* The set of objects representing the sealbit of each loglet
          snapshots \* The set of snapshot files

\* Per task (per-replica) state
VARIABLES rAppend,  \* Append task
          rApply,   \* Apply (app state-machine) task
          rReconf,  \* Reconfiguration task
          rGC       \* PrefixTrim/GC task

VARIABLES rManifest,  \* Replica -> cached copy of the manifest
          rSequencer  \* Replica -> sequencer state

\* History variables. auxUsedValues restricts the workload to distinct
\* requests; auxAckOK and auxHistory only check protocol behavior.
VARIABLES auxUsedValues, auxAckOK, auxHistory

storeVars == <<manifest, entries, sealbits, snapshots>>
serviceVars == <<rManifest, rSequencer>>
auxVars == <<auxUsedValues, auxAckOK, auxHistory>>
sharedVars == <<storeVars, serviceVars, auxVars>>

Slots == 1..MaxLogletLength
LogletIds == 1..MaxLoglets
MaxIndex == MaxLoglets * MaxLogletLength
EmptyEntries == [s \in Slots |-> U]
EmptySequencer == [s \in Slots |-> FREE]
SeqToSet(sq) == {sq[i] : i \in DOMAIN sq}

\*******************************************************************
\* COMMON HELPERS
\*******************************************************************

\* Manifest/metadata helpers -------------------------------

GetActiveLogletRef(m) == Last(m.loglets)
GetScanStart(m, lRef) == Max({1, m.trimIndex - lRef.first + 2})
GetLogletRef(m, lId) == m.loglets[lId]
\* Translate a local slot or exclusive local tail to a global index.
GlobalIndex(lRef, slot) == lRef.first + slot - 1

GetLogletAt(m, index) ==
    CHOOSE lRef \in SeqToSet(m.loglets) :
        /\ lRef.first <= index
        /\ IF lRef.tail = 0 THEN TRUE
           ELSE index < GlobalIndex(lRef, lRef.tail)

ReconfigBase(m) == [version   |-> m.version,
                    logletRef |-> GetActiveLogletRef(m),
                    trimIndex |-> m.trimIndex]

\* Cached manifest helpers ---------------------------------
CachedActiveLogletRef(r) == GetActiveLogletRef(rManifest[r])
CachedActiveLogletId(r) == CachedActiveLogletRef(r).id 
CachedLogletRef(r, lId) == GetLogletRef(rManifest[r], lId) 

\* Find the first missing local slot.
FirstHole(written, start) ==
    Min((start..MaxLogletLength \ written) \union {MaxLogletLength + 1})

\* Collection policy for a known trim point and resolved descriptor.
EntryCollectable(trimIndex, lRef, slot) ==
    \/ GlobalIndex(lRef, slot) <= trimIndex
    \/ /\ lRef.tail /= 0
       /\ GlobalIndex(lRef, lRef.tail) <= trimIndex + 1

\* LogDrive -----------------------------------------------------

\* This is an artifact of how storage is modeled in TLA+.
\* On S3, a LogDrive's address space is simply an addressing convention
CreateDrive(lId) ==
    entries' = entries @@ (lId :> EmptyEntries)

PutEntry(lId, slot, value) ==
    entries' = [entries EXCEPT ![lId][slot] = value]

ReadEntry(lId, slot) ==
    entries[lId][slot]

DeleteEntry(lId, slot) ==
    entries' = [entries EXCEPT ![lId][slot] = U]

\* AtomicLog (incl sequencer) -----------------------------------

\* A seal object could be modeled as an address which is
\* unwritten (unsealed) or written (sealed), or as a written
\* object with version 0 (unsealed), version 1 (sealed), etc.
CreateSeal(lId) ==
    sealbits' = sealbits @@ (lId :> FALSE)

SealLoglet(lId) ==
    sealbits' = [sealbits EXCEPT ![lId] = TRUE]

IsSealed(lId) == sealbits[lId]

CreateSequencer(seq, lId) ==
    rSequencer' = [rSequencer EXCEPT ![seq] =
                            [logletId |-> lId, 
                             slots    |-> EmptySequencer]]

AcquireSequencerSlot(seq, slot) ==
    rSequencer' = [rSequencer EXCEPT ![seq].slots[slot] = ACQUIRED]

CanCompleteSlot(seq, slot) ==
    /\ rSequencer[seq].slots[slot] = ACQUIRED
    /\ \A prior \in 1..(slot - 1) :
        rSequencer[seq].slots[prior] = COMPLETED

CompleteSequencerSlot(seq, slot) ==
    rSequencer' = [rSequencer EXCEPT ![seq].slots[slot] = COMPLETED]    

SequencerAvailable(lRef) ==
    IF rSequencer[lRef.seq] \in {None, Down}
    THEN FALSE
    ELSE rSequencer[lRef.seq].logletId = lRef.id

\* Exclusive local tail: the first slot outside the completed prefix.
SequencerTail(lRef) ==
    FirstHole({slot \in Slots :
                    rSequencer[lRef.seq].slots[slot] = COMPLETED}, 1)

NextSlot(lRef) ==
    FirstHole({slot \in Slots :
                    rSequencer[lRef.seq].slots[slot] /= FREE}, 1)

\*******************************************************************
\* VERIFICATION HELPERS (not part of the protocol)
\*******************************************************************

\* Verification only. Has an optional Java override for performance
ReconstructLog(m, objects, checkpointObjects, unwritten, maxLength) ==
    LET lRef == GetActiveLogletRef(m)
        start == GetScanStart(m, lRef)
        tail == Min({s \in start..maxLength : objects[lRef.id][s] = unwritten}
                    \union {maxLength + 1})
        lastIndex == GlobalIndex(lRef, tail) - 1
    IN [i \in 1..lastIndex |->
            IF i <= m.trimIndex
            THEN checkpointObjects[m.snapshot][i]
            ELSE LET entryLRef == GetLogletAt(m, i)
                 IN objects[entryLRef.id][i - entryLRef.first + 1]]

\* Exclusive local storage tail for verification, not a client checkTail.
StoredTail(m) ==
    LET lRef == GetActiveLogletRef(m) IN
        FirstHole({slot \in Slots : ReadEntry(lRef.id, slot) /= U},
                     GetScanStart(m, lRef))

\* Verification only: durable history, never a protocol decision or S3 GET.
RecoverableLog == ReconstructLog(manifest, entries, snapshots, U, MaxLogletLength)

(* Record the committed prefix through the given inclusive entry index.
   Append or Apply may record it first; preserve the existing
   history and append only entries beyond its end.
   This only updates ghost state for verification; it does
   not refresh metadata or advance applied data. *)
RecordHistory(index) ==
    auxHistory' = IF index > Len(auxHistory)
                  THEN auxHistory \o SubSeq(RecoverableLog,
                                           Len(auxHistory) + 1, index)
                  ELSE auxHistory

\*******************************************************************
\* DATA MODEL
\*******************************************************************

LogletRefType ==
    [id: LogletIds,
     first: 1..(MaxIndex + 1),
     tail: 0..(MaxLogletLength + 1), \* Exclusive local cutoff; 0 means not yet fixed.
     seq: Replicas]

SnapshotIdType == 1..MaxIndex

ManifestType ==
    [version: Nat,
     loglets: Seq(LogletRefType),
     trimIndex: 0..MaxIndex,
     snapshot: SnapshotIdType \union {None}]

SequencerType ==
    [logletId: LogletIds,
     slots: [Slots -> {FREE, ACQUIRED, COMPLETED}]]

CommonTypeOK ==
    /\ manifest \in ManifestType
    /\ Len(manifest.loglets) \in LogletIds
    /\ entries \in [DOMAIN manifest.loglets -> [Slots -> Values \union {U}]]
    /\ sealbits \in [DOMAIN manifest.loglets -> BOOLEAN]
    /\ DOMAIN snapshots \subseteq SnapshotIdType
    /\ \A id \in DOMAIN snapshots : snapshots[id] \in Seq(Values)
    /\ rManifest \in [Replicas -> ManifestType \union {None}]
    /\ rSequencer \in [Replicas -> SequencerType \union {None, Down}]
    /\ auxUsedValues \subseteq Values
    /\ auxAckOK \in BOOLEAN
    /\ auxHistory \in Seq(Values)

\*******************************************************************
\* Init and common actions
\*******************************************************************

CommonInit(firstSeq) ==
    /\ manifest = [version |-> 0, trimIndex |-> 0, snapshot |-> None,
                    loglets |-> <<[id |-> 1, first |-> 1, tail |-> 0, seq |-> firstSeq]>>]
    /\ rSequencer = [r \in Replicas |->
                        IF r = firstSeq
                        THEN [logletId |-> 1, slots |-> EmptySequencer] ELSE None]
    /\ entries = 1 :> EmptyEntries
    /\ sealbits = 1 :> FALSE
    /\ snapshots = <<>>
    /\ rManifest = [r \in Replicas |-> None]
    /\ auxUsedValues = {}
    /\ auxAckOK = TRUE
    /\ auxHistory = <<>>

(* ---------------------------------------------------------
    ACTION: CommonCrash

    Lose the replica's cached manifest and sequencer state.
    Durable objects and verification history are preserved.
-----------------------------------------------------------*)

CommonCrash(r) ==
    /\ rSequencer' = [rSequencer EXCEPT ![r] = Down]
    /\ rManifest' = [rManifest EXCEPT ![r] = None]
    /\ UNCHANGED <<storeVars, auxVars>>

=============================================================================
