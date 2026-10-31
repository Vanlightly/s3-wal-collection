---------------- MODULE Conflux ----------------

(*
    Conflux modeled as a set of replicas, where each replica
    has 4 tasks (append, apply, gc, reconfiguration), and
    operate over object storage (only durable state is object
    storage).

    The real Conflux is a metadata service in Confluent's Kora 2
    architecture, and is built as a multi-master state-machine 
    replication service designed around Virtual Consensus and
    LogDrive concepts. It uses a shared log to agree on a sequence
    of commands that are applied to its machine state. The 
    machine state itself is related to sequencing and metadata 
    lookups for Kafka workloads. This spec does not model the 
    application model (Kafka workload metadata), but the underlying
    shared log protocol, which can run on diverse storage, including
    entirely on S3.

    This spec is split up into the following TLA+ files:
    * Conflux.tla -> Parent spec, Next, Spec
    * ConfluxAppend.tla -> Append task
    * ConfluxApply.tla -> Log read/state machine apply task
    * ConfluxGC.tla -> Garbage collection (prefix trim) task
    * ConfluxReconf.tla -> Log reconfiguration task
    * ConfluxCommon -> constants, shared variables, helpers, data model, typeok
    * ConfluxProperties -> Safety and liveness properties
*)

EXTENDS ConfluxApply, ConfluxAppend, ConfluxReconf,
        ConfluxGC, ConfluxProperties

replicaVars == <<serviceVars, rApply, rAppend, rGC, rReconf>>
vars == <<storeVars, replicaVars, auxVars>>

(* ---------------------------------------------------------
    ACTION: Init

    Choose the first sequencer, initialize shared state,
    and initialize all four tasks on every replica.
-----------------------------------------------------------*)

Init ==
    /\ \E firstSeq \in Replicas : CommonInit(firstSeq)
    /\ ApplyInit
    /\ AppendInit
    /\ GCInit
    /\ ReconfInit

(* ---------------------------------------------------------
    ACTION: CrashReplica

    On the given replica, reset all tasks, discard the manifest
    cache, and lose its sequencer (if it has one). Durable 
    objects on S3 and verification history survive.
-----------------------------------------------------------*)

CrashReplica(r) ==
    /\ FailuresEnabled
    /\ CommonCrash(r)
    /\ ApplyCrash(r)
    /\ AppendCrash(r)
    /\ GCCrash(r)
    /\ ReconfCrash(r)

(* ---------------------------------------------------------
    Next, Fairness, Spec
-----------------------------------------------------------*)

Next ==
    \E r \in Replicas :
        \* Apply task: reader protocol and state-machine application layer
        \/ RefreshManifest(r)
        \/ LoadSnapshot(r)
        \/ FastCheckTail(r)
        \/ FastCheckTailResponse(r)
        \/ CheckSealBeforeRead(r)
        \/ ReadNext(r)
        \* Append operation actions
        \/ \E v \in Values : AcceptWrite(r, v)
        \/ AcquireSlot(r)
        \/ WriteValue(r)
        \/ CompleteSlot(r)
        \/ CheckSealBeforeAck(r)
        \/ AppendTimeout(r)
        \/ CheckManifest(r)
        \* Reconfiguration actions
        \/ StartReconfig(r)
        \/ Seal(r)
        \/ SlowCheckTail(r)
        \/ FinishSlowCheckTail(r)
        \/ CommitReconfig(r)
        \* GC/prefixTrim actions
        \/ StartPrefixTrim(r)
        \/ CommitPrefixTrim(r)
        \/ CrashReplica(r)
        \/ \E slot \in Slots, lId \in LogletIds : 
            CollectEntry(r, lId, slot)

Fairness ==
    \A r \in Replicas :
        /\ WF_vars(Seal(r))
        /\ WF_vars(SlowCheckTail(r))
        /\ WF_vars(FinishSlowCheckTail(r))
        /\ WF_vars(CommitReconfig(r))
        /\ WF_vars(CommitPrefixTrim(r))

Spec == Init /\ [][Next]_vars

LivenessSpec == Spec /\ Fairness

=============================================================================
