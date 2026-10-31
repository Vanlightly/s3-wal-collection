-------------------------- MODULE ConfluxCheck --------------------------
EXTENDS Conflux

\* FOR CHECKING THE JAVA OVERRIDE IS EQUIVALENT OF TLA+

\* Original reconstruction expression, evaluated by TLC rather than Java.
\* Check it on every reachable state, including snapshots, gaps, stale
\* writers, reconfiguration, and deleted objects.
ReferenceLog ==
    LET lastIndex == GlobalIndex(GetActiveLogletRef(manifest), StoredTail(manifest)) - 1
    IN [i \in 1..lastIndex |->
            IF i <= manifest.trimIndex
            THEN snapshots[manifest.snapshot][i]
            ELSE LET lRef == GetLogletAt(manifest, i)
                 IN ReadEntry(lRef.id, i - lRef.first + 1)]

JavaMatchesTLA == RecoverableLog = ReferenceLog

=========================================================================
