------------------------------- MODULE CrashStop -------------------------------
EXTENDS Naturals, FiniteSets

CrashStop(maxCrashes) ==
    [crashed |-> {}, max |-> maxCrashes]

IsCrashed(fm, process) ==
    process \in fm.crashed

CanCrash(fm) ==
    Cardinality(fm.crashed) < fm.max

Crash(fm, process) ==
    [fm EXCEPT !.crashed = fm.crashed \union {process}]

=============================================================================
