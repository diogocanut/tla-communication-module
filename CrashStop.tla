------------------------------- MODULE CrashStop -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT MaxCrashes


CrashStop == [crashed |-> {}]

IsCrashed(fm, process) ==
    process \in fm.crashed

CanCrash(fm) ==
    Cardinality(fm.crashed) < MaxCrashes

Crash(fm, process) ==
    [fm EXCEPT !.crashed = fm.crashed \union {process}]

=============================================================================
