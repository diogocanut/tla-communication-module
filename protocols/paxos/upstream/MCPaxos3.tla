------------------------------- MODULE MCPaxos3 -------------------------------
EXTENDS Paxos, FiniteSets, TLC
-----------------------------------------------------------------------------
CONSTANTS a1, a2, a3  \* acceptors
CONSTANTS v1, v2      \* Values
CONSTANT  MaxBallot

MCAcceptor == {a1, a2, a3}
MCValue    == {v1, v2}
MCQuorum   == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot   == 0..MaxBallot
MCSymmetry == Permutations(MCAcceptor) \cup Permutations(MCValue)

VotingSpecBar == V!Spec
InvOneChosen  == Cardinality(V!chosen) <= 1
=============================================================================
