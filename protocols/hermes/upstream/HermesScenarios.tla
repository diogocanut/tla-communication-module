--------------------------- MODULE HermesScenarios ---------------------------
(***************************************************************************
 Scenario harness over the UNMODIFIED upstream Hermes specification
 (Katsarakis et al., ASPLOS 2020, https://github.com/ease-lab/Hermes,
 Apache License 2.0; Hermes.tla in this directory is a verbatim copy).

 The harness EXTENDS Hermes and re-assembles its next-state relation from
 the original actions, adding only the two scenario dials used for
 HermesRB: S_WRITERS restricts which nodes may issue writes, and
 S_MAX_CRASHES bounds node failures. With S_WRITERS = H_NODES and
 S_MAX_CRASHES = 1 on three nodes, S_Spec has exactly the behaviors of the
 upstream H_Spec (the upstream Cardinality(aliveNodes) > 2 guard already
 limits three nodes to one crash).

 The upstream specification states no fairness and no liveness property,
 so each scenario checks only its two safety invariants, HTypeOK and
 HConsistent.
 ***************************************************************************)
EXTENDS Hermes

CONSTANTS S_WRITERS, S_MAX_CRASHES

SNext ==
    \E n \in aliveNodes:
        \/ HRead(n)
        \/ /\ n \in S_WRITERS
           /\ HWrite(n)
        \/ HCoordWriteReplay(n)
        \/ HRcvAck(n)
        \/ HSendVals(n)
        \/ HRcvInv(n)
        \/ HFollowerWriteReplay(n)
        \/ HRcvVal(n)
        \/ /\ Cardinality(H_NODES \ aliveNodes) < S_MAX_CRASHES
           /\ nodeFailure(n)

S_Spec == HInit /\ [][SNext]_hvars

=============================================================================
