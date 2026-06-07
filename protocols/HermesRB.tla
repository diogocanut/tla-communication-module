------------------------------ MODULE HermesRB ------------------------------
(***************************************************************************
 Modified version of the Hermes TLA+ specification by Katsarakis et al.

 Original: https://github.com/ease-lab/Hermes
 Paper:    Antonios Katsarakis, Vasilis Gavrielatos, M.R. Siavash
           Katebzadeh, Arpit Joshi, Aleksandar Dragojevic, Boris Grot,
           and Vijay Nagarajan. "Hermes: A Fast, Fault-Tolerant and
           Linearizable Replication Protocol." Proceedings of the
           Twenty-Fifth International Conference on Architectural Support
           for Programming Languages and Operating Systems (ASPLOS),
           ACM, 2020, pp. 201-217.
 License:  Apache License 2.0 (see upstream repository).

 Modifications from the original:
   - Communication primitives reworked over the TLA+ communication module
     library: INV and VAL routed through ReliableBroadcast, ACK through
     PerfectLink, replacing the flat global msgs set.
   - Crash semantics imported from the library (RB and PerfectLink share
     a uniform Crash / IsCrashed / CanCrash interface).
   - H_MAX_CRASHES constant added to expose the library's crash bound at
     the protocol level.
 ***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS H_NODES,
          H_MAX_VERSION,
          H_MAX_CRASHES

RB == INSTANCE ReliableBroadcast WITH MaxCrashes <- H_MAX_CRASHES
PL == INSTANCE PerfectLink       WITH MaxCrashes <- H_MAX_CRASHES

VARIABLES
    invChan,         \* RB channel carrying INV messages
    valChan,         \* RB channel carrying VAL messages
    ackLink,         \* PerfectLink carrying ACK messages
    nodeTS,
    nodeState,
    nodeRcvedAcks,
    nodeLastWriter,
    nodeLastWriteTS,
    nodeWriteEpochID,
    aliveNodes,
    epochID

hvars == << invChan, valChan, ackLink,
            nodeTS, nodeState, nodeRcvedAcks, nodeLastWriter,
            nodeLastWriteTS, nodeWriteEpochID, aliveNodes, epochID >>

InvGroup == "inv"
ValGroup == "val"

-------------------------------------------------------------------------------------

HMessage ==
    [type: {"INV"}, sender    : H_NODES,
                    epochID   : 0..(Cardinality(H_NODES) - 1),
                    version   : 0..H_MAX_VERSION,
                    tieBreaker: H_NODES]
    \union
    [type: {"ACK"}, sender    : H_NODES,
                    epochID   : 0..(Cardinality(H_NODES) - 1),
                    version   : 0..H_MAX_VERSION,
                    tieBreaker: H_NODES]
    \union
    [type: {"VAL"}, version   : 0..H_MAX_VERSION,
                    tieBreaker: H_NODES]

MinNode == CHOOSE k \in H_NODES: \A m \in H_NODES: k <= m

ZeroTS == [version |-> 0, tieBreaker |-> MinNode]

-------------------------------------------------------------------------------------

equalTS(v1, tb1, v2, tb2) ==
    /\ v1 = v2
    /\ tb1 = tb2

greaterTS(v1, tb1, v2, tb2) ==
    \/ v1 > v2
    \/ /\ v1 = v2
       /\ tb1 > tb2

isAlive(n) == n \in aliveNodes

receivedAllAcks(n) == (aliveNodes \ {n}) \subseteq nodeRcvedAcks[n]

-------------------------------------------------------------------------------------

HInit ==
    /\ invChan          = RB!Channel({InvGroup}, H_NODES)
    /\ valChan          = RB!Channel({ValGroup}, H_NODES)
    /\ ackLink          = PL!PerfectLink(H_NODES, H_NODES)
    /\ epochID          = 0
    /\ aliveNodes       = H_NODES
    /\ nodeWriteEpochID = [n \in H_NODES |-> 0]
    /\ nodeRcvedAcks    = [n \in H_NODES |-> {}]
    /\ nodeState        = [n \in H_NODES |-> "valid"]
    /\ nodeLastWriter   = [n \in H_NODES |-> MinNode]
    /\ nodeTS           = [n \in H_NODES |-> ZeroTS]
    /\ nodeLastWriteTS  = [n \in H_NODES |-> ZeroTS]

-------------------------------------------------------------------------------------
\* Shared update bundles.

h_upd_state(n, newVersion, newTieBreaker, newState, newAcks) ==
    /\ nodeLastWriter'   = [nodeLastWriter   EXCEPT ![n] = n]
    /\ nodeRcvedAcks'    = [nodeRcvedAcks    EXCEPT ![n] = newAcks]
    /\ nodeState'        = [nodeState        EXCEPT ![n] = newState]
    /\ nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID]
    /\ nodeTS'           = [nodeTS           EXCEPT ![n].version    = newVersion,
                                                    ![n].tieBreaker = newTieBreaker]
    /\ nodeLastWriteTS'  = [nodeLastWriteTS  EXCEPT ![n].version    = newVersion,
                                                    ![n].tieBreaker = newTieBreaker]

h_send_inv(n, newVersion, newTieBreaker) ==
    LET m == [type       |-> "INV",
              epochID    |-> epochID,
              sender     |-> n,
              version    |-> newVersion,
              tieBreaker |-> newTieBreaker]
    IN  invChan' = RB!Broadcast(invChan, InvGroup, n, m)

h_actions_for_upd(n, newVersion, newTieBreaker, newState, newAcks) ==
    /\ h_upd_state(n, newVersion, newTieBreaker, newState, newAcks)
    /\ h_send_inv(n, newVersion, newTieBreaker)
    /\ UNCHANGED <<valChan, ackLink, aliveNodes, epochID>>

h_actions_for_upd_replay(n, acks) ==
    h_actions_for_upd(n, nodeTS[n].version, nodeTS[n].tieBreaker, "replay", acks)

-------------------------------------------------------------------------------------
\* Coordinator actions.

HRead(n) ==
    /\ nodeState[n] = "valid"
    /\ UNCHANGED hvars

HWrite(n) ==
    /\ nodeState[n] = "valid"
    /\ nodeTS[n].version < H_MAX_VERSION
    /\ h_actions_for_upd(n, nodeTS[n].version + 1, n, "write", {})

HCoordWriteReplay(n) ==
    /\ nodeState[n] \in {"write", "replay"}
    /\ nodeWriteEpochID[n] < epochID
    /\ ~receivedAllAcks(n)
    /\ h_actions_for_upd_replay(n, nodeRcvedAcks[n])

HRcvAck(n) ==
    \E sndr \in H_NODES :
        /\ PL!HasMessage(ackLink, sndr, n)
        /\ \E m \in PL!Messages(ackLink, sndr, n) :
            /\ m.type    = "ACK"
            /\ m.epochID = epochID
            /\ m.sender /= n
            /\ m.sender \notin nodeRcvedAcks[n]
            /\ equalTS(m.version, m.tieBreaker,
                       nodeLastWriteTS[n].version,
                       nodeLastWriteTS[n].tieBreaker)
            /\ nodeState[n] \in {"write", "invalid_write", "replay"}
            /\ ackLink'       = PL!Receive(ackLink, sndr, n, m)
            /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = @ \union {m.sender}]
            /\ UNCHANGED <<invChan, valChan,
                           nodeTS, nodeState, nodeLastWriter, nodeLastWriteTS,
                           nodeWriteEpochID, aliveNodes, epochID>>

HSendVals(n) ==
    /\ nodeState[n] \in {"write", "replay"}
    /\ receivedAllAcks(n)
    /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
    /\ LET m == [type       |-> "VAL",
                 version    |-> nodeTS[n].version,
                 tieBreaker |-> nodeTS[n].tieBreaker]
       IN  valChan' = RB!Broadcast(valChan, ValGroup, n, m)
    /\ UNCHANGED <<invChan, ackLink, nodeTS, nodeLastWriter, nodeLastWriteTS,
                   nodeRcvedAcks, nodeWriteEpochID, aliveNodes, epochID>>

HCoordinatorActions(n) ==
    \/ HRead(n)
    \/ HCoordWriteReplay(n)
    \/ HWrite(n)
    \/ HRcvAck(n)
    \/ HSendVals(n)

-------------------------------------------------------------------------------------
\* Follower actions.

HRcvInv(n) ==
    /\ RB!HasMessage(invChan, InvGroup, n)
    /\ \E m \in RB!Messages(invChan, InvGroup, n) :
        /\ m.type    = "INV"
        /\ m.epochID = epochID
        /\ m.sender /= n
        /\ invChan' = RB!Deliver(invChan, InvGroup, n, m)
        /\ ackLink' = PL!Send(ackLink, n, m.sender,
                              [type       |-> "ACK",
                               sender     |-> n,
                               epochID    |-> epochID,
                               version    |-> m.version,
                               tieBreaker |-> m.tieBreaker])
        /\ IF greaterTS(m.version, m.tieBreaker,
                        nodeTS[n].version, nodeTS[n].tieBreaker)
           THEN /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
                /\ nodeTS'         = [nodeTS         EXCEPT ![n].version    = m.version,
                                                            ![n].tieBreaker = m.tieBreaker]
                /\ IF nodeState[n] \in {"valid", "invalid", "replay"}
                   THEN nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                   ELSE nodeState' = [nodeState EXCEPT ![n] = "invalid_write"]
           ELSE UNCHANGED <<nodeState, nodeTS, nodeLastWriter>>
        /\ UNCHANGED <<valChan, nodeLastWriteTS, nodeRcvedAcks,
                       nodeWriteEpochID, aliveNodes, epochID>>

HRcvVal(n) ==
    /\ RB!HasMessage(valChan, ValGroup, n)
    /\ \E m \in RB!Messages(valChan, ValGroup, n) :
        /\ m.type = "VAL"
        /\ nodeState[n] /= "valid"
        /\ equalTS(m.version, m.tieBreaker,
                   nodeTS[n].version, nodeTS[n].tieBreaker)
        /\ valChan'   = RB!Deliver(valChan, ValGroup, n, m)
        /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
        /\ UNCHANGED <<invChan, ackLink, nodeTS, nodeLastWriter, nodeLastWriteTS,
                       nodeRcvedAcks, nodeWriteEpochID, aliveNodes, epochID>>

HFollowerWriteReplay(n) ==
    /\ nodeState[n] \in {"invalid", "invalid_write"}
    /\ ~isAlive(nodeLastWriter[n])
    /\ h_actions_for_upd_replay(n, {})

HFollowerActions(n) ==
    \/ HRcvInv(n)
    \/ HFollowerWriteReplay(n)
    \/ HRcvVal(n)

-------------------------------------------------------------------------------------
\* Node failure: mark crashed across all three channels and bump epoch.

HNodeFailure(n) ==
    /\ Cardinality(aliveNodes) > 2
    /\ RB!CanCrash(invChan)
    /\ aliveNodes'    = aliveNodes \ {n}
    /\ epochID'       = epochID + 1
    /\ nodeRcvedAcks' = [k \in H_NODES |-> {}]
    /\ invChan'       = RB!Crash(invChan, n)
    /\ valChan'       = RB!Crash(valChan, n)
    /\ ackLink'       = PL!Crash(ackLink, n)
    /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter,
                   nodeLastWriteTS, nodeWriteEpochID>>

-------------------------------------------------------------------------------------

HNext ==
    \E n \in aliveNodes :
        \/ HCoordinatorActions(n)
        \/ HFollowerActions(n)
        \/ HNodeFailure(n)

H_Spec == HInit /\ [][HNext]_hvars

-------------------------------------------------------------------------------------
\* The consistent invariant: all alive nodes in valid state agree on the TS.

HConsistent ==
    \A k, s \in aliveNodes :
        \/ nodeState[k] /= "valid"
        \/ nodeState[s] /= "valid"
        \/ nodeTS[k] = nodeTS[s]

HTypeOK ==
    /\ \A n \in H_NODES :
         nodeRcvedAcks[n] \subseteq (H_NODES \ {n})
    /\ nodeLastWriter   \in [H_NODES -> H_NODES]
    /\ nodeLastWriteTS  \in [H_NODES -> [version    : 0..H_MAX_VERSION,
                                         tieBreaker : H_NODES]]
    /\ nodeTS           \in [H_NODES -> [version    : 0..H_MAX_VERSION,
                                         tieBreaker : H_NODES]]
    /\ nodeState        \in [H_NODES -> {"valid", "invalid", "invalid_write",
                                         "write", "replay"}]
    /\ aliveNodes       \subseteq H_NODES
    /\ epochID          \in 0..(Cardinality(H_NODES) - 1)
    /\ nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)]

THEOREM H_Spec => ([]HTypeOK) /\ ([]HConsistent)

=============================================================================
