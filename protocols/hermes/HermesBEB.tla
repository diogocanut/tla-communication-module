------------------------------- MODULE HermesBEB ------------------------------
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
     library: INV and VAL routed through BestEffortBroadcast, ACK through
     PerfectLink.
   - Crash semantics imported from the library (BEB and PerfectLink share
     a uniform Crash / IsCrashed / CanCrash interface).
   - H_MAX_CRASHES constant added to expose the library's crash bound at
     the protocol level.
 ***************************************************************************)
EXTENDS     Integers,
            FiniteSets

CONSTANTS   H_NODES,
            H_MAX_VERSION,
            H_MAX_CRASHES

BEB == INSTANCE BestEffortBroadcast WITH MaxCrashes <- H_MAX_CRASHES
PL  == INSTANCE PerfectLink         WITH MaxCrashes <- H_MAX_CRASHES

VARIABLES   nodeTS,
            nodeState,
            nodeRcvedAcks,
            nodeLastWriter,
            nodeLastWriteTS,
            nodeWriteEpochID,
            aliveNodes,
            epochID,
            channel,
            link

hvars == << channel, link, nodeTS, nodeState, nodeRcvedAcks, nodeLastWriter,
            nodeLastWriteTS, nodeWriteEpochID, aliveNodes, epochID >>

InvGroup == "inv"
ValGroup == "val"

-------------------------------------------------------------------------------------

HMessage ==
    [type: {"INV", "ACK"}, sender    : H_NODES,
                           epochID   : 0..(Cardinality(H_NODES) - 1),
                           version   : 0..H_MAX_VERSION,
                           tieBreaker: H_NODES]
        \union
    [type: {"VAL"},        version   : 0..H_MAX_VERSION,
                           tieBreaker: H_NODES]

LowerNode == CHOOSE k \in H_NODES: \A m \in H_NODES: k <= m

InitialTS == [version |-> 0, tieBreaker |-> LowerNode]

-------------------------------------------------------------------------------------

receivedAllAcks(n) == (aliveNodes \ {n}) \subseteq nodeRcvedAcks[n]

equalTS(v1,tb1,v2,tb2) ==
    /\ v1 = v2
    /\ tb1 = tb2

greaterTS(v1,tb1,v2,tb2) ==
    \/ v1 > v2
    \/ /\   v1 = v2
       /\  tb1 > tb2

isAlive(n) == n \in aliveNodes

-------------------------------------------------------------------------------------

HInit ==
    /\  channel          = BEB!Channel({InvGroup, ValGroup}, H_NODES)
    /\  link             = PL!PerfectLink(H_NODES, H_NODES)
    /\  epochID          = 0
    /\  aliveNodes       = H_NODES
    /\  nodeWriteEpochID = [n \in H_NODES |-> 0]
    /\  nodeRcvedAcks    = [n \in H_NODES |-> {}]
    /\  nodeState        = [n \in H_NODES |-> "valid"]
    /\  nodeLastWriter   = [n \in H_NODES |-> LowerNode]
    /\  nodeTS           = [n \in H_NODES |-> InitialTS]
    /\  nodeLastWriteTS  = [n \in H_NODES |-> InitialTS]

-------------------------------------------------------------------------------------
\* Shared update bundles.

h_upd_state(n, newVersion, newTieBreaker, newState, newAcks) ==
    /\  nodeLastWriter'   = [nodeLastWriter   EXCEPT ![n] = n]
    /\  nodeRcvedAcks'    = [nodeRcvedAcks    EXCEPT ![n] = newAcks]
    /\  nodeState'        = [nodeState        EXCEPT ![n] = newState]
    /\  nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID]
    /\  nodeTS'           = [nodeTS           EXCEPT ![n].version    = newVersion,
                                                     ![n].tieBreaker = newTieBreaker]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS  EXCEPT ![n].version    = newVersion,
                                                     ![n].tieBreaker = newTieBreaker]

\* BEB!Broadcast returns a SET of next states (one per subset of alive
\* receivers), so we existentially quantify over it.
h_send_inv(n, newVersion, newTieBreaker) ==
    LET m == [type       |-> "INV",
              epochID    |-> epochID,
              sender     |-> n,
              version    |-> newVersion,
              tieBreaker |-> newTieBreaker]
    IN  \E next \in BEB!Broadcast(channel, InvGroup, n, m) : channel' = next

h_actions_for_upd(n, newVersion, newTieBreaker, newState, newAcks) ==
    /\  h_upd_state(n, newVersion, newTieBreaker, newState, newAcks)
    /\  h_send_inv(n, newVersion, newTieBreaker)
    /\  UNCHANGED <<link, aliveNodes, epochID>>


h_actions_for_upd_replay(n, acks) ==
    /\  h_actions_for_upd(n, nodeTS[n].version, nodeTS[n].tieBreaker, "replay", acks)

-------------------------------------------------------------------------------------
\* Coordinator

HRead(n) ==
    /\ nodeState[n] = "valid"
    /\ UNCHANGED hvars

HWrite(n) ==
    /\  nodeState[n]      \in {"valid"}
    /\  nodeTS[n].version < H_MAX_VERSION \* Only to configurably terminate the model checking
    /\  h_actions_for_upd(n, nodeTS[n].version + 1, n, "write", {})


HCoordWriteReplay(n) ==
    /\  nodeState[n] \in {"write", "replay"}
    /\  nodeWriteEpochID[n] < epochID
    /\  ~receivedAllAcks(n)
    /\  h_actions_for_upd_replay(n, nodeRcvedAcks[n])


HRcvAck(n) ==
    \E node \in H_NODES :
        /\ PL!HasMessage(link, node, n)
        /\ \E m \in PL!Messages(link, node, n) :
            /\ m.type    = "ACK"
            /\ m.epochID = epochID
            /\ m.sender /= n
            /\ m.sender \notin nodeRcvedAcks[n]
            /\ equalTS(m.version, m.tieBreaker,
                       nodeLastWriteTS[n].version,
                       nodeLastWriteTS[n].tieBreaker)
            /\ nodeState[n] \in {"write", "invalid_write", "replay"}
            /\ link'       = PL!Receive(link, node, n, m)
            /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = @ \union {m.sender}]
            /\ UNCHANGED <<channel,
                           nodeTS, nodeState, nodeLastWriter, nodeLastWriteTS,
                           nodeWriteEpochID, aliveNodes, epochID>>


HSendVals(n) ==
    /\ nodeState[n] \in {"write", "replay"}
    /\ receivedAllAcks(n)
    /\ nodeState'         = [nodeState EXCEPT![n] = "valid"]
    /\ LET m == [type       |-> "VAL",
                 version    |-> nodeTS[n].version,
                 tieBreaker |-> nodeTS[n].tieBreaker]
       IN  \E next \in BEB!Broadcast(channel, ValGroup, n, m) : channel' = next
    /\ UNCHANGED <<link, nodeTS, nodeLastWriter, nodeLastWriteTS,
                   aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>

HCoordinatorActions(n) ==
    \/ HRead(n)
    \/ HCoordWriteReplay(n) \* After failures
    \/ HWrite(n)
    \/ HRcvAck(n)
    \/ HSendVals(n)

-------------------------------------------------------------------------------------
\* Follower

HRcvInv(n) ==  \* Process a received invalidation
    /\ BEB!HasMessage(channel, InvGroup, n)
    /\ \E m \in BEB!Messages(channel, InvGroup, n) :
        /\ m.type     = "INV"
        /\ m.epochID  = epochID
        /\ m.sender  /= n
        /\ channel' = BEB!Deliver(channel, InvGroup, n, m)
        /\ link'    = PL!Send(link, n, m.sender,
                                [type       |-> "ACK",
                                 sender     |-> n,
                                 epochID    |-> epochID,
                                 version    |-> m.version,
                                 tieBreaker |-> m.tieBreaker])
        /\ IF greaterTS(m.version, m.tieBreaker,
                        nodeTS[n].version, nodeTS[n].tieBreaker)
           THEN   /\ nodeLastWriter' = [nodeLastWriter EXCEPT ![n] = m.sender]
                  /\ nodeTS'         = [nodeTS         EXCEPT ![n].version    = m.version,
                                                              ![n].tieBreaker = m.tieBreaker]
                  /\ IF nodeState[n] \in {"valid", "invalid", "replay"}
                     THEN nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                     ELSE nodeState' = [nodeState EXCEPT ![n] = "invalid_write"]
           ELSE
                  UNCHANGED <<nodeState, nodeTS, nodeLastWriter, nodeWriteEpochID>>
        /\ UNCHANGED <<nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>

HRcvVal(n) ==
    /\ BEB!HasMessage(channel, ValGroup, n)
    /\ \E m \in BEB!Messages(channel, ValGroup, n) :
        /\ m.type = "VAL"
        /\ nodeState[n] /= "valid"
        /\ equalTS(m.version, m.tieBreaker,
                   nodeTS[n].version, nodeTS[n].tieBreaker)
        /\ channel' = BEB!Deliver(channel, ValGroup, n, m)
        /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
        /\ UNCHANGED <<link, nodeTS, nodeLastWriter, nodeLastWriteTS,
                       nodeRcvedAcks, nodeWriteEpochID, aliveNodes, epochID>>

HFollowerWriteReplay(n) ==
    /\  nodeState[n] \in {"invalid", "invalid_write"}
    /\  ~isAlive(nodeLastWriter[n])
    /\  h_actions_for_upd_replay(n, {})


HFollowerActions(n) ==
    \/ HRcvInv(n)
    \/ HFollowerWriteReplay(n)
    \/ HRcvVal(n)

-------------------------------------------------------------------------------------
\* Node failure: mark crashed on the broadcast channel and the ack link,
\* and bump epoch.

HNodeFailure(n) ==
    /\ Cardinality(aliveNodes) > 2
    /\ BEB!CanCrash(channel)
    /\ PL!CanCrash(link)
    /\ nodeRcvedAcks' = [k \in H_NODES |-> {}]
    /\ aliveNodes'    = aliveNodes \ {n}
    /\ epochID'       = epochID + 1
    /\ channel'       = BEB!Crash(channel, n)
    /\ link'          = PL!Crash(link, n)
    /\ UNCHANGED <<nodeState, nodeTS, nodeLastWriter,
                   nodeLastWriteTS, nodeWriteEpochID>>

-------------------------------------------------------------------------------------

HNext == \* Hermes (read/write) protocol (Coordinator and Follower actions) + failures
    \E n \in aliveNodes:
            \/ HFollowerActions(n)
            \/ HCoordinatorActions(n)
            \/ HNodeFailure(n)


H_Spec == HInit /\ [][HNext]_hvars


-------------------------------------------------------------------------------------
HTypeOK ==  \* The type correctness invariant
    /\ \A n \in H_NODES: nodeRcvedAcks[n] \subseteq (H_NODES \ {n})
    /\  nodeLastWriter  \in [H_NODES -> H_NODES]
    /\  nodeLastWriteTS \in [H_NODES -> [version   : 0..H_MAX_VERSION,
                                       tieBreaker: H_NODES         ]]
    /\  nodeTS          \in [H_NODES -> [version   : 0..H_MAX_VERSION,
                                       tieBreaker: H_NODES         ]]
    /\  nodeState       \in [H_NODES -> {"valid", "invalid", "invalid_write",
                                         "write", "replay"}]
    /\  aliveNodes      \subseteq H_NODES
    /\  epochID         \in 0..(Cardinality(H_NODES) - 1)
    /\  nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)]


\* The consistent invariant: all alive nodes in valid state should have the same value / TS
HConsistent ==
    \A k,s \in aliveNodes:  \/ nodeState[k] /= "valid"
                            \/ nodeState[s] /= "valid"
                            \/ nodeTS[k] = nodeTS[s]

THEOREM H_Spec =>([]HTypeOK) /\ ([]HConsistent)

=============================================================================
