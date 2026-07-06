------------------------------- MODULE HermesRB -------------------------------
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
     PerfectLink.
   - Crash semantics imported from the library's CrashStop module (Cachin's
     crash-stop process abstraction): a single failure-model value fm is
     consulted by every operator of both channels, so there is one source
     of truth for which nodes have crashed.
   - H_MAX_CRASHES constant added to expose the library's crash bound at
     the protocol level.
 ***************************************************************************)
EXTENDS     Integers,
            FiniteSets

CONSTANTS   H_NODES,
            H_WRITERS,
            H_MAX_VERSION,
            H_MAX_CRASHES

CS == INSTANCE CrashStop WITH MaxCrashes <- H_MAX_CRASHES
RB == INSTANCE ReliableBroadcast
PL == INSTANCE PerfectLink

VARIABLES   fm,
            nodeTS,
            nodeState,
            nodeRcvedAcks,
            nodeLastWriter,
            nodeLastWriteTS,
            nodeWriteEpochID,
            aliveNodes,
            epochID,
            channel,
            link

hvars == << channel, link, fm, nodeTS, nodeState, nodeRcvedAcks, nodeLastWriter,
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
    /\  channel          = RB!Channel({InvGroup, ValGroup}, H_NODES)
    /\  link             = PL!PerfectLink(H_NODES, H_NODES)
    /\  fm               = CS!CrashStop
    /\  epochID          = 0
    /\  aliveNodes       = H_NODES
    /\  nodeWriteEpochID = [n \in H_NODES |-> 0]
    /\  nodeRcvedAcks    = [n \in H_NODES |-> {}]
    /\  nodeState        = [n \in H_NODES |-> "valid"]
    /\  nodeLastWriter   = [n \in H_NODES |-> LowerNode]
    /\  nodeTS           = [n \in H_NODES |-> InitialTS]
    /\  nodeLastWriteTS  = [n \in H_NODES |-> InitialTS]

-------------------------------------------------------------------------------------
\* Shared update bundles

h_upd_state(n, newVersion, newTieBreaker, newState, newAcks) ==
    /\  nodeLastWriter'   = [nodeLastWriter   EXCEPT ![n] = n]
    /\  nodeRcvedAcks'    = [nodeRcvedAcks    EXCEPT ![n] = newAcks]
    /\  nodeState'        = [nodeState        EXCEPT ![n] = newState]
    /\  nodeWriteEpochID' = [nodeWriteEpochID EXCEPT ![n] = epochID]
    /\  nodeTS'           = [nodeTS           EXCEPT ![n].version    = newVersion,
                                                     ![n].tieBreaker = newTieBreaker]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS  EXCEPT ![n].version    = newVersion,
                                                     ![n].tieBreaker = newTieBreaker]

h_send_inv(n, newVersion, newTieBreaker) ==
    LET m == [type       |-> "INV",
              epochID    |-> epochID,
              sender     |-> n,
              version    |-> newVersion,
              tieBreaker |-> newTieBreaker]
    IN  channel' = RB!Broadcast(channel, fm, InvGroup, n, m)

h_actions_for_upd(n, newVersion, newTieBreaker, newState, newAcks) ==
    /\  h_upd_state(n, newVersion, newTieBreaker, newState, newAcks)
    /\  h_send_inv(n, newVersion, newTieBreaker)
    /\  UNCHANGED <<link, fm, aliveNodes, epochID>>


h_actions_for_upd_replay(n, acks) ==
    /\  h_actions_for_upd(n, nodeTS[n].version, nodeTS[n].tieBreaker, "replay", acks)

-------------------------------------------------------------------------------------
\* Coordinator

HRead(n) ==
    /\ nodeState[n] = "valid"
    /\ UNCHANGED hvars

HWrite(n) ==
    /\  n \in H_WRITERS
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
        /\ PL!HasMessage(link, fm, node, n)
        /\ \E m \in PL!Messages(link, fm, node, n) :
            /\ m.type    = "ACK"
            /\ m.epochID = epochID
            /\ m.sender /= n
            /\ m.sender \notin nodeRcvedAcks[n]
            /\ equalTS(m.version, m.tieBreaker,
                       nodeLastWriteTS[n].version,
                       nodeLastWriteTS[n].tieBreaker)
            /\ nodeState[n] \in {"write", "invalid_write", "replay"}
            /\ link'       = PL!Receive(link, fm, node, n, m)
            /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = @ \union {m.sender}]
            /\ UNCHANGED <<channel, fm,
                           nodeTS, nodeState, nodeLastWriter, nodeLastWriteTS,
                           nodeWriteEpochID, aliveNodes, epochID>>


HSendVals(n) ==
    /\ nodeState[n] \in {"write", "replay"}
    /\ receivedAllAcks(n)
    /\ nodeState'         = [nodeState EXCEPT![n] = "valid"]
    /\ LET m == [type       |-> "VAL",
                 version    |-> nodeTS[n].version,
                 tieBreaker |-> nodeTS[n].tieBreaker]
       IN  channel' = RB!Broadcast(channel, fm, ValGroup, n, m)
    /\ UNCHANGED <<link, fm, nodeTS, nodeLastWriter, nodeLastWriteTS,
                   aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>

HCoordinatorActions(n) ==
    \/ HRead(n)
    \/ HCoordWriteReplay(n)
    \/ HWrite(n)
    \/ HRcvAck(n)
    \/ HSendVals(n)

-------------------------------------------------------------------------------------
\* Follower

HRcvInv(n) ==  \* Process a received invalidation
    /\ RB!HasMessage(channel, fm, InvGroup, n)
    /\ \E m \in RB!Messages(channel, fm, InvGroup, n) :
        /\ m.type     = "INV"
        /\ m.epochID  = epochID
        /\ m.sender  /= n
        /\ channel' = RB!Deliver(channel, fm, InvGroup, n, m)
        /\ link'    = PL!Send(link, fm, n, m.sender,
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
        /\ UNCHANGED <<fm, nodeLastWriteTS, aliveNodes, nodeRcvedAcks, epochID, nodeWriteEpochID>>

HRcvVal(n) ==
    /\ RB!HasMessage(channel, fm, ValGroup, n)
    /\ \E m \in RB!Messages(channel, fm, ValGroup, n) :
        /\ m.type = "VAL"
        /\ nodeState[n] /= "valid"
        /\ equalTS(m.version, m.tieBreaker,
                   nodeTS[n].version, nodeTS[n].tieBreaker)
        /\ channel' = RB!Deliver(channel, fm, ValGroup, n, m)
        /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
        /\ UNCHANGED <<link, fm, nodeTS, nodeLastWriter, nodeLastWriteTS,
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
\* Node failure: record the crash once, in the shared failure model, and
\* bump the epoch. Both channels consult fm, so neither is touched here.

HNodeFailure(n) ==
    /\ Cardinality(aliveNodes) > 2
    /\ CS!CanCrash(fm)
    /\ nodeRcvedAcks' = [k \in H_NODES |-> {}]
    /\ aliveNodes'    = aliveNodes \ {n}
    /\ epochID'       = epochID + 1
    /\ fm'            = CS!Crash(fm, n)
    /\ UNCHANGED <<channel, link, nodeState, nodeTS, nodeLastWriter,
                   nodeLastWriteTS, nodeWriteEpochID>>

-------------------------------------------------------------------------------------

HNext == \* Hermes (read/write) protocol (Coordinator and Follower actions) + failures
    \E n \in aliveNodes:
            \/ HFollowerActions(n)
            \/ HCoordinatorActions(n)
            \/ HNodeFailure(n)


\* Fairness: weak fairness on every receive / replay action so that, once
\* such an action stays enabled, it eventually fires. No fairness on
\* HWrite (writers choose when to write) or HNodeFailure (failures are voluntary).
H_Fairness ==
    /\ \A n \in H_NODES: WF_hvars(HRcvInv(n))
    /\ \A n \in H_NODES: WF_hvars(HRcvAck(n))
    /\ \A n \in H_NODES: WF_hvars(HSendVals(n))
    /\ \A n \in H_NODES: WF_hvars(HRcvVal(n))
    /\ \A n \in H_NODES: WF_hvars(HCoordWriteReplay(n))
    /\ \A n \in H_NODES: WF_hvars(HFollowerWriteReplay(n))

H_Spec == HInit /\ [][HNext]_hvars /\ H_Fairness


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
    /\  fm.crashed      \subseteq H_NODES
    /\  epochID         \in 0..(Cardinality(H_NODES) - 1)
    /\  nodeWriteEpochID \in [H_NODES -> 0..(Cardinality(H_NODES) - 1)]


\* The consistent invariant: all alive nodes in valid state should have the same value / TS
HConsistent ==
    \A k,s \in aliveNodes:  \/ nodeState[k] /= "valid"
                            \/ nodeState[s] /= "valid"
                            \/ nodeTS[k] = nodeTS[s]

\* CRASH-STOP: the protocol-level membership view (aliveNodes) and the
\* library's failure model never diverge. Together with HNext drawing the
\* actor from aliveNodes, this is what guarantees a crashed node performs
\* no further action. Because the failure model is a single shared value,
\* both channels see exactly this set of crashes.
HCrashStop ==
    fm.crashed = (H_NODES \ aliveNodes)

\* PROPERTY (LIVENESS): every write started by a correct (non-crashing)
\* coordinator eventually commits. Includes writes taken over by followers
\* via write-replay after the original coordinator crashed. Cachin et al.,
\* "Introduction to Reliable and Secure Distributed Programming",
\* Termination pattern (Response under Globally).
PropertyWriteTermination ==
    \A n \in H_NODES:
        ([](n \in aliveNodes))
            => ((nodeState[n] \in {"write", "replay"}) ~> (nodeState[n] = "valid"))

THEOREM H_Spec =>([]HTypeOK) /\ ([]HConsistent) /\ ([]HCrashStop) /\ PropertyWriteTermination

=============================================================================
