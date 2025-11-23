------------------------- MODULE ReliableBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE ReliableBroadcast

CONSTANTS Groups, Processes, totalCounter

VARIABLES channel, counter


Init ==
  /\ channel = Channel(Groups, Processes)
  /\ counter = 0

Termination ==
  counter = totalCounter /\ channel.links["g1"]["p1"] = {} /\ channel.links["g1"]["p2"] = {}
  /\ UNCHANGED <<channel, counter>>

SendP1 ==
    /\ counter < totalCounter
    /\ channel' = Broadcast(channel, "g1", "p1", "m1")
    /\ counter' = counter + 1

SendP2 ==
    /\ counter < totalCounter
    /\ channel' = Broadcast(channel, "g1", "p2", "m1")
    /\ counter' = counter + 1

DeliverP1 ==
  \E p \in Processes:
    /\ HasMessage(channel, "g1", p)
    /\ \E m \in Messages(channel, "g1", p):
        /\ channel' = Deliver(channel, "g1", p, m)
    /\ UNCHANGED counter

Next ==
  \/ SendP1
  \/ SendP2
  \/ DeliverP1
  \/ Termination

Spec == Init /\ [][Next]_<<channel, counter>>


=============================================================================
