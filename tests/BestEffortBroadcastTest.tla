------------------------- MODULE BestEffortBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE BestEffortBroadcast WITH MaxDrops <- 2

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
  /\ channel' \in Broadcast(channel, "g1", "p1", "m1")
  /\ counter' = counter + 1

SendP2 ==
  /\ counter < totalCounter
  /\ channel' \in Broadcast(channel, "g1", "p2", "m1")
  /\ counter' = counter + 1

DeliverOne ==
  \E p \in Processes:
    \E m \in Messages(channel, "g1", p):
        /\ channel' = Deliver(channel, "g1", p, m)
        /\ UNCHANGED <<counter>>

Next ==
  \/ SendP1
  \/ SendP2
  \/ DeliverOne
  \/ Termination

Spec == Init /\ [][Next]_<<channel, counter>>

=============================================================================
