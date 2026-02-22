------------------------- MODULE BestEffortBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE BestEffortBroadcast WITH MaxDrops <- 2

CONSTANTS Groups, Processes, totalCounter

VARIABLES channel, counter, sent, received, receivedOrdered

vars == <<channel, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

Init ==
  /\ channel = Channel(Groups, Processes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]

ProcessSend ==
  \E p \in Processes:
    /\ counter < totalCounter
    /\ LET msg == counter + 1 IN
       /\ channel' \in Broadcast(channel, "g1", p, msg)
       /\ counter' = counter + 1
       /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {msg}]
       /\ UNCHANGED <<received, receivedOrdered>>

ProcessReceive ==
  \E p \in Processes:
    \E m \in Messages(channel, "g1", p):
      /\ channel' = Deliver(channel, "g1", p, m)
      /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
      /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], m)]
      /\ UNCHANGED <<counter, sent>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in Processes: Messages(channel, "g1", p) = {}
  /\ UNCHANGED vars

Next ==
  \/ ProcessSend
  \/ ProcessReceive
  \/ Termination

Spec ==
  Init /\ [][Next]_vars
       /\ WF_vars(Next)
       /\ SF_vars(ProcessSend)
       /\ SF_vars(ProcessReceive)

\* Best-Effort Broadcast properties (Cachin, Guerraoui & Rodrigues)

\* (BEB1 - Validity) If a correct process broadcasts m, every correct process eventually delivers m.
\* Note: Not checkable in this model — BestEffortBroadcast allows message drops (up to MaxDrops),
\* so delivery is not guaranteed. Use ReliableBroadcast for delivery guarantees.

\* (BEB2 - No Duplication) No message is delivered more than once.
NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantNoDuplication ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])

\* (BEB3 - No Creation) If a process delivers m, then m was previously broadcast by some process.
InvariantNoCreation ==
  \A p \in Processes:
    \A m \in received[p]:
      \E q \in Processes: m \in sent[q]

=============================================================================
