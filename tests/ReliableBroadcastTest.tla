------------------------- MODULE ReliableBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE ReliableBroadcast

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
       /\ channel' = Broadcast(channel, "g1", p, msg)
       /\ counter' = counter + 1
       /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {msg}]
       /\ UNCHANGED <<received, receivedOrdered>>

ProcessReceive ==
  \E p \in Processes:
    /\ HasMessage(channel, "g1", p)
    /\ \E m \in Messages(channel, "g1", p):
      /\ channel' = Deliver(channel, "g1", p, m)
      /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
      /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], m)]
      /\ UNCHANGED <<counter, sent>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in Processes: ~HasMessage(channel, "g1", p)
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

\* Reliable Broadcast properties (Cachin, Guerraoui & Rodrigues)

\* (RB1 - Validity) If a correct process broadcasts m, it eventually delivers m.
PropertyValidity ==
  \A p \in Processes:
    \A m \in MessagesToSend:
      [](m \in sent[p] => <>(m \in received[p]))

\* (RB2 - No Duplication) No message is delivered more than once.
NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantNoDuplication ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])

\* (RB3 - No Creation) If a process delivers m, then m was previously broadcast by some process.
InvariantNoCreation ==
  \A p \in Processes:
    \A m \in received[p]:
      \E q \in Processes: m \in sent[q]

\* (RB4 - Agreement) If any correct process delivers m, every correct process eventually delivers m.
PropertyAgreement ==
  \A m \in MessagesToSend:
    \A p1 \in Processes:
      [](m \in received[p1] => \A p2 \in Processes: <>(m \in received[p2]))

=============================================================================
