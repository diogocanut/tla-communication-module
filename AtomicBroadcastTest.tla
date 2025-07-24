--------------------------- MODULE AtomicBroadcastTest ---------------------------
EXTENDS Integers, Sequences, TLC, AtomicBroadcast

CONSTANTS Groups, Processes, totalCounter

VARIABLES channel, counter, sent, received, receivedOrdered

vars == <<channel, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

Init ==
  channel = Channel(Groups, Processes)
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
      /\ received' = [received EXCEPT ![p] = received[p] \cup {UnwrapMessage(Message(channel, "g1", p))}]
      /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], UnwrapMessage(Message(channel, "g1", p)))]
      /\ channel' = Deliver(channel, "g1", p)
      /\ UNCHANGED <<counter, sent>>

Termination ==
  counter = totalCounter /\ channel["g1"]["p1"] = <<>> /\ channel["g1"]["p2"] = <<>>
  /\ UNCHANGED vars

Next ==
  \/ ProcessSend
  \/ ProcessReceive
  \/ Termination

Spec == Init /\ [][Next]_vars
             /\ WF_vars(Next)
             /\ SF_vars(ProcessSend)
             /\ SF_vars(ProcessReceive)


\* Broadcast properties

PropertyValidity ==
  \A p \in Processes:
    \A m \in MessagesToSend:
      [](m \in sent[p] => <>(m \in received[p]))

PropertyUniformAgreement ==
  \A m \in MessagesToSend:
    \A p1 \in Processes:
      [](m \in received[p1] => \A p2 \in Processes: <>(m \in received[p2]))

Delivered(p, m) ==
  \E i \in 1..Len(receivedOrdered[p]): receivedOrdered[p][i] = m

PropertyUniformIntegrity ==
  \A p \in Processes:
    \A m \in MessagesToSend:
      [](Delivered(p, m) => \E q \in Processes: m \in sent[q])


IndexOf(seq, m) ==
  CHOOSE i \in 1..Len(seq): seq[i] = m

DeliveredBefore(p, m1, m2) ==
  Delivered(p, m1) /\ Delivered(p, m2) /\
  IndexOf(receivedOrdered[p], m1) < IndexOf(receivedOrdered[p], m2)

PropertyUniformTotalOrder ==
  \A m1, m2 \in MessagesToSend:
    \A p1, p2 \in Processes:
      [](Delivered(p1, m1) /\ Delivered(p1, m2) /\ DeliveredBefore(p1, m1, m2)
         /\ Delivered(p2, m1) /\ Delivered(p2, m2)
         =>
         DeliveredBefore(p2, m1, m2))

NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantNoDuplicateDeliveries ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])


=============================================================================