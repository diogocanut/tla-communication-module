------------------------ MODULE PerfectLinkFIFOTest ------------------------
EXTENDS Integers, Sequences, TLC, PerfectLinkFIFO

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, receivedOrdered, sentTo, receivedFrom

vars == <<link, counter, sent, received, receivedOrdered, sentTo, receivedFrom>>

MessagesToSend == 1 .. totalCounter

Init ==
  /\ link = PerfectLinkFIFO(Processes, Processes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]
  /\ sentTo = [s \in Processes |-> [r \in Processes |-> <<>>]]
  /\ receivedFrom = [r \in Processes |-> [s \in Processes |-> <<>>]]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ counter < totalCounter
      /\ LET msg == counter + 1 IN
         /\ link' = Send(link, s, r, msg)
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![s] = sent[s] \cup {msg}]
         /\ sentTo' = [sentTo EXCEPT ![s][r] = Append(sentTo[s][r], msg)]
         /\ UNCHANGED <<received, receivedOrdered, receivedFrom>>

ProcessReceive ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ HasMessage(link, s, r)
      /\ \E m \in Messages(link, s, r):
          /\ link' = Receive(link, s, r)
          /\ received' =
               [received EXCEPT ![r] =
                  received[r] \cup {m}]
          /\ receivedOrdered' =
               [receivedOrdered EXCEPT ![r] =
                  Append(receivedOrdered[r], m)]
          /\ receivedFrom' =
               [receivedFrom EXCEPT ![r][s] =
                  Append(receivedFrom[r][s], m)]
          /\ UNCHANGED <<counter, sent, sentTo>>

Termination ==
  /\ counter = totalCounter
  /\ \A s \in Processes: \A r \in Processes: ~HasMessage(link, s, r)
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

\* Perfect FIFO Link properties (Cachin, Guerraoui & Rodrigues)

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ \A s, r \in Processes:
       \A i \in 1..Len(link[s][r]): link[s][r][i] \in MessagesToSend

\* (PL1 - Reliable Delivery) If a process sends m, the receiver eventually delivers m.
PropertyReliableDelivery ==
  \A s \in Processes:
    \A m \in MessagesToSend:
      [](m \in sent[s] => <>(\E r \in Processes: r # s /\ m \in received[r]))

\* (PL2 - No Duplication) No message is delivered more than once.
NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantNoDuplication ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])

\* (PL3 - No Creation) If a process delivers m, then m was previously sent by some process.
InvariantNoCreation ==
  \A p \in Processes:
    \A m \in received[p]:
      \E q \in Processes: m \in sent[q]

\* (FIFO Ordering) Messages from s to r are delivered in the order they were sent.
\* receivedFrom[r][s] must always be a prefix of sentTo[s][r].
IsPrefix(a, b) ==
  /\ Len(a) <= Len(b)
  /\ \A i \in 1..Len(a): a[i] = b[i]

InvariantFIFOOrdering ==
  \A s, r \in Processes:
    s # r => IsPrefix(receivedFrom[r][s], sentTo[s][r])

=============================================================================
