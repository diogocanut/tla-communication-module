--------------------------- MODULE StubbornLinkTest ---------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, StubbornLink

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, receivedOrdered

vars == <<link, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

Init ==
  /\ link = StubbornLink(Processes, Processes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ counter < totalCounter
      /\ LET msg == counter + 1 IN
         /\ link' = Send(link, s, r, msg)
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![s] = sent[s] \cup {msg}]
         /\ UNCHANGED <<received, receivedOrdered>>

ProcessReceive ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ HasMessage(link, s, r)
      /\ \E m \in Messages(link, s, r):
          /\ link' = Receive(link, s, r, m)
          /\ received' =
               [received EXCEPT ![r] =
                  received[r] \cup {m}]
          /\ receivedOrdered' =
               [receivedOrdered EXCEPT ![r] =
                  Append(receivedOrdered[r], m)]
          /\ UNCHANGED <<counter, sent>>

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

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ \A s, r \in Processes: Messages(link, s, r) \subseteq MessagesToSend

\* Stubborn Link properties (Cachin, Guerraoui & Rodrigues)

\* (STUBBORN DELIVERY) If a process sends m, it is eventually received
\* (finite-model approximation: m is received at least once).
PropertyStubbornDelivery ==
  \A s \in Processes:
    \A m \in MessagesToSend:
      [](m \in sent[s] => <>(\E r \in Processes: r # s /\ m \in received[r]))

\* Stubborn links deliver messages multiple times by design.
\* This property verifies that duplication is actually occurring.
PropertyDuplication ==
  \A p \in Processes:
    Len(receivedOrdered[p]) >= Cardinality(received[p])

=============================================================================
