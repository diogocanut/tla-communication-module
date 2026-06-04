--------------------------- MODULE PerfectLinkTest ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, PerfectLink

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, receivedOrdered

vars == <<link, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(link, p) }

Init ==
  /\ link = PerfectLink(Processes, Processes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ ~IsCrashed(link, s)
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

\* Crash-stop model from Cachin
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(link, p)
    /\ CanCrash(link)
    /\ link' = Crash(link, p)
    /\ UNCHANGED <<counter, sent, received, receivedOrdered>>

Termination ==
  /\ counter = totalCounter
  /\ \A s \in Processes: \A r \in CorrectProcesses: ~HasMessage(link, s, r)
  /\ UNCHANGED vars

Next ==
  \/ ProcessSend
  \/ ProcessReceive
  \/ ProcessCrash
  \/ Termination

Spec ==
  Init /\ [][Next]_vars
       /\ WF_vars(Next)
       /\ SF_vars(ProcessSend)
       /\ SF_vars(ProcessReceive)

\* Perfect Link properties (Cachin, Guerraoui & Rodrigues)

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ link.crashed \subseteq Processes
  /\ \A s, r \in Processes: link.links[s][r] \subseteq MessagesToSend

\* (PL1 - Reliable Delivery) If a correct process sends m to a correct receiver,
\* the receiver eventually delivers m.
PropertyReliableDelivery ==
  \A s \in Processes:
    \A m \in MessagesToSend:
      (m \in sent[s] /\ [](~IsCrashed(link, s)))
        => \A r \in Processes:
             (r # s /\ [](~IsCrashed(link, r))) => <>(m \in received[r])

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

=============================================================================
