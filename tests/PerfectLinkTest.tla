--------------------------- MODULE PerfectLinkTest ---------------------------
EXTENDS Integers, Sequences, TLC, PerfectLink

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, receivedOrdered

vars == <<link, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

Init ==
  /\ link = PerfectLink(Processes)
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
  \E p \in Processes:
    /\ HasMessage(link, p)
    /\ \E m \in Messages(link, p):
        /\ link' = Receive(link, p, m)
        /\ received' =
             [received EXCEPT ![p] =
                received[p] \cup {UnwrapMessage(m)}]
        /\ receivedOrdered' =
             [receivedOrdered EXCEPT ![p] =
                Append(receivedOrdered[p], UnwrapMessage(m))]
        /\ UNCHANGED <<counter, sent>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in Processes: ~HasMessage(link, p)
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

=============================================================================
