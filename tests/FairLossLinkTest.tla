--------------------------- MODULE FairLossLinkTest ---------------------------
EXTENDS Integers, Sequences, TLC, FairLossLink

CONSTANTS Processes, totalCounter, MaxDrops

VARIABLES link, counter, sent, received, receivedOrdered

vars == <<link, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

Init ==
  /\ link = FairLossLink(Processes, Processes)
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
         /\ link' \in Send(link, s, r, msg)
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

PropertySomeDelivery ==
  <>(received # [p \in Processes |-> {}])

PropertyMaxDropsRespected ==
  [](link.totalDrops <= MaxDrops)

PropertyEventualDeliveryWhenNoDrops ==
  [](link.totalDrops = MaxDrops =>
      \A s, r \in Processes: \A m \in sent[s]:
        <>(m \in received[r] \/ s = r))

=============================================================================
