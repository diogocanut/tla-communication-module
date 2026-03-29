--------------------------- MODULE FairLossLinkTest ---------------------------
EXTENDS Integers, Sequences, TLC, FairLossLink

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, receivedOrdered, reliablySent

vars == <<link, counter, sent, received, receivedOrdered, reliablySent>>

MessagesToSend == 1 .. totalCounter

Init ==
  /\ link = FairLossLink(Processes, Processes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]
  /\ reliablySent = [s \in Processes |-> [r \in Processes |-> {}]]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ counter < totalCounter
      /\ LET msg == counter + 1 IN
         /\ link' \in Send(link, s, r, msg)
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![s] = sent[s] \cup {msg}]
         /\ reliablySent' =
              [reliablySent EXCEPT ![s][r] =
                 IF link.totalDrops = MaxDrops
                 THEN reliablySent[s][r] \cup {msg}
                 ELSE reliablySent[s][r]]
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
          /\ UNCHANGED <<counter, sent, reliablySent>>

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
  /\ link.totalDrops \in 0..MaxDrops
  /\ \A s, r \in Processes: link.links[s][r] \subseteq MessagesToSend
  /\ \A s, r \in Processes: reliablySent[s][r] \subseteq MessagesToSend

\* Fair Loss Link properties (Cachin, Guerraoui & Rodrigues)

\* Liveness witness: at least one message is eventually delivered.
PropertyEventualDelivery ==
  <>(received # [p \in Processes |-> {}])

\* Implementation constraint: total drops stay within configured bound.
PropertyMaxDropsRespected ==
  [](link.totalDrops <= MaxDrops)

\* (FAIR LOSS) Messages sent while the drop budget is already exhausted are eventually received.
\* This is a finite-model approximation of the Fair Loss property.
PropertyFairLoss ==
  \A s, r \in Processes:
    \A m \in MessagesToSend:
      [](m \in reliablySent[s][r] => <>(m \in received[r]))

=============================================================================
