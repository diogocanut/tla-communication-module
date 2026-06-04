--------------------------- MODULE FairLossLinkTest ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, FairLossLink

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, receivedOrdered, reliablySent

vars == <<link, counter, sent, received, receivedOrdered, reliablySent>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(link, p) }

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
      /\ ~IsCrashed(link, s)
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

\* Crash-stop model from Cachin
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(link, p)
    /\ CanCrash(link)
    /\ link' = Crash(link, p)
    /\ UNCHANGED <<counter, sent, received, receivedOrdered, reliablySent>>

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

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ link.totalDrops \in 0..MaxDrops
  /\ link.crashed \subseteq Processes
  /\ \A s, r \in Processes: link.links[s][r] \subseteq MessagesToSend
  /\ \A s, r \in Processes: reliablySent[s][r] \subseteq MessagesToSend

\* Fair Loss Link properties (Cachin, Guerraoui & Rodrigues)

\* Implementation constraint: total drops stay within configured bound.
PropertyMaxDropsRespected ==
  [](link.totalDrops <= MaxDrops)

\* (FLL1 - Fair Loss) Messages sent while the drop budget is already exhausted
\* are eventually received by every correct receiver. This is a finite-model
\* approximation of the Fair Loss property.
PropertyFairLoss ==
  \A s, r \in Processes:
    \A m \in MessagesToSend:
      [](~IsCrashed(link, r)) =>
        [](m \in reliablySent[s][r] => <>(m \in received[r]))

=============================================================================
