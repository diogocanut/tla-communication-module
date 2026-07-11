--------------------------- MODULE FairLossLinkTest ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, FairLossLink, CrashStop

CONSTANTS Processes, totalCounter, MaxCrashes

VARIABLES link, fm, counter, sent, received, receivedOrdered, reliablySent

vars == <<link, fm, counter, sent, received, receivedOrdered, reliablySent>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(fm, p) }

Init ==
  /\ link = FairLossLink(Processes, Processes)
  /\ fm = CrashStop(MaxCrashes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]
  /\ reliablySent = [s \in Processes |-> [r \in Processes |-> {}]]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ ~IsCrashed(fm, s)
      /\ counter < totalCounter
      /\ LET msg == counter + 1 IN
         /\ link' \in Send(link, fm, s, r, msg)
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![s] = sent[s] \cup {msg}]
         /\ reliablySent' =
              [reliablySent EXCEPT ![s][r] =
                 IF link.totalDrops = MaxDrops
                 THEN reliablySent[s][r] \cup {msg}
                 ELSE reliablySent[s][r]]
         /\ UNCHANGED <<fm, received, receivedOrdered>>

ProcessReceive ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ HasMessage(link, fm, s, r)
      /\ \E m \in Messages(link, fm, s, r):
         /\ link' = Receive(link, fm, s, r, m)
         /\ received' = [received EXCEPT ![r] = received[r] \cup {m}]
         /\ receivedOrdered' =
              [receivedOrdered EXCEPT ![r] =
                 Append(receivedOrdered[r], m)]
         /\ UNCHANGED <<fm, counter, sent, reliablySent>>

\* Crash-stop model from Cachin: the crash is recorded once, in the shared
\* failure model; the link itself is untouched.
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(fm, p)
    /\ CanCrash(fm)
    /\ fm' = Crash(fm, p)
    /\ UNCHANGED <<link, counter, sent, received, receivedOrdered, reliablySent>>

Termination ==
  /\ counter = totalCounter
  /\ \A s \in Processes: \A r \in CorrectProcesses: ~HasMessage(link, fm, s, r)
  /\ UNCHANGED vars

Next ==
  \/ ProcessSend
  \/ ProcessReceive
  \/ ProcessCrash
  \/ Termination

\* Fairness convention (paper, Properties under Crash): weak fairness on the
\* consumer-side actions only. A receive stays enabled while a message waits
\* (the message cannot vanish), so WF forces eventual delivery; sends and
\* crashes are choices and get no fairness. The liveness properties are
\* conditional on their triggers, so behaviors that never send satisfy them
\* trivially.
Spec ==
  Init /\ [][Next]_vars
       /\ WF_vars(ProcessReceive)

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ link.totalDrops \in 0..MaxDrops
  /\ fm.crashed \subseteq Processes
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
      [](~IsCrashed(fm, r)) =>
        [](m \in reliablySent[s][r] => <>(m \in received[r]))

=============================================================================
