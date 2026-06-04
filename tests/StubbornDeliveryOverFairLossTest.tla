-------------------- MODULE StubbornDeliveryOverFairLossTest --------------------
EXTENDS Integers, Sequences, TLC, FiniteSets, FairLossLink

(*
  In Fair-Loss Link, we use a MaxDrops constant to bound how many times a message can be dropped.
  This avoids unbounded behaviors in TLC where the same message is dropped indefinitely.
  MaxCrashes bounds process crashes (orthogonal to drops).
*)

CONSTANTS Processes, totalCounter

VARIABLES link, counter, sent, received, pending

vars == <<link, counter, sent, received, pending>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(link, p) }

Init ==
  /\ link = FairLossLink(Processes, Processes)
  /\ counter = 0
  /\ sent = [s \in Processes |-> [r \in Processes |-> {}]]
  /\ received = [p \in Processes |-> {}]
  /\ pending = [s \in Processes |-> [r \in Processes |-> {}]]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ ~IsCrashed(link, s)
      /\ counter < totalCounter
      /\ LET msg == counter + 1 IN
         /\ link' \in Send(link, s, r, msg)
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![s][r] = sent[s][r] \cup {msg}]
         /\ pending' = [pending EXCEPT ![s][r] = pending[s][r] \cup {msg}]
         /\ UNCHANGED received

ProcessRetransmit ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ ~IsCrashed(link, s)
      /\ pending[s][r] /= {}
      /\ \E m \in pending[s][r]:
         /\ link' \in Send(link, s, r, m)
         /\ UNCHANGED <<counter, sent, received, pending>>

ProcessReceive ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ HasMessage(link, s, r)
      /\ \E m \in Messages(link, s, r):
         /\ link' = Receive(link, s, r, m)
         /\ received' = [received EXCEPT ![r] = received[r] \cup {m}]
         /\ pending' = [pending EXCEPT ![s][r] = pending[s][r] \ {m}]
         /\ UNCHANGED <<counter, sent>>

\* Crash-stop model from Cachin
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(link, p)
    /\ CanCrash(link)
    /\ link' = Crash(link, p)
    /\ UNCHANGED <<counter, sent, received, pending>>

Termination ==
  /\ counter = totalCounter
  /\ \A s \in Processes: \A r \in CorrectProcesses: ~HasMessage(link, s, r)
  /\ \A s \in CorrectProcesses: \A r \in CorrectProcesses: pending[s][r] = {}
  /\ UNCHANGED vars

Next ==
  \/ ProcessSend
  \/ ProcessRetransmit
  \/ ProcessReceive
  \/ ProcessCrash
  \/ Termination

Spec ==
  Init /\ [][Next]_vars
       /\ WF_vars(Next)
       /\ SF_vars(ProcessSend)
       /\ SF_vars(ProcessRetransmit)
       /\ SF_vars(ProcessReceive)

TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A s, r \in Processes: sent[s][r] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ \A s, r \in Processes: pending[s][r] \subseteq MessagesToSend
  /\ link.totalDrops \in 0..MaxDrops
  /\ link.crashed \subseteq Processes
  /\ \A s, r \in Processes: link.links[s][r] \subseteq MessagesToSend

\* (STUBBORN DELIVERY) If a correct process sends m to a correct receiver,
\* the receiver eventually receives m. This property holds because MaxDrops
\* guarantees that after a bounded number of drops, retransmissions are forced
\* to succeed.
PropertyStubbornDelivery ==
  \A s \in Processes:
    \A r \in Processes:
      \A m \in MessagesToSend:
        ([](~IsCrashed(link, s)) /\ [](~IsCrashed(link, r)))
          => [](m \in sent[s][r] => <>(m \in received[r]))

\* (NO CREATION) A process receives m only if some process previously sent m.
InvariantNoCreation ==
  \A r \in Processes:
    \A m \in received[r]:
      \E s \in Processes: m \in sent[s][r]

=============================================================================
