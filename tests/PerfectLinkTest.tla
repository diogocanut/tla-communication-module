--------------------------- MODULE PerfectLinkTest ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, PerfectLink, CrashStop

CONSTANTS Processes, totalCounter, MaxCrashes

VARIABLES link, fm, counter, sent, received, receivedOrdered, sentTo

vars == <<link, fm, counter, sent, received, receivedOrdered, sentTo>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(fm, p) }

Init ==
  /\ link = PerfectLink(Processes, Processes)
  /\ fm = CrashStop(MaxCrashes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]
  /\ sentTo = [s \in Processes |-> [r \in Processes |-> {}]]

ProcessSend ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ ~IsCrashed(fm, s)
      /\ counter < totalCounter
      /\ LET msg == counter + 1 IN
         /\ link' = Send(link, fm, s, r, msg)
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![s] = sent[s] \cup {msg}]
         /\ sentTo' = [sentTo EXCEPT ![s][r] = sentTo[s][r] \cup {msg}]
         /\ UNCHANGED <<fm, received, receivedOrdered>>

ProcessReceive ==
  \E s \in Processes:
    \E r \in Processes:
      /\ s # r
      /\ HasMessage(link, fm, s, r)
      /\ \E m \in Messages(link, fm, s, r):
          /\ link' = Receive(link, fm, s, r, m)
          /\ received' =
               [received EXCEPT ![r] =
                  received[r] \cup {m}]
          /\ receivedOrdered' =
               [receivedOrdered EXCEPT ![r] =
                  Append(receivedOrdered[r], m)]
          /\ UNCHANGED <<fm, counter, sent, sentTo>>

\* Crash-stop model from Cachin: the crash is recorded once, in the shared
\* failure model; the link itself is untouched.
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(fm, p)
    /\ CanCrash(fm)
    /\ fm' = Crash(fm, p)
    /\ UNCHANGED <<link, counter, sent, received, receivedOrdered, sentTo>>

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

\* Perfect Link properties (Cachin, Guerraoui & Rodrigues)

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ fm.crashed \subseteq Processes
  /\ \A s, r \in Processes: link.links[s][r] \subseteq MessagesToSend
  /\ \A s, r \in Processes: sentTo[s][r] \subseteq MessagesToSend

\* (PL1 - Reliable Delivery) If a correct process sends m to a correct receiver,
\* the receiver eventually delivers m. The obligation binds only the receiver
\* the message was actually sent to, hence the per-pair sentTo bookkeeping.
\* Note the trigger sits under [] (Response under Globally): a plain state
\* predicate outside a temporal operator would be evaluated in the initial
\* state only, making the property vacuously true.
PropertyReliableDelivery ==
  \A s, r \in Processes:
    \A m \in MessagesToSend:
      ([](~IsCrashed(fm, s)) /\ [](~IsCrashed(fm, r)))
        => [](m \in sentTo[s][r] => <>(m \in received[r]))

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
