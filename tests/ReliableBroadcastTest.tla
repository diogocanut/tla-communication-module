------------------------- MODULE ReliableBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE ReliableBroadcast
INSTANCE CrashStop

CONSTANTS Groups, Processes, totalCounter

VARIABLES channel, fm, counter, sent, received, receivedOrdered

vars == <<channel, fm, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(fm, p) }

Init ==
  /\ channel = Channel(Groups, Processes)
  /\ fm = CrashStop(1)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]

ProcessSend ==
  \E p \in Processes:
    /\ ~IsCrashed(fm, p)
    /\ counter < totalCounter
    /\ LET msg == counter + 1 IN
       /\ channel' = Broadcast(channel, fm, "g1", p, msg)
       /\ counter' = counter + 1
       /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {msg}]
       /\ UNCHANGED <<fm, received, receivedOrdered>>

ProcessReceive ==
  \E p \in Processes:
    /\ HasMessage(channel, fm, "g1", p)
    /\ \E m \in Messages(channel, fm, "g1", p):
      /\ channel' = Deliver(channel, fm, "g1", p, m)
      /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
      /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], m)]
      /\ UNCHANGED <<fm, counter, sent>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in CorrectProcesses: ~HasMessage(channel, fm, "g1", p)
  /\ UNCHANGED vars

\* Crash-stop model from Cachin: the crash is recorded once, in the shared
\* failure model; the channel itself is untouched.
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(fm, p)
    /\ CanCrash(fm)
    /\ fm' = Crash(fm, p)
    /\ UNCHANGED <<channel, counter, sent, received, receivedOrdered>>

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
  /\ fm.crashed \subseteq Processes
  /\ \A g \in Groups: \A p \in Processes: channel.links[g][p] \subseteq MessagesToSend

\* Reliable Broadcast properties (Cachin, Guerraoui & Rodrigues)

\* (RB1 - Validity) If a correct process broadcasts m, every correct process eventually delivers m.
\* Note the trigger sits under [] (Response under Globally): a plain state
\* predicate outside a temporal operator would be evaluated in the initial
\* state only, making the property vacuously true.
PropertyValidity ==
  \A p, q \in Processes:
    \A m \in MessagesToSend:
      ([](~IsCrashed(fm, p)) /\ [](~IsCrashed(fm, q)))
        => [](m \in sent[p] => <>(m \in received[q]))

\* (RB2 - No Duplication) No message is delivered more than once.
NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantNoDuplication ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])

\* (RB3 - No Creation) If a process delivers m, then m was previously broadcast by some process.
InvariantNoCreation ==
  \A p \in Processes:
    \A m \in received[p]:
      \E q \in Processes: m \in sent[q]

\* (RB4 - Agreement) If any correct process delivers m, every correct process eventually delivers m.
PropertyAgreement ==
  \A m \in MessagesToSend:
    \A p1, p2 \in Processes:
      [](~IsCrashed(fm, p2))
        => [](m \in received[p1] => <>(m \in received[p2]))

=============================================================================
