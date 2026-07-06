------------------------- MODULE BestEffortBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE BestEffortBroadcast WITH MaxCrashes <- 1
INSTANCE CrashStop WITH MaxCrashes <- 1

CONSTANTS Groups, Processes, totalCounter

VARIABLES channel, fm, counter, sent, received, receivedOrdered

vars == <<channel, fm, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(fm, p) }

Init ==
  /\ channel = Channel(Groups, Processes)
  /\ fm = CrashStop
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]

\* A best-effort broadcast may crash the sender mid-broadcast (reaching only
\* a subset of the receivers), so Broadcast returns records carrying both
\* the new channel and the new failure model.
ProcessSend ==
  \E p \in Processes:
    /\ ~IsCrashed(fm, p)
    /\ counter < totalCounter
    /\ LET msg == counter + 1 IN
       \E out \in Broadcast(channel, fm, "g1", p, msg):
         /\ channel' = out.channel
         /\ fm' = out.fm
         /\ counter' = counter + 1
         /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {msg}]
         /\ UNCHANGED <<received, receivedOrdered>>

ProcessReceive ==
  \E p \in Processes:
    /\ HasMessage(channel, fm, "g1", p)
    /\ \E m \in Messages(channel, fm, "g1", p):
      /\ channel' = Deliver(channel, fm, "g1", p, m)
      /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
      /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], m)]
      /\ UNCHANGED <<fm, counter, sent>>

\* Crash-stop model from Cachin: the crash is recorded once, in the shared
\* failure model; the channel itself is untouched.
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(fm, p)
    /\ CanCrash(fm)
    /\ fm' = Crash(fm, p)
    /\ UNCHANGED <<channel, counter, sent, received, receivedOrdered>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in CorrectProcesses: ~HasMessage(channel, fm, "g1", p)
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
  /\ fm.crashed \subseteq Processes
  /\ \A g \in Groups: \A p \in Processes: channel.links[g][p] \subseteq MessagesToSend

\* Best-Effort Broadcast properties (Cachin, Guerraoui & Rodrigues)

\* (BEB1 - Validity) If a correct process broadcasts m, every correct process eventually delivers m.
\* A correct process is one that never crashes throughout the entire execution.
\* Note the trigger sits under [] (Response under Globally): a plain state
\* predicate outside a temporal operator would be evaluated in the initial
\* state only, making the property vacuously true.
PropertyValidity ==
  \A p, q \in Processes:
    \A m \in MessagesToSend:
      ([](~IsCrashed(fm, p)) /\ [](~IsCrashed(fm, q)))
        => [](m \in sent[p] => <>(m \in received[q]))

\* (BEB2 - No Duplication) No message is delivered more than once.
NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantNoDuplication ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])

\* (BEB3 - No Creation) If a process delivers m, then m was previously broadcast by some process.
InvariantNoCreation ==
  \A p \in Processes:
    \A m \in received[p]:
      \E q \in Processes: m \in sent[q]

=============================================================================
