------------------------- MODULE BestEffortBroadcastTest -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE BestEffortBroadcast WITH MaxCrashes <- 1

CONSTANTS Groups, Processes, totalCounter

VARIABLES channel, counter, sent, received, receivedOrdered

vars == <<channel, counter, sent, received, receivedOrdered>>

MessagesToSend == 1 .. totalCounter

CorrectProcesses == { p \in Processes : ~IsCrashed(channel, p) }

Init ==
  /\ channel = Channel(Groups, Processes)
  /\ counter = 0
  /\ sent = [p \in Processes |-> {}]
  /\ received = [p \in Processes |-> {}]
  /\ receivedOrdered = [p \in Processes |-> <<>>]

ProcessSend ==
  \E p \in Processes:
    /\ ~IsCrashed(channel, p)
    /\ counter < totalCounter
    /\ LET msg == counter + 1 IN
        \* Broadcast returns a set of possible next channel states. TLA+ non-deterministically picks one.
       /\ channel' \in Broadcast(channel, "g1", p, msg)
       /\ counter' = counter + 1
       /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {msg}]
       /\ UNCHANGED <<received, receivedOrdered>>

ProcessReceive ==
  \E p \in Processes:
    /\ HasMessage(channel, "g1", p)
    /\ \E m \in Messages(channel, "g1", p):
      /\ channel' = Deliver(channel, "g1", p, m)
      /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
      /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], m)]
      /\ UNCHANGED <<counter, sent>>

\* Crash-stop model from Cachin
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(channel, p)
    /\ CanCrash(channel)
    /\ channel' = Crash(channel, p)
    /\ UNCHANGED <<counter, sent, received, receivedOrdered>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in CorrectProcesses: ~HasMessage(channel, "g1", p)
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

\* Best-Effort Broadcast properties (Cachin, Guerraoui & Rodrigues)

\* (BEB1 - Validity) If a correct process broadcasts m, every correct process eventually delivers m.
\* A correct process is one that never crashes throughout the entire execution.
PropertyValidity ==
  \A p \in Processes:
    \A m \in MessagesToSend:
      (m \in sent[p] /\ [](~IsCrashed(channel, p)))
        => \A q \in Processes:
             [](~IsCrashed(channel, q)) => <>(m \in received[q])

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
