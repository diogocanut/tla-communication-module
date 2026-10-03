-------------------------- MODULE EchoPipelinedUnordered --------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NumMessages, Window

CS == INSTANCE CrashStop
PL == INSTANCE PerfectLink

\* Failure-free scenario: the failure model is a constant value in which no
\* process ever crashes.
fm == CS!CrashStop(0)

Processes == {"A", "B"}

Fin == -1
MessagesToSend == (1 .. NumMessages) \cup {Fin}
Workload == [i \in 1 .. NumMessages |-> i] \o <<Fin>>

VARIABLES link, toSend, sentA, receivedA, receivedMessageB, bPending

vars == <<link, toSend, sentA, receivedA, receivedMessageB, bPending>>

Range(seq) == { seq[i] : i \in 1 .. Len(seq) }

Init ==
  /\ link = PL!PerfectLink(Processes, Processes)
  /\ toSend = Workload
  /\ sentA = <<>>
  /\ receivedA = <<>>
  /\ receivedMessageB = 0
  /\ bPending = FALSE

SendA ==
  /\ toSend /= <<>>
  /\ Len(sentA) - Len(receivedA) < Window
  /\ link' = PL!Send(link, fm, "A", "B", Head(toSend))
  /\ sentA' = Append(sentA, Head(toSend))
  /\ toSend' = Tail(toSend)
  /\ UNCHANGED <<receivedA, receivedMessageB, bPending>>

ReceiveA ==
  /\ PL!HasMessage(link, fm, "B", "A")
  /\ \E m \in PL!Messages(link, fm, "B", "A"):
       /\ link' = PL!Receive(link, fm, "B", "A", m)
       /\ receivedA' = Append(receivedA, m)
  /\ UNCHANGED <<toSend, sentA, receivedMessageB, bPending>>

ReceiveB ==
  /\ ~bPending
  /\ PL!HasMessage(link, fm, "A", "B")
  /\ \E m \in PL!Messages(link, fm, "A", "B"):
       /\ link' = PL!Receive(link, fm, "A", "B", m)
       /\ receivedMessageB' = m
  /\ bPending' = TRUE
  /\ UNCHANGED <<toSend, sentA, receivedA>>

EchoB ==
  /\ bPending
  /\ link' = PL!Send(link, fm, "B", "A", receivedMessageB)
  /\ bPending' = FALSE
  /\ UNCHANGED <<toSend, sentA, receivedA, receivedMessageB>>

Done ==
  /\ toSend = <<>>
  /\ Len(receivedA) = Len(sentA)
  /\ ~bPending
  /\ UNCHANGED vars

Next ==
  \/ SendA
  \/ ReceiveA
  \/ ReceiveB
  \/ EchoB
  \/ Done

Spec == Init /\ [][Next]_vars
             /\ WF_vars(SendA)
             /\ WF_vars(ReceiveA)
             /\ WF_vars(ReceiveB)
             /\ WF_vars(EchoB)

PropertyEcho ==
    \A m \in MessagesToSend : [](m \in Range(sentA) => <>(m \in Range(receivedA)))

PropertyTermination ==
    <>(Len(receivedA) = Len(Workload))

InvariantNoCreation ==
    Range(receivedA) \subseteq Range(sentA)

InvariantEchoOrder ==
    receivedA = SubSeq(sentA, 1, Len(receivedA))

=============================================================================
