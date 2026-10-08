-------------------------- MODULE EchoStubborn --------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NumMessages, MaxCopies

CS == INSTANCE CrashStop
SL == INSTANCE StubbornLink

\* Failure-free scenario: the failure model is a constant value in which no
\* process ever crashes.
fm == CS!CrashStop(0)

Processes == {"A", "B"}

Fin == -1
MessagesToSend == (1 .. NumMessages) \cup {Fin}
Workload == [i \in 1 .. NumMessages |-> i] \o <<Fin>>

VARIABLES link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB,
          aWaiting, bPending, deliveredB

vars == <<link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB, aWaiting, bPending, deliveredB>>

Init ==
  /\ link = SL!StubbornLink(Processes, Processes)
  /\ toSend = Workload
  /\ sentMessagesA = {}
  /\ messageToSend = 0
  /\ receivedMessageA = 0
  /\ receivedMessageB = 0
  /\ aWaiting = FALSE
  /\ bPending = FALSE
  /\ deliveredB = {}

SendA ==
  /\ ~aWaiting
  /\ toSend /= <<>>
  /\ messageToSend' = Head(toSend)
  /\ link' = SL!Send(link, fm, "A", "B", messageToSend')
  /\ sentMessagesA' = sentMessagesA \cup {messageToSend'}
  /\ toSend' = Tail(toSend)
  /\ aWaiting' = TRUE
  /\ UNCHANGED <<receivedMessageA, receivedMessageB, bPending, deliveredB>>

ReceiveA ==
  /\ aWaiting
  /\ SL!HasMessage(link, fm, "B", "A")
  /\ \E m \in SL!Messages(link, fm, "B", "A"):
       /\ m = messageToSend
       /\ link' = SL!Receive(link, fm, "B", "A", m)
       /\ receivedMessageA' = m
  /\ aWaiting' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageB, bPending, deliveredB>>

ReceiveB ==
  /\ ~bPending
  /\ SL!HasMessage(link, fm, "A", "B")
  /\ \E m \in SL!Messages(link, fm, "A", "B"):
       /\ m \notin deliveredB
       /\ link' = SL!Receive(link, fm, "A", "B", m)
       /\ receivedMessageB' = m
       /\ deliveredB' = deliveredB \cup {m}
  /\ bPending' = TRUE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, aWaiting>>

EchoB ==
  /\ bPending
  /\ link' = SL!Send(link, fm, "B", "A", receivedMessageB)
  /\ bPending' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, receivedMessageB, aWaiting, deliveredB>>

Done ==
  /\ toSend = <<>>
  /\ ~aWaiting
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
    \A m \in MessagesToSend : [](messageToSend = m => <>(receivedMessageA = m))

PropertyTermination ==
    <>(receivedMessageB = Fin /\ receivedMessageA = Fin)

PropertyNoCreation ==
    \A m \in MessagesToSend : [](receivedMessageA = m => m \in sentMessagesA)

=============================================================================
