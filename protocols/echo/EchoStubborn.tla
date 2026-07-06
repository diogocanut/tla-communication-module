-------------------------- MODULE EchoStubborn --------------------------
EXTENDS Integers, Sequences, TLC

CS == INSTANCE CrashStop WITH MaxCrashes <- 0
SL == INSTANCE StubbornLink WITH MaxCopies <- 2

\* Failure-free scenario: the failure model is a constant value in which no
\* process ever crashes.
fm == CS!CrashStop

Processes == {"A", "B"}
MessagesToSend == {1, 2, -1}

VARIABLES link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB,
          aWaiting, bPending, deliveredB

vars == <<link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB, aWaiting, bPending, deliveredB>>

Init ==
  /\ link = SL!StubbornLink(Processes, Processes)
  /\ toSend = <<1, 2, -1>>
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

\* A stubborn link duplicates deliveries, so A accepts only the echo of the
\* message it is currently waiting for; stale duplicate echoes of earlier
\* messages stay in the buffer and are never mistaken for the reply.
ReceiveA ==
  /\ aWaiting
  /\ SL!HasMessage(link, fm, "B", "A")
  /\ \E m \in SL!Messages(link, fm, "B", "A"):
       /\ m = messageToSend
       /\ link' = SL!Receive(link, fm, "B", "A", m)
       /\ receivedMessageA' = m
  /\ aWaiting' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageB, bPending, deliveredB>>

\* B de-duplicates: it delivers each message once, ignoring the extra copies
\* the stubborn link produces (Cachin: eliminating duplicates over a stubborn
\* link is exactly how a perfect link is implemented).
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
             /\ WF_vars(Next)
             /\ SF_vars(SendA)
             /\ SF_vars(ReceiveA)
             /\ SF_vars(ReceiveB)
             /\ SF_vars(EchoB)


Property1 ==
    \A m \in MessagesToSend : [](messageToSend = m => <>(receivedMessageA = m))

Property2 ==
    <>(receivedMessageB = -1 /\ receivedMessageA = -1)

Property3 ==
    \A m \in MessagesToSend : [](receivedMessageA = m => m \in sentMessagesA)

=============================================================================
