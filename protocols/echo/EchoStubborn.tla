-------------------------- MODULE EchoStubborn --------------------------
EXTENDS Integers, Sequences, TLC

SL == INSTANCE StubbornLink WITH MaxCopies <- 2, MaxCrashes <- 0

Processes == {"A", "B"}
MessagesToSend == {1, 2, -1}

VARIABLES link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB,
          aWaiting, bPending

vars == <<link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB, aWaiting, bPending>>

Init ==
  /\ link = SL!StubbornLink(Processes, Processes)
  /\ toSend = <<1, 2, -1>>
  /\ sentMessagesA = {}
  /\ messageToSend = 0
  /\ receivedMessageA = 0
  /\ receivedMessageB = 0
  /\ aWaiting = FALSE
  /\ bPending = FALSE

SendA ==
  /\ ~aWaiting
  /\ toSend /= <<>>
  /\ messageToSend' = Head(toSend)
  /\ link' = SL!Send(link, "A", "B", messageToSend')
  /\ sentMessagesA' = sentMessagesA \cup {messageToSend'}
  /\ toSend' = Tail(toSend)
  /\ aWaiting' = TRUE
  /\ UNCHANGED <<receivedMessageA, receivedMessageB, bPending>>

ReceiveA ==
  /\ aWaiting
  /\ SL!HasMessage(link, "B", "A")
  /\ \E m \in SL!Messages(link, "B", "A"):
       /\ link' = SL!Receive(link, "B", "A", m)
       /\ receivedMessageA' = m
  /\ aWaiting' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageB, bPending>>

ReceiveB ==
  /\ ~bPending
  /\ SL!HasMessage(link, "A", "B")
  /\ \E m \in SL!Messages(link, "A", "B"):
       /\ link' = SL!Receive(link, "A", "B", m)
       /\ receivedMessageB' = m
  /\ bPending' = TRUE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, aWaiting>>

EchoB ==
  /\ bPending
  /\ link' = SL!Send(link, "B", "A", receivedMessageB)
  /\ bPending' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, receivedMessageB, aWaiting>>

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
