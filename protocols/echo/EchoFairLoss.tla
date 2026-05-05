-------------------------- MODULE EchoFairLoss --------------------------
EXTENDS Integers, Sequences, TLC

FL == INSTANCE FairLossLink WITH MaxDrops <- 0, MaxCrashes <- 0

Processes == {"A", "B"}
MessagesToSend == {1, 2, 3, 4, 5, -1}

VARIABLES link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB,
          aWaiting, bPending

vars == <<link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB, aWaiting, bPending>>

Init ==
  /\ link = FL!FairLossLink(Processes, Processes)
  /\ toSend = <<1, 2, 3, 4, 5, -1>>
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
  /\ \E newLink \in FL!Send(link, "A", "B", messageToSend'):
       link' = newLink
  /\ sentMessagesA' = sentMessagesA \cup {messageToSend'}
  /\ toSend' = Tail(toSend)
  /\ aWaiting' = TRUE
  /\ UNCHANGED <<receivedMessageA, receivedMessageB, bPending>>

ReceiveA ==
  /\ aWaiting
  /\ FL!HasMessage(link, "B", "A")
  /\ \E m \in FL!Messages(link, "B", "A"):
       /\ link' = FL!Receive(link, "B", "A", m)
       /\ receivedMessageA' = m
  /\ aWaiting' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageB, bPending>>

ReceiveB ==
  /\ ~bPending
  /\ FL!HasMessage(link, "A", "B")
  /\ \E m \in FL!Messages(link, "A", "B"):
       /\ link' = FL!Receive(link, "A", "B", m)
       /\ receivedMessageB' = m
  /\ bPending' = TRUE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, aWaiting>>

EchoB ==
  /\ bPending
  /\ \E newLink \in FL!Send(link, "B", "A", receivedMessageB):
       link' = newLink
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
