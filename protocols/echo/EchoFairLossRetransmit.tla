-------------------------- MODULE EchoFairLossRetransmit --------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NumMessages, MaxDrops

CS == INSTANCE CrashStop
FL == INSTANCE FairLossLink

\* Failure-free scenario: the failure model is a constant value in which no
\* process ever crashes.
fm == CS!CrashStop(0)

Processes == {"A", "B"}

Fin == -1
MessagesToSend == (1 .. NumMessages) \cup {Fin}
Workload == [i \in 1 .. NumMessages |-> i] \o <<Fin>>

VARIABLES link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB,
          aWaiting, bPending, echoMessage, deliveredB

vars == <<link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB, aWaiting, bPending, echoMessage, deliveredB>>

Init ==
  /\ link = FL!FairLossLink(Processes, Processes)
  /\ toSend = Workload
  /\ sentMessagesA = {}
  /\ messageToSend = 0
  /\ receivedMessageA = 0
  /\ receivedMessageB = 0
  /\ aWaiting = FALSE
  /\ bPending = FALSE
  /\ echoMessage = 0
  /\ deliveredB = {}

SendA ==
  /\ ~aWaiting
  /\ toSend /= <<>>
  /\ messageToSend' = Head(toSend)
  /\ \E newLink \in FL!Send(link, fm, "A", "B", messageToSend'):
       link' = newLink
  /\ sentMessagesA' = sentMessagesA \cup {messageToSend'}
  /\ toSend' = Tail(toSend)
  /\ aWaiting' = TRUE
  /\ UNCHANGED <<receivedMessageA, receivedMessageB, bPending, echoMessage, deliveredB>>

ResendA ==
  /\ aWaiting
  /\ \E newLink \in FL!Send(link, fm, "A", "B", messageToSend):
       link' = newLink
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA,
                 receivedMessageB, aWaiting, bPending, echoMessage, deliveredB>>

ReceiveA ==
  /\ FL!HasMessage(link, fm, "B", "A")
  /\ \E m \in FL!Messages(link, fm, "B", "A"):
       /\ link' = FL!Receive(link, fm, "B", "A", m)
       /\ IF aWaiting /\ m = messageToSend
          THEN /\ receivedMessageA' = m
               /\ aWaiting' = FALSE
          ELSE UNCHANGED <<receivedMessageA, aWaiting>>
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageB,
                 bPending, echoMessage, deliveredB>>

ReceiveB ==
  /\ ~bPending
  /\ FL!HasMessage(link, fm, "A", "B")
  /\ \E m \in FL!Messages(link, fm, "A", "B"):
       /\ link' = FL!Receive(link, fm, "A", "B", m)
       /\ echoMessage' = m
       /\ IF m \notin deliveredB
          THEN /\ receivedMessageB' = m
               /\ deliveredB' = deliveredB \cup {m}
          ELSE UNCHANGED <<receivedMessageB, deliveredB>>
  /\ bPending' = TRUE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, aWaiting>>

EchoB ==
  /\ bPending
  /\ \E newLink \in FL!Send(link, fm, "B", "A", echoMessage):
       link' = newLink
  /\ bPending' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA,
                 receivedMessageB, aWaiting, echoMessage, deliveredB>>

Done ==
  /\ toSend = <<>>
  /\ ~aWaiting
  /\ ~bPending
  /\ UNCHANGED vars

Next ==
  \/ SendA
  \/ ResendA
  \/ ReceiveA
  \/ ReceiveB
  \/ EchoB
  \/ Done

Spec == Init /\ [][Next]_vars
             /\ WF_vars(SendA)
             /\ WF_vars(ResendA)
             /\ WF_vars(ReceiveA)
             /\ WF_vars(ReceiveB)
             /\ WF_vars(EchoB)

SpecNoResendFairness == Init /\ [][Next]_vars
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
