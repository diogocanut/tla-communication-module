-------------------------- MODULE EchoCrash --------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS NumMessages, MaxCrashes

CS == INSTANCE CrashStop
PL == INSTANCE PerfectLinkFIFO

Processes == {"A", "B"}

Fin == -1
MessagesToSend == (1 .. NumMessages) \cup {Fin}
Workload == [i \in 1 .. NumMessages |-> i] \o <<Fin>>

VARIABLES link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB,
          aWaiting, bPending, fm

vars == <<link, toSend, sentMessagesA, messageToSend,
          receivedMessageA, receivedMessageB, aWaiting, bPending, fm>>

Init ==
  /\ link = PL!PerfectLinkFIFO(Processes, Processes)
  /\ toSend = Workload
  /\ sentMessagesA = {}
  /\ messageToSend = 0
  /\ receivedMessageA = 0
  /\ receivedMessageB = 0
  /\ aWaiting = FALSE
  /\ bPending = FALSE
  /\ fm = CS!CrashStop(MaxCrashes)

SendA ==
  /\ ~CS!IsCrashed(fm, "A")
  /\ ~aWaiting
  /\ toSend /= <<>>
  /\ messageToSend' = Head(toSend)
  /\ link' = PL!Send(link, fm, "A", "B", messageToSend')
  /\ sentMessagesA' = sentMessagesA \cup {messageToSend'}
  /\ toSend' = Tail(toSend)
  /\ aWaiting' = TRUE
  /\ UNCHANGED <<receivedMessageA, receivedMessageB, bPending, fm>>

ReceiveA ==
  /\ aWaiting
  /\ PL!HasMessage(link, fm, "B", "A")
  /\ \E m \in PL!Messages(link, fm, "B", "A"):
       /\ link' = PL!Receive(link, fm, "B", "A")
       /\ receivedMessageA' = m
  /\ aWaiting' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageB, bPending, fm>>

ReceiveB ==
  /\ ~bPending
  /\ PL!HasMessage(link, fm, "A", "B")
  /\ \E m \in PL!Messages(link, fm, "A", "B"):
       /\ link' = PL!Receive(link, fm, "A", "B")
       /\ receivedMessageB' = m
  /\ bPending' = TRUE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, aWaiting, fm>>

EchoB ==
  /\ ~CS!IsCrashed(fm, "B")
  /\ bPending
  /\ link' = PL!Send(link, fm, "B", "A", receivedMessageB)
  /\ bPending' = FALSE
  /\ UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, receivedMessageB, aWaiting, fm>>

ProcessCrash ==
  \E p \in Processes:
    /\ ~CS!IsCrashed(fm, p)
    /\ CS!CanCrash(fm)
    /\ fm' = CS!Crash(fm, p)
    /\ UNCHANGED <<link, toSend, sentMessagesA, messageToSend,
                   receivedMessageA, receivedMessageB, aWaiting, bPending>>

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
  \/ ProcessCrash
  \/ Done

Spec == Init /\ [][Next]_vars
             /\ WF_vars(SendA)
             /\ WF_vars(ReceiveA)
             /\ WF_vars(ReceiveB)
             /\ WF_vars(EchoB)

BothCorrect == [](~CS!IsCrashed(fm, "A")) /\ [](~CS!IsCrashed(fm, "B"))

PropertyEcho ==
    \A m \in MessagesToSend : [](messageToSend = m => <>(receivedMessageA = m))

PropertyTermination ==
    <>(receivedMessageB = Fin /\ receivedMessageA = Fin)

PropertyEchoCorrect ==
    \A m \in MessagesToSend :
      BothCorrect => [](messageToSend = m => <>(receivedMessageA = m))

PropertyTerminationCorrect ==
    BothCorrect => <>(receivedMessageB = Fin /\ receivedMessageA = Fin)

PropertyNoCreation ==
    \A m \in MessagesToSend : [](receivedMessageA = m => m \in sentMessagesA)

PropertyCrashedIsSilent ==
    /\ [][CS!IsCrashed(fm, "A") => UNCHANGED <<toSend, sentMessagesA, messageToSend, receivedMessageA, aWaiting>>]_vars
    /\ [][CS!IsCrashed(fm, "B") => UNCHANGED <<receivedMessageB, bPending>>]_vars

=============================================================================
