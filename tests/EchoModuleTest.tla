---------------------------- MODULE EchoModuleTest ----------------------------
EXTENDS Integers, Sequences, TLC

INSTANCE PerfectLink

VARIABLES link, toSend, sentA, receivedA,
          lastSentA, lastRecvA, lastRecvB,
          pcA, pcB

vars == <<link, toSend, sentA, receivedA, lastSentA, lastRecvA, lastRecvB, pcA, pcB>>

Procs == {"A", "B"}
MessageSequence == <<1, 2, 3, -1>>
MessageValues == {MessageSequence[i] : i \in DOMAIN MessageSequence}

Init ==
  /\ link = PerfectLink(Procs, Procs)
  /\ toSend = MessageSequence
  /\ sentA = {}
  /\ receivedA = {}
  /\ lastSentA = 0
  /\ lastRecvA = 0
  /\ lastRecvB = 0
  /\ pcA = "send"
  /\ pcB = "waitMsg"

ProcessA_Send ==
  /\ pcA = "send"
  /\ toSend /= <<>>
  /\ LET msg == Head(toSend) IN
     /\ link' = Send(link, "A", "B", msg)
     /\ lastSentA' = msg
     /\ sentA' = sentA \cup {msg}
     /\ toSend' = Tail(toSend)
     /\ pcA' = "waitEcho"
  /\ UNCHANGED <<pcB, lastRecvB, receivedA, lastRecvA>>

ProcessA_Receive ==
  /\ pcA = "waitEcho"
  /\ HasMessage(link, "B", "A")
  /\ \E m \in Messages(link, "B", "A"):
     /\ link' = Receive(link, "B", "A", m)
     /\ lastRecvA' = m
     /\ receivedA' = receivedA \cup {m}
     /\ pcA' = IF toSend = <<>> THEN "done" ELSE "send"
  /\ UNCHANGED <<pcB, toSend, lastSentA, sentA, lastRecvB>>

ProcessB_Receive ==
  /\ pcB = "waitMsg"
  /\ HasMessage(link, "A", "B")
  /\ \E m \in Messages(link, "A", "B"):
     /\ link' = Receive(link, "A", "B", m)
     /\ lastRecvB' = m
     /\ pcB' = "echo"
  /\ UNCHANGED <<pcA, toSend, lastSentA, sentA, receivedA, lastRecvA>>

ProcessB_Echo ==
  /\ pcB = "echo"
  /\ link' = Send(link, "B", "A", lastRecvB)
  /\ pcB' = IF lastRecvB = -1 THEN "done" ELSE "waitMsg"
  /\ UNCHANGED <<pcA, toSend, lastSentA, sentA, receivedA, lastRecvA, lastRecvB>>

Termination ==
  /\ pcA = "done"
  /\ pcB = "done"
  /\ UNCHANGED vars

Next ==
  \/ ProcessA_Send
  \/ ProcessA_Receive
  \/ ProcessB_Receive
  \/ ProcessB_Echo
  \/ Termination

Spec == Init /\ [][Next]_vars
             /\ WF_vars(Next)
             /\ SF_vars(ProcessA_Send)
             /\ SF_vars(ProcessA_Receive)
             /\ SF_vars(ProcessB_Receive)
             /\ SF_vars(ProcessB_Echo)


\* Every message A sends is eventually echoed back
PropertyEcho ==
  \A m \in MessageValues:
    [](lastSentA = m => <>(lastRecvA = m))

\* Both processes eventually see the termination signal (-1)
PropertyTermination ==
  <>(lastRecvB = -1 /\ lastRecvA = -1)

\* A only receives messages it previously sent (no creation)
PropertyNoCreation ==
  \A m \in MessageValues:
    [](lastRecvA = m => m \in sentA)

=============================================================================
