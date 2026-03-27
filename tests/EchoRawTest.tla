---------------------------- MODULE EchoRawTest ----------------------------
EXTENDS Integers, Sequences, TLC


Message(from, to, body) == [from |-> from, to |-> to, body |-> body]


VARIABLES network, toSend, sentA, receivedA,
          lastSentA, lastRecvA, lastRecvB,
          pcA, pcB

vars == <<network, toSend, sentA, receivedA, lastSentA, lastRecvA, lastRecvB, pcA, pcB>>

MessageSequence == <<1, 2, 3, -1>>
MessageValues == {MessageSequence[i] : i \in DOMAIN MessageSequence}

Init ==
  /\ network = {}
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
     /\ network' = network \cup {Message("A", "B", msg)}
     /\ lastSentA' = msg
     /\ sentA' = sentA \cup {msg}
     /\ toSend' = Tail(toSend)
     /\ pcA' = "waitEcho"
  /\ UNCHANGED <<pcB, lastRecvB, receivedA, lastRecvA>>

ProcessA_Receive ==
  /\ pcA = "waitEcho"
  /\ \E m \in network:
     /\ m.to = "A"
     /\ network' = network \ {m}
     /\ lastRecvA' = m.body
     /\ receivedA' = receivedA \cup {m.body}
     /\ pcA' = IF toSend = <<>> THEN "done" ELSE "send"
  /\ UNCHANGED <<pcB, toSend, lastSentA, sentA, lastRecvB>>

ProcessB_Receive ==
  /\ pcB = "waitMsg"
  /\ \E m \in network:
     /\ m.to = "B"
     /\ network' = network \ {m}
     /\ lastRecvB' = m.body
     /\ pcB' = "echo"
  /\ UNCHANGED <<pcA, toSend, lastSentA, sentA, receivedA, lastRecvA>>

ProcessB_Echo ==
  /\ pcB = "echo"
  /\ network' = network \cup {Message("B", "A", lastRecvB)}
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
