--------------------------- MODULE AtomicBroadcastTest ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

INSTANCE AtomicBroadcast WITH MaxCrashes <- 1

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
        /\ channel' = Broadcast(channel, "g1", p, msg)
        /\ counter' = counter + 1
        /\ sent' = [sent EXCEPT ![p] = sent[p] \cup {msg}]
        /\ UNCHANGED <<received, receivedOrdered>>

ProcessReceive ==
    \E p \in Processes:
      /\ HasMessage(channel, "g1", p)
      /\ \E m \in Messages(channel, "g1", p):
          /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
          /\ receivedOrdered' = [receivedOrdered EXCEPT ![p] = Append(receivedOrdered[p], m)]
          /\ channel' = Deliver(channel, "g1", p)
          /\ UNCHANGED <<counter, sent>>

Termination ==
  /\ counter = totalCounter
  /\ \A p \in CorrectProcesses: ~HasMessage(channel, "g1", p)
  /\ UNCHANGED vars

\* Crash-stop model from Cachin
ProcessCrash ==
  \E p \in Processes:
    /\ ~IsCrashed(channel, p)
    /\ CanCrash(channel)
    /\ channel' = Crash(channel, p)
    /\ UNCHANGED <<counter, sent, received, receivedOrdered>>

Next ==
  \/ ProcessSend
  \/ ProcessReceive
  \/ ProcessCrash
  \/ Termination

Spec == Init /\ [][Next]_vars
             /\ WF_vars(Next)
             /\ SF_vars(ProcessSend)
             /\ SF_vars(ProcessReceive)

\* Type invariant
TypeOK ==
  /\ counter \in 0..totalCounter
  /\ \A p \in Processes: sent[p] \subseteq MessagesToSend
  /\ \A p \in Processes: received[p] \subseteq MessagesToSend
  /\ channel.crashed \subseteq Processes
  /\ \A g \in Groups: \A p \in Processes:
       \A i \in 1..Len(channel.links[g][p]): channel.links[g][p][i] \in MessagesToSend


\* Total Order Broadcast properties (Defago 1998)

\* (VALIDITY) If a correct process TO-broadcasts m, every correct process eventually TO-delivers m.
PropertyValidity ==
  \A p \in Processes:
    \A m \in MessagesToSend:
      (m \in sent[p] /\ [](~IsCrashed(channel, p)))
        => \A q \in Processes:
             [](~IsCrashed(channel, q)) => <>(m \in received[q])

\* (UNIFORM AGREEMENT) If a process TO-delivers m, all correct processes eventually TO-deliver m.
PropertyUniformAgreement ==
  \A m \in MessagesToSend:
    \A p1, p2 \in Processes:
      [](~IsCrashed(channel, p2))
        => [](m \in received[p1] => <>(m \in received[p2]))

Delivered(p, m) ==
  \E i \in 1..Len(receivedOrdered[p]): receivedOrdered[p][i] = m

\* (UNIFORM INTEGRITY) Part 1: Every process TO-delivers m at most once.
NoDuplicates(seq) ==
  \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]

InvariantUniformIntegrityAtMostOnce ==
  \A p \in Processes: NoDuplicates(receivedOrdered[p])

\* (UNIFORM INTEGRITY) Part 2: A process TO-delivers m only if m was previously TO-broadcast.
PropertyUniformIntegrity ==
  \A p \in Processes:
    \A m \in MessagesToSend:
      [](Delivered(p, m) => \E q \in Processes: m \in sent[q])


IndexOf(seq, m) ==
  CHOOSE i \in 1..Len(seq): seq[i] = m

DeliveredBefore(p, m1, m2) ==
  Delivered(p, m1) /\ Delivered(p, m2) /\
  IndexOf(receivedOrdered[p], m1) < IndexOf(receivedOrdered[p], m2)

\* (UNIFORM TOTAL ORDER) If p and q both TO-deliver m and m', then p delivers m before m' iff q does.
PropertyUniformTotalOrder ==
  \A m1, m2 \in MessagesToSend :
    \A p1, p2 \in Processes :
      (m1 # m2) /\ (p1 # p2) /\ [](~IsCrashed(channel, p2)) =>
        []( Delivered(p1,m1) /\ Delivered(p1,m2) /\ DeliveredBefore(p1,m1,m2)
            => <>DeliveredBefore(p2,m1,m2) )


=============================================================================