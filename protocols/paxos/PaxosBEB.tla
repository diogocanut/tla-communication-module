------------------------------- MODULE PaxosBEB -------------------------------
(***************************************************************************
 Modified version of the Paxos TLA+ specification by Leslie Lamport.

 Original: https://github.com/tlaplus/Examples/tree/master/specifications/Paxos
           (specifications/Paxos/Paxos.tla, commit 47b0e2cc), together with
           Voting.tla and Consensus.tla, which this module refines.
 Paper:    Leslie Lamport. "The Part-Time Parliament." ACM Transactions on
           Computer Systems, 16(2), 1998, pp. 133-169.
           Leslie Lamport. "Paxos Made Simple." ACM SIGACT News, 32(4), 2001.
 License:  MIT (see upstream repository). The unmodified upstream modules
           are vendored in protocols/paxos/upstream/.

 Modifications from the original:
   - The set msgs of all messages ever sent is replaced by two channels of
     the TLA+ communication module library: phase 1a and 2a messages are
     broadcast by the ballot owner through BestEffortBroadcast, and phase
     1b and 2b messages travel from each acceptor to the ballot owner over
     PerfectLink. Messages are consumed when received.
   - Proposers are explicit processes. Ballot b belongs to proposer
     Owner(b) = b % |Proposer|. The owner keeps the 1b messages it received
     (promises), the value of the 2a it sent (proposal), the ballots it
     started (started) and the 2b votes it learned (accepted).
   - votes, a state function derived from the 2b messages in the original,
     is a variable of the acceptor updated in Phase2b.
   - The histories the inductive invariant Inv quantifies over are derived
     from the owner state and the messages in transit (Sent1b, Sent2a).
   - Crash semantics imported from the library's CrashStop module: a single
     failure-model value fm is consulted by every operator of both channels,
     and MaxCrashes exposes the crash bound at the protocol level.
 ***************************************************************************)
EXTENDS     Integers,
            FiniteSets,
            TLC

CONSTANTS   Acceptor,
            Proposer,
            Value,
            Quorum,
            MaxBallot,
            MaxCrashes

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

ASSUME ProposerAssumption == Proposer = 0..(Cardinality(Proposer) - 1)

CS  == INSTANCE CrashStop
BEB == INSTANCE BestEffortBroadcast
PL  == INSTANCE PerfectLink

Ballot == 0..MaxBallot

VotingBallot == Ballot

None == CHOOSE v : v \notin Value

Owner(b) == b % Cardinality(Proposer)

Group1a == "1a"
Group2a == "2a"

-------------------------------------------------------------------------------------

Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

-------------------------------------------------------------------------------------

VARIABLES   maxBal,
            maxVBal,
            maxVal,
            votes,
            promises,
            proposal,
            started,
            accepted,
            bcast,
            link,
            fm

vars == << maxBal, maxVBal, maxVal, votes, promises, proposal, started, accepted,
           bcast, link, fm >>

V == INSTANCE Voting

-------------------------------------------------------------------------------------

Init == /\ maxBal   = [a \in Acceptor |-> -1]
        /\ maxVBal  = [a \in Acceptor |-> -1]
        /\ maxVal   = [a \in Acceptor |-> None]
        /\ votes    = [a \in Acceptor |-> {}]
        /\ promises = [b \in Ballot |-> {}]
        /\ proposal = [b \in Ballot |-> None]
        /\ started  = {}
        /\ accepted = [b \in Ballot |-> {}]
        /\ bcast    = BEB!Channel({Group1a, Group2a}, Acceptor)
        /\ link     = PL!PerfectLink(Acceptor, Proposer)
        /\ fm       = CS!CrashStop(MaxCrashes)

-------------------------------------------------------------------------------------

Phase1a(b) ==
    /\ b \notin started
    /\ started' = started \cup {b}
    /\ \E out \in BEB!Broadcast(bcast, fm, Group1a, Owner(b), [type |-> "1a", bal |-> b]) :
        /\ bcast' = out.channel
        /\ fm'    = out.fm
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, promises, proposal, accepted, link>>

Receive1b(p) ==
    \E a \in Acceptor :
        /\ PL!HasMessage(link, fm, a, p)
        /\ \E m \in PL!Messages(link, fm, a, p) :
            /\ m.type = "1b"
            /\ link'     = PL!Receive(link, fm, a, p, m)
            /\ promises' = [promises EXCEPT ![m.bal] = @ \cup {m}]
            /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, proposal, started, accepted,
                           bcast, fm>>

Phase2a(b, v) ==
    /\ proposal[b] = None
    /\ \E Q \in Quorum :
        LET Q1b  == {m \in promises[b] : m.acc \in Q}
            Q1bv == {m \in Q1b : m.mbal \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal \geq mm.mbal
    /\ proposal' = [proposal EXCEPT ![b] = v]
    /\ \E out \in BEB!Broadcast(bcast, fm, Group2a, Owner(b), [type |-> "2a", bal |-> b, val |-> v]) :
        /\ bcast' = out.channel
        /\ fm'    = out.fm
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, promises, started, accepted, link>>

Learn(p) ==
    \E a \in Acceptor :
        /\ PL!HasMessage(link, fm, a, p)
        /\ \E m \in PL!Messages(link, fm, a, p) :
            /\ m.type = "2b"
            /\ link'     = PL!Receive(link, fm, a, p, m)
            /\ accepted' = [accepted EXCEPT ![m.bal] = @ \cup {<<m.acc, m.val>>}]
            /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, promises, proposal, started,
                           bcast, fm>>

ProposerActions(p) ==
    \/ \E b \in Ballot :
        /\ Owner(b) = p
        /\ \/ Phase1a(b)
           \/ \E v \in Value : Phase2a(b, v)
    \/ Receive1b(p)
    \/ Learn(p)

-------------------------------------------------------------------------------------

Phase1b(a) ==
    /\ BEB!HasMessage(bcast, fm, Group1a, a)
    /\ \E m \in BEB!Messages(bcast, fm, Group1a, a) :
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ bcast'  = BEB!Deliver(bcast, fm, Group1a, a, m)
        /\ link'   = PL!Send(link, fm, a, Owner(m.bal),
                             [type |-> "1b", acc |-> a, bal |-> m.bal,
                              mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal, votes, promises, proposal, started, accepted, fm>>

Phase2b(a) ==
    /\ BEB!HasMessage(bcast, fm, Group2a, a)
    /\ \E m \in BEB!Messages(bcast, fm, Group2a, a) :
        /\ m.bal \geq maxBal[a]
        /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
        /\ votes'   = [votes   EXCEPT ![a] = @ \cup {<<m.bal, m.val>>}]
        /\ bcast'   = BEB!Deliver(bcast, fm, Group2a, a, m)
        /\ link'    = PL!Send(link, fm, a, Owner(m.bal),
                              [type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
    /\ UNCHANGED <<promises, proposal, started, accepted, fm>>

AcceptorActions(a) ==
    \/ Phase1b(a)
    \/ Phase2b(a)

-------------------------------------------------------------------------------------

Crash(n) ==
    /\ CS!CanCrash(fm)
    /\ ~CS!IsCrashed(fm, n)
    /\ fm' = CS!Crash(fm, n)
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, promises, proposal, started, accepted,
                   bcast, link>>

-------------------------------------------------------------------------------------

Next == \/ \E p \in Proposer : ~CS!IsCrashed(fm, p) /\ ProposerActions(p)
        \/ \E a \in Acceptor : ~CS!IsCrashed(fm, a) /\ AcceptorActions(a)
        \/ \E n \in Acceptor \cup Proposer : Crash(n)

Spec == Init /\ [][Next]_vars

Symmetry == Permutations(Acceptor) \cup Permutations(Value)

-------------------------------------------------------------------------------------

Sent1b == UNION { {m \in link.links[a][p] : m.type = "1b"} : a \in Acceptor, p \in Proposer }
          \cup UNION { promises[b] : b \in Ballot }

Sent2a == { [type |-> "2a", bal |-> b, val |-> proposal[b]] :
            b \in {bb \in Ballot : proposal[bb] # None} }

-------------------------------------------------------------------------------------

TypeOK == /\ maxBal   \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal   \in [Acceptor -> Value \cup {None}]
          /\ votes    \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ promises \in [Ballot -> SUBSET Message]
          /\ proposal \in [Ballot -> Value \cup {None}]
          /\ started  \subseteq Ballot
          /\ accepted \in [Ballot -> SUBSET (Acceptor \X Value)]
          /\ \A g \in {Group1a, Group2a}, a \in Acceptor : bcast.links[g][a] \subseteq Message
          /\ \A a \in Acceptor, p \in Proposer : link.links[a][p] \subseteq Message
          /\ fm.crashed \subseteq Acceptor \cup Proposer

Inv == /\ TypeOK
       /\ \A a \in Acceptor : IF maxVBal[a] = -1
                                THEN maxVal[a] = None
                                ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]
       /\ \A m \in Sent1b :
             /\ maxBal[m.acc] \geq m.bal
             /\ (m.mbal \geq 0) => <<m.mbal, m.mval>> \in votes[m.acc]
       /\ \A m \in Sent2a :
             /\ \E Q \in Quorum : V!ShowsSafeAt(Q, m.bal, m.val)
             /\ \A mm \in Sent2a : mm.bal = m.bal => mm.val = m.val
       /\ V!Inv

InvOneChosen == Cardinality(V!chosen) <= 1

Learned(p, v) == \E b \in Ballot :
                    /\ Owner(b) = p
                    /\ \E Q \in Quorum : \A a \in Q : <<a, v>> \in accepted[b]

InvLearned == \A p \in Proposer, v \in Value : Learned(p, v) => v \in V!chosen

VotingSpecBar == V!Spec

THEOREM Spec => ([]TypeOK) /\ ([]Inv) /\ ([]InvOneChosen) /\ ([]InvLearned) /\ V!Spec

=============================================================================
