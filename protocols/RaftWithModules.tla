--------------------------- MODULE RaftWithModules ----------------------------
\* Raft consensus algorithm using the tla-communication-module library:
\*
\*   - PerfectLinkFIFO  for all server-to-server RPCs
\*     (replaces the raw message-bag model in Raft.tla)
\*
\*   - AtomicBroadcast   for the committed-log output layer
\*     (the leader broadcasts each newly committed entry via ABC;
\*      every server delivers from ABC, yielding the total-order
\*      replicated state-machine input)
\*
\* Because PerfectLinkFIFO guarantees reliable, in-order delivery,
\* this spec models a network WITHOUT message loss (comparable to TCP).
\* The DropMessage action from Raft.tla is therefore absent.
\*
\* Reference:
\*   Ongaro, D. and Ousterhout, J. (2014).
\*   "In Search of an Understandable Consensus Algorithm (Extended Version)."
\*   Proceedings of USENIX ATC '14.
\*   Original TLA+: https://github.com/ongardie/raft.tla
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -----------------------------------------------------------------------
\* Library modules
\* -----------------------------------------------------------------------
PLF == INSTANCE PerfectLinkFIFO
ABC == INSTANCE AtomicBroadcast

\* -----------------------------------------------------------------------
\* Constants
\* -----------------------------------------------------------------------
CONSTANTS
    Servers,         \* Set of server identifiers
    Values,          \* Set of values that can be proposed
    MaxTerm,         \* Upper bound on terms  (state-space bound)
    MaxLogLength,    \* Upper bound on log length (state-space bound)
    Groups           \* ABC group set — typically {"g1"}

\* -----------------------------------------------------------------------
\* Server roles
\* -----------------------------------------------------------------------
Follower  == "Follower"
Candidate == "Candidate"
Leader    == "Leader"

Nil == "nil"

\* -----------------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------------
VARIABLES
    \* -- Persistent state (stable storage) --
    currentTerm,    \* [Servers -> Nat]         latest term seen
    votedFor,       \* [Servers -> Servers|Nil] vote granted in current term
    log,            \* [Servers -> Seq(entry)]  log entries [term, value]

    \* -- Volatile state --
    state,          \* [Servers -> {Follower,Candidate,Leader}]
    commitIndex,    \* [Servers -> Nat]  highest committed log index

    \* -- Leader-only volatile state --
    nextIndex,      \* [Servers -> [Servers -> Nat]]
    matchIndex,     \* [Servers -> [Servers -> Nat]]

    \* -- Candidate-only state --
    votesGranted,   \* [Servers -> SUBSET Servers]  votes received

    \* -- Communication: PerfectLinkFIFO (server ↔ server RPCs) --
    rpc,            \* PLF channel  [Servers -> [Servers -> Seq(msg)]]

    \* -- Committed output: AtomicBroadcast --
    commitLog,      \* ABC channel  [Groups -> [Servers -> Seq(entry)]]
    broadcastIndex, \* Nat — global: entries 1..broadcastIndex have been
                    \*               broadcast via ABC by the leader
    delivered       \* [Servers -> Seq(entry)]  entries delivered from ABC

vars == <<currentTerm, votedFor, log, state, commitIndex,
          nextIndex, matchIndex, votesGranted,
          rpc, commitLog, broadcastIndex, delivered>>

\* -----------------------------------------------------------------------
\* Helpers
\* -----------------------------------------------------------------------

LastTerm(s) ==
    IF Len(log[s]) = 0 THEN 0
    ELSE log[s][Len(log[s])].term

Quorum == {Q \in SUBSET Servers : Cardinality(Q) * 2 > Cardinality(Servers)}

Min(a, b) == IF a < b THEN a ELSE b

\* Pop the head of the queue from→to AND append a reply to→from,
\* composing PLF!Receive and PLF!Send in one step.
ReceiveAndReply(link, from, to, replyMsg) ==
    PLF!Send(PLF!Receive(link, from, to), to, from, replyMsg)

\* Send the same message from 'sender' to every server in 'receivers'
\* by updating all target queues in one expression.
SendToEach(link, sender, receivers, msg) ==
    [s \in DOMAIN link |->
        [r \in DOMAIN link[s] |->
            IF s = sender /\ r \in receivers
            THEN Append(link[s][r], msg)
            ELSE link[s][r]]]

\* -----------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------
Init ==
    /\ currentTerm   = [s \in Servers |-> 0]
    /\ votedFor      = [s \in Servers |-> Nil]
    /\ log           = [s \in Servers |-> <<>>]
    /\ state         = [s \in Servers |-> Follower]
    /\ commitIndex   = [s \in Servers |-> 0]
    /\ nextIndex     = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex    = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ votesGranted  = [s \in Servers |-> {}]
    /\ rpc           = PLF!PerfectLinkFIFO(Servers, Servers)
    /\ commitLog     = ABC!Channel(Groups, Servers)
    /\ broadcastIndex = 0
    /\ delivered     = [s \in Servers |-> <<>>]

\* =======================================================================
\*  LEADER ELECTION
\* =======================================================================

\* ---- Timeout / Start Election ----
\* A follower or candidate times out and starts a new election.
\* Sends RequestVote to every other server via PerfectLinkFIFO.
Timeout(s) ==
    /\ state[s] \in {Follower, Candidate}
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm'  = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor'     = [votedFor EXCEPT ![s] = s]
    /\ state'        = [state EXCEPT ![s] = Candidate]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]  \* vote for self
    /\ rpc' = SendToEach(rpc, s, Servers \ {s},
                [mtype         |-> "RequestVoteRequest",
                 msource       |-> s,
                 mterm         |-> currentTerm[s] + 1,
                 mlastLogIndex |-> Len(log[s]),
                 mlastLogTerm  |-> LastTerm(s)])
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex,
                   commitLog, broadcastIndex, delivered>>

\* ---- Handle RequestVote Request ----
\* Receive a RequestVote from the PLF queue, decide whether to grant the
\* vote, and reply via PLF in the same atomic step.
HandleRequestVoteRequest(s) ==
    \E sender \in Servers \ {s}:
      \E m \in PLF!Messages(rpc, sender, s):
        /\ m.mtype = "RequestVoteRequest"
        /\ LET grant ==
               /\ m.mterm >= currentTerm[s]
                \* Haven't voted yet in this term, or already voted for this candidate
               /\ (votedFor[s] = Nil \/ votedFor[s] = m.msource
                   \/ m.mterm > currentTerm[s])
               /\ \/ m.mlastLogTerm > LastTerm(s)
                  \/ (m.mlastLogTerm = LastTerm(s)
                      /\ m.mlastLogIndex >= Len(log[s]))
           IN
           /\ currentTerm' = [currentTerm EXCEPT
                ![s] = IF m.mterm > currentTerm[s]
                       THEN m.mterm ELSE currentTerm[s]]
           /\ votedFor' = [votedFor EXCEPT
                ![s] = IF grant THEN m.msource
                       ELSE IF m.mterm > currentTerm[s] THEN Nil
                       ELSE votedFor[s]]
           /\ state' = [state EXCEPT
                ![s] = IF m.mterm > currentTerm[s] THEN Follower
                       ELSE state[s]]
           /\ rpc' = ReceiveAndReply(rpc, sender, s,
                [mtype        |-> "RequestVoteResponse",
                 msource      |-> s,
                 mterm        |-> IF m.mterm > currentTerm[s]
                                  THEN m.mterm ELSE currentTerm[s],
                 mvoteGranted |-> grant])
           /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex,
                          votesGranted, commitLog, broadcastIndex,
                          delivered>>

\* ---- Handle RequestVote Response ----
\* Consume the head vote-response from the PLF queue.
\* If the term is higher, step down.  Otherwise, if the server is still
\* a candidate in the matching term, record the vote.
HandleRequestVoteResponse(s) ==
    \E sender \in Servers \ {s}:
      \E m \in PLF!Messages(rpc, sender, s):
        /\ m.mtype = "RequestVoteResponse"
        /\ \/ \* Higher term → step down
              /\ m.mterm > currentTerm[s]
              /\ currentTerm'  = [currentTerm EXCEPT ![s] = m.mterm]
              /\ state'        = [state EXCEPT ![s] = Follower]
              /\ votedFor'     = [votedFor EXCEPT ![s] = Nil]
              /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
              /\ rpc'          = PLF!Receive(rpc, sender, s)
              /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
           \/ \* Current or stale term — record vote if applicable, consume msg
              /\ m.mterm <= currentTerm[s]
              /\ IF m.mterm = currentTerm[s]
                    /\ state[s] = Candidate
                    /\ m.mvoteGranted
                 THEN votesGranted' = [votesGranted EXCEPT
                        ![s] = votesGranted[s] \cup {sender}]
                 ELSE UNCHANGED votesGranted
              /\ rpc' = PLF!Receive(rpc, sender, s)
              /\ UNCHANGED <<currentTerm, votedFor, state, log,
                             commitIndex, nextIndex, matchIndex>>
        /\ UNCHANGED <<commitLog, broadcastIndex, delivered>>

\* ---- Become Leader ----
\* A candidate that has collected votes from a quorum transitions to Leader.
BecomeLeader(s) ==
    /\ state[s] = Candidate
    /\ \E Q \in Quorum : Q \subseteq votesGranted[s]
    /\ state'      = [state EXCEPT ![s] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT
                       ![s] = [t \in Servers |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT
                       ![s] = [t \in Servers |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex,
                   votesGranted, rpc, commitLog, broadcastIndex,
                   delivered>>

\* =======================================================================
\*  LOG REPLICATION
\* =======================================================================

\* ---- Client Request ----
\* The leader appends a new entry to its own log.
ClientRequest(s, v) ==
    /\ state[s] = Leader
    /\ Len(log[s]) < MaxLogLength
    /\ log' = [log EXCEPT
                ![s] = Append(log[s], [term  |-> currentTerm[s],
                                        value |-> v])]
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex,
                   nextIndex, matchIndex, votesGranted, rpc,
                   commitLog, broadcastIndex, delivered>>

\* ---- Send AppendEntries ----
\* Leader s sends an AppendEntries RPC to follower t via PerfectLinkFIFO.
SendAppendEntries(s, t) ==
    /\ s /= t
    /\ state[s] = Leader
    /\ LET
         prevLogIndex == nextIndex[s][t] - 1
         prevLogTerm  == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[s])
                         THEN log[s][prevLogIndex].term
                         ELSE 0
         entries == SubSeq(log[s], nextIndex[s][t], Len(log[s]))
       IN
       rpc' = PLF!Send(rpc, s, t,
                [mtype         |-> "AppendEntriesRequest",
                 msource       |-> s,
                 mterm         |-> currentTerm[s],
                 mprevLogIndex |-> prevLogIndex,
                 mprevLogTerm  |-> prevLogTerm,
                 mentries      |-> entries,
                 mleaderCommit |-> commitIndex[s]])
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex,
                   nextIndex, matchIndex, votesGranted,
                   commitLog, broadcastIndex, delivered>>

\* ---- Handle AppendEntries Request ----
\* Follower s processes an AppendEntries from the PLF queue and replies.
HandleAppendEntriesRequest(s) ==
    \E sender \in Servers \ {s}:
      \E m \in PLF!Messages(rpc, sender, s):
        /\ m.mtype = "AppendEntriesRequest"
        /\ LET logOk ==
               \/ m.mprevLogIndex = 0
               \/ (m.mprevLogIndex > 0
                   /\ m.mprevLogIndex <= Len(log[s])
                   /\ log[s][m.mprevLogIndex].term = m.mprevLogTerm)
           IN
           \/ \* REJECT — stale term
              /\ m.mterm < currentTerm[s]
              /\ rpc' = ReceiveAndReply(rpc, sender, s,
                    [mtype       |-> "AppendEntriesResponse",
                     msource     |-> s,
                     mterm       |-> currentTerm[s],
                     msuccess    |-> FALSE,
                     mmatchIndex |-> 0])
              /\ UNCHANGED <<currentTerm, votedFor, log, state,
                             commitIndex, nextIndex, matchIndex,
                             votesGranted, commitLog, broadcastIndex,
                             delivered>>
           \/ \* REJECT — log mismatch (term is ok)
              /\ m.mterm >= currentTerm[s]
              /\ ~logOk
              /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
              /\ state'       = [state EXCEPT ![s] = Follower]
              /\ votedFor'    = [votedFor EXCEPT
                    ![s] = IF m.mterm > currentTerm[s]
                           THEN Nil ELSE votedFor[s]]
              /\ rpc' = ReceiveAndReply(rpc, sender, s,
                    [mtype       |-> "AppendEntriesResponse",
                     msource     |-> s,
                     mterm       |-> m.mterm,
                     msuccess    |-> FALSE,
                     mmatchIndex |-> 0])
              /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex,
                             votesGranted, commitLog, broadcastIndex,
                             delivered>>
           \/ \* ACCEPT — log is consistent, append new entries
              /\ m.mterm >= currentTerm[s]
              /\ logOk
              /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
              /\ state'       = [state EXCEPT ![s] = Follower]
              /\ votedFor'    = [votedFor EXCEPT
                    ![s] = IF m.mterm > currentTerm[s]
                           THEN Nil ELSE votedFor[s]]
              /\ LET
                   updatedLog ==
                     IF m.mentries = <<>> THEN log[s]
                     ELSE SubSeq(log[s], 1, m.mprevLogIndex) \o m.mentries
                   newMatchIdx ==
                     IF m.mentries = <<>>
                     THEN m.mprevLogIndex
                     ELSE m.mprevLogIndex + Len(m.mentries)
                 IN
                 /\ log' = [log EXCEPT ![s] = updatedLog]
                 /\ commitIndex' = [commitIndex EXCEPT
                      ![s] = IF m.mleaderCommit > commitIndex[s]
                             THEN Min(m.mleaderCommit, newMatchIdx)
                             ELSE commitIndex[s]]
                 /\ rpc' = ReceiveAndReply(rpc, sender, s,
                      [mtype       |-> "AppendEntriesResponse",
                       msource     |-> s,
                       mterm       |-> m.mterm,
                       msuccess    |-> TRUE,
                       mmatchIndex |-> newMatchIdx])
              /\ UNCHANGED <<nextIndex, matchIndex, votesGranted,
                             commitLog, broadcastIndex, delivered>>

\* ---- Handle AppendEntries Response ----
\* Leader s processes a response from the PLF queue.
HandleAppendEntriesResponse(s) ==
    \E sender \in Servers \ {s}:
      \E m \in PLF!Messages(rpc, sender, s):
        /\ m.mtype = "AppendEntriesResponse"
        /\ \/ \* Higher term → step down
              /\ m.mterm > currentTerm[s]
              /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
              /\ state'       = [state EXCEPT ![s] = Follower]
              /\ votedFor'    = [votedFor EXCEPT ![s] = Nil]
              /\ rpc'         = PLF!Receive(rpc, sender, s)
              /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex,
                             votesGranted>>
           \/ \* Success — advance nextIndex and matchIndex
              /\ m.mterm = currentTerm[s]
              /\ m.msuccess
              /\ state[s] = Leader
              /\ nextIndex'  = [nextIndex EXCEPT
                    ![s][sender] = m.mmatchIndex + 1]
              /\ matchIndex' = [matchIndex EXCEPT
                    ![s][sender] = m.mmatchIndex]
              /\ rpc' = PLF!Receive(rpc, sender, s)
              /\ UNCHANGED <<currentTerm, votedFor, log, state,
                             commitIndex, votesGranted>>
           \/ \* Failure — decrement nextIndex
              /\ m.mterm = currentTerm[s]
              /\ ~m.msuccess
              /\ state[s] = Leader
              /\ nextIndex' = [nextIndex EXCEPT
                    ![s][sender] = IF nextIndex[s][sender] > 1
                                   THEN nextIndex[s][sender] - 1
                                   ELSE 1]
              /\ rpc' = PLF!Receive(rpc, sender, s)
              /\ UNCHANGED <<currentTerm, votedFor, log, state,
                             commitIndex, matchIndex, votesGranted>>
           \/ \* Stale or not leader — discard
              /\ m.mterm <= currentTerm[s]
              /\ (m.mterm < currentTerm[s] \/ state[s] /= Leader)
              /\ rpc' = PLF!Receive(rpc, sender, s)
              /\ UNCHANGED <<currentTerm, votedFor, log, state,
                             commitIndex, nextIndex, matchIndex,
                             votesGranted>>
        /\ UNCHANGED <<commitLog, broadcastIndex, delivered>>

\* =======================================================================
\*  COMMIT & ATOMIC BROADCAST OUTPUT
\* =======================================================================

\* ---- Advance Commit Index ----
\* Leader s checks whether a quorum has replicated an entry from the
\* current term, and advances commitIndex accordingly.
AdvanceCommitIndex(s) ==
    /\ state[s] = Leader
    /\ \E newCI \in (commitIndex[s]+1)..Len(log[s]) :
        /\ log[s][newCI].term = currentTerm[s]
        /\ \E Q \in Quorum :
            \A q \in Q : q = s \/ matchIndex[s][q] >= newCI
        /\ commitIndex' = [commitIndex EXCEPT ![s] = newCI]
    /\ UNCHANGED <<currentTerm, votedFor, log, state,
                   nextIndex, matchIndex, votesGranted, rpc,
                   commitLog, broadcastIndex, delivered>>

\* ---- Broadcast Committed Entry via AtomicBroadcast ----
\* The leader publishes the next un-broadcast committed entry to the
\* ABC channel.  'broadcastIndex' ensures each entry is broadcast
\* exactly once, even across leader changes.
BroadcastCommitted(s) ==
    /\ state[s] = Leader
    /\ broadcastIndex < commitIndex[s]
    /\ LET idx == broadcastIndex + 1
           entry == [index |-> idx,
                     term  |-> log[s][idx].term,
                     value |-> log[s][idx].value]
       IN
       /\ commitLog' = ABC!Broadcast(commitLog, "g1", s, entry)
       /\ broadcastIndex' = idx
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex,
                   nextIndex, matchIndex, votesGranted, rpc,
                   delivered>>

\* ---- Deliver Committed Entry from AtomicBroadcast ----
\* Any server consumes the next entry from the ABC channel.
\* The 'delivered' sequence is the total-order state-machine input.
DeliverCommitted(s) ==
    /\ ABC!HasMessage(commitLog, "g1", s)
    /\ \E entry \in ABC!Messages(commitLog, "g1", s):
        /\ delivered'  = [delivered EXCEPT
                           ![s] = Append(delivered[s], entry)]
        /\ commitLog'  = ABC!Deliver(commitLog, "g1", s)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex,
                   nextIndex, matchIndex, votesGranted, rpc,
                   broadcastIndex>>

\* =======================================================================
\*  SPECIFICATION
\* =======================================================================

Next ==
    \* Election
    \/ \E s \in Servers : Timeout(s)
    \/ \E s \in Servers : HandleRequestVoteRequest(s)
    \/ \E s \in Servers : HandleRequestVoteResponse(s)
    \/ \E s \in Servers : BecomeLeader(s)
    \* Log replication
    \/ \E s \in Servers, v \in Values : ClientRequest(s, v)
    \/ \E s, t \in Servers : SendAppendEntries(s, t)
    \/ \E s \in Servers : HandleAppendEntriesRequest(s)
    \/ \E s \in Servers : HandleAppendEntriesResponse(s)
    \* Commit & ABC output
    \/ \E s \in Servers : AdvanceCommitIndex(s)
    \/ \E s \in Servers : BroadcastCommitted(s)
    \/ \E s \in Servers : DeliverCommitted(s)

Spec == Init /\ [][Next]_vars
             /\ WF_vars(Next)

\* =======================================================================
\*  SAFETY PROPERTIES — Raft invariants
\* =======================================================================

\* At most one leader per term.
ElectionSafety ==
    \A s1, s2 \in Servers :
        (state[s1] = Leader /\ state[s2] = Leader
         /\ currentTerm[s1] = currentTerm[s2])
        => s1 = s2

\* If two logs share the same index and term, their prefixes are identical.
LogMatching ==
    \A s1, s2 \in Servers :
        \A i \in 1..Min(Len(log[s1]), Len(log[s2])) :
            log[s1][i].term = log[s2][i].term
            => SubSeq(log[s1], 1, i) = SubSeq(log[s2], 1, i)

\* No two servers commit different entries at the same index.
StateMachineSafety ==
    \A s1, s2 \in Servers :
        \A i \in 1..Min(commitIndex[s1], commitIndex[s2]) :
            log[s1][i] = log[s2][i]

\* A leader's log contains every previously committed entry.
LeaderCompleteness ==
    \A s \in Servers :
        state[s] = Leader =>
            \A t \in Servers :
                \A i \in 1..commitIndex[t] :
                    /\ i <= Len(log[s])
                    /\ log[s][i] = log[t][i]

\* =======================================================================
\*  SAFETY PROPERTIES — AtomicBroadcast / Total Order Broadcast
\*  (Défago, Schiper, Urbán, 2004)
\* =======================================================================

\* (TOTAL ORDER) All servers deliver entries in the same order.
\* For any two servers, the shorter delivered sequence is a prefix
\* of the longer one.
PropertyTotalOrderDelivery ==
    \A s1, s2 \in Servers :
        LET len == Min(Len(delivered[s1]), Len(delivered[s2])) IN
        SubSeq(delivered[s1], 1, len) = SubSeq(delivered[s2], 1, len)

\* (UNIFORM INTEGRITY) Each log index is delivered at most once per server.
\* Entries carry an 'index' field to provide unique identity.
NoDuplicateDeliveries(seq) ==
    \A i, j \in 1..Len(seq) : i /= j => seq[i].index /= seq[j].index

PropertyUniformIntegrity ==
    \A s \in Servers : NoDuplicateDeliveries(delivered[s])

\* -----------------------------------------------------------------------
\* Type invariant
\* -----------------------------------------------------------------------
TypeOK ==
    /\ currentTerm   \in [Servers -> Nat]
    /\ votedFor      \in [Servers -> Servers \cup {Nil}]
    /\ state         \in [Servers -> {Follower, Candidate, Leader}]
    /\ commitIndex   \in [Servers -> Nat]
    /\ broadcastIndex \in Nat

=============================================================================
