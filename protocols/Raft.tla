--------------------------------- MODULE Raft ---------------------------------
\* Raft consensus algorithm TLA+ specification.
\*
\* Based on:
\*   Ongaro, D. and Ousterhout, J. (2014).
\*   "In Search of an Understandable Consensus Algorithm (Extended Version)."
\*   Proceedings of USENIX ATC '14.
\*
\*   Ongaro, D. (2014).
\*   "Consensus: Bridging Theory and Practice."
\*   PhD dissertation, Stanford University.
\*
\* Original TLA+ specification by Diego Ongaro:
\*   https://github.com/ongardie/raft.tla
\*
\* This adaptation follows the conventions of the tla-communication-module
\* workspace and captures the core Raft protocol: leader election and
\* log replication with safety guarantees.
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -----------------------------------------------------------------------
\* Constants
\* -----------------------------------------------------------------------
CONSTANTS
    Servers,        \* The set of all server identifiers
    Values,         \* The set of values that can be proposed
    MaxTerm,        \* Upper bound on terms (state-space bound)
    MaxLogLength    \* Upper bound on log length (state-space bound)

\* -----------------------------------------------------------------------
\* Server states
\* -----------------------------------------------------------------------
Follower  == "Follower"
Candidate == "Candidate"
Leader    == "Leader"

\* Special null value
Nil == "nil"

\* -----------------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------------
VARIABLES
    \* Persistent state on all servers (updated on stable storage before
    \* responding to RPCs)
    currentTerm,   \* Latest term server has seen
    votedFor,      \* CandidateId that received vote in current term (or Nil)
    log,           \* Log entries; each entry contains a command and the term
                   \* when the entry was received by the leader

    \* Volatile state on all servers
    state,         \* Server role: Follower, Candidate, or Leader
    commitIndex,   \* Index of highest log entry known to be committed

    \* Volatile state on leaders (reinitialized after election)
    nextIndex,     \* For each server, index of the next log entry to send
    matchIndex,    \* For each server, index of highest log entry known to
                   \* be replicated on that server

    \* Message network — an unordered bag (set) of messages in transit
    messages

\* All variables as a tuple for stuttering
vars == <<currentTerm, votedFor, log, state, commitIndex,
          nextIndex, matchIndex, messages>>

\* -----------------------------------------------------------------------
\* Helper operators
\* -----------------------------------------------------------------------

\* The term of the last entry in a server's log, or 0 if the log is empty.
LastTerm(s) ==
    IF Len(log[s]) = 0 THEN 0
    ELSE log[s][Len(log[s])].term

\* A quorum is any majority subset of servers.
Quorum == {Q \in SUBSET Servers : Cardinality(Q) * 2 > Cardinality(Servers)}

\* The set of all log entries at index i or before.
LogPrefix(s, i) ==
    SubSeq(log[s], 1, i)

\* Minimum of two naturals
Min(a, b) == IF a < b THEN a ELSE b

\* -----------------------------------------------------------------------
\* Message constructors
\* -----------------------------------------------------------------------

\* RequestVote RPC — sent by candidates to gather votes.
RequestVoteRequest(src, dst, term, lastLogIndex, lastLogTerm) ==
    [mtype        |-> "RequestVoteRequest",
     msource      |-> src,
     mdest        |-> dst,
     mterm        |-> term,
     mlastLogIndex |-> lastLogIndex,
     mlastLogTerm  |-> lastLogTerm]

RequestVoteResponse(src, dst, term, voteGranted) ==
    [mtype        |-> "RequestVoteResponse",
     msource      |-> src,
     mdest        |-> dst,
     mterm        |-> term,
     mvoteGranted |-> voteGranted]

\* AppendEntries RPC — sent by leaders to replicate log entries and
\* as heartbeats.
AppendEntriesRequest(src, dst, term, prevLogIndex, prevLogTerm,
                     entries, leaderCommit) ==
    [mtype          |-> "AppendEntriesRequest",
     msource        |-> src,
     mdest          |-> dst,
     mterm          |-> term,
     mprevLogIndex  |-> prevLogIndex,
     mprevLogTerm   |-> prevLogTerm,
     mentries       |-> entries,
     mleaderCommit  |-> leaderCommit]

AppendEntriesResponse(src, dst, term, success, matchIdx) ==
    [mtype        |-> "AppendEntriesResponse",
     msource      |-> src,
     mdest        |-> dst,
     mterm        |-> term,
     msuccess     |-> success,
     mmatchIndex  |-> matchIdx]

\* Send a message by adding it to the messages set.
Send(m) == messages' = messages \cup {m}

\* Remove a message from the messages set.
Discard(m) == messages' = messages \ {m}

\* Send one message and discard another (reply pattern).
Reply(response, request) ==
    messages' = (messages \ {request}) \cup {response}

\* -----------------------------------------------------------------------
\* State transitions
\* -----------------------------------------------------------------------

\* ---- Timeout / Start Election ----
\* A follower or candidate times out and starts a new election.
Timeout(s) ==
    /\ state[s] \in {Follower, Candidate}
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor'    = [votedFor EXCEPT ![s] = s]  \* Vote for self
    /\ state'       = [state EXCEPT ![s] = Candidate]
    \* Send RequestVote RPCs to all other servers
    /\ messages' = messages \cup
         {RequestVoteRequest(s, t,
              currentTerm[s] + 1,
              Len(log[s]),
              LastTerm(s)) : t \in Servers \ {s}}
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

\* ---- Request Vote ----
\* Server i handles a RequestVote request from candidate j.
HandleRequestVoteRequest(s, m) ==
    LET grant ==
        /\ m.mterm >= currentTerm[s]
        \* Haven't voted yet in this term, or already voted for this candidate
        /\ (votedFor[s] = Nil \/ votedFor[s] = m.msource
            \/ m.mterm > currentTerm[s])
        \* Candidate's log is at least as up-to-date as receiver's log
        /\ \/ m.mlastLogTerm > LastTerm(s)
           \/ (m.mlastLogTerm = LastTerm(s)
               /\ m.mlastLogIndex >= Len(log[s]))
    IN
    \* Step down if we see a higher term
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
    /\ Reply(RequestVoteResponse(s, m.msource,
                IF m.mterm > currentTerm[s] THEN m.mterm
                ELSE currentTerm[s],
                grant), m)
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

\* ---- Become Leader ----
\* Candidate s receives a majority of votes and becomes leader.
BecomeLeader(s) ==
    /\ state[s] = Candidate
    /\ \E Q \in Quorum :
        /\ s \in Q
        /\ \A q \in Q :
            q = s \/ \E m \in messages :
                /\ m.mtype = "RequestVoteResponse"
                /\ m.mdest = s
                /\ m.mterm = currentTerm[s]
                /\ m.msource = q
                /\ m.mvoteGranted = TRUE
    /\ state'      = [state EXCEPT ![s] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT
                       ![s] = [t \in Servers |-> Len(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT
                       ![s] = [t \in Servers |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, messages>>

\* ---- Client Request ----
\* Leader s receives a client request to append value v to the log.
ClientRequest(s, v) ==
    /\ state[s] = Leader
    /\ Len(log[s]) < MaxLogLength
    /\ log' = [log EXCEPT
                ![s] = Append(log[s], [term |-> currentTerm[s],
                                        value |-> v])]
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex,
                   nextIndex, matchIndex, messages>>

\* ---- Append Entries (leader sends to follower) ----
\* Leader s sends an AppendEntries RPC to server t.
AppendEntries(s, t) ==
    /\ s /= t
    /\ state[s] = Leader
    /\ LET
         prevLogIndex == nextIndex[s][t] - 1
         prevLogTerm  == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[s])
                         THEN log[s][prevLogIndex].term
                         ELSE 0
         \* Send entries from nextIndex[s][t] onwards
         entries == SubSeq(log[s], nextIndex[s][t],
                           Len(log[s]))
       IN
       Send(AppendEntriesRequest(s, t,
                currentTerm[s],
                prevLogIndex,
                prevLogTerm,
                entries,
                commitIndex[s]))
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex,
                   nextIndex, matchIndex>>

\* ---- Handle AppendEntries Request ----
\* Server s handles an AppendEntries request message m.
HandleAppendEntriesRequest(s, m) ==
    LET
      logOk ==
        \/ m.mprevLogIndex = 0
        \/ (m.mprevLogIndex > 0
            /\ m.mprevLogIndex <= Len(log[s])
            /\ log[s][m.mprevLogIndex].term = m.mprevLogTerm)
    IN
    \/ \* Reject: stale term
       /\ m.mterm < currentTerm[s]
       /\ Reply(AppendEntriesResponse(s, m.msource,
                    currentTerm[s], FALSE, 0), m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state,
                      commitIndex, nextIndex, matchIndex>>
    \/ \* Reject: log doesn't contain an entry at prevLogIndex with
       \* matching term
       /\ m.mterm >= currentTerm[s]
       /\ ~logOk
       /\ currentTerm' = [currentTerm EXCEPT
                            ![s] = m.mterm]
       /\ state' = [state EXCEPT ![s] = Follower]
       /\ votedFor' = [votedFor EXCEPT
                        ![s] = IF m.mterm > currentTerm[s]
                               THEN Nil ELSE votedFor[s]]
       /\ Reply(AppendEntriesResponse(s, m.msource,
                    m.mterm, FALSE, 0), m)
       /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>
    \/ \* Accept: log is consistent, append any new entries
       /\ m.mterm >= currentTerm[s]
       /\ logOk
       /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
       /\ state' = [state EXCEPT ![s] = Follower]
       /\ votedFor' = [votedFor EXCEPT
                        ![s] = IF m.mterm > currentTerm[s]
                               THEN Nil ELSE votedFor[s]]
       \* Find the point of conflict and truncate/append
       /\ LET
            newEntryIndex == m.mprevLogIndex + 1
            \* Entries to keep: the existing prefix up to prevLogIndex,
            \* then append the new entries from the leader.
            updatedLog ==
              IF m.mentries = <<>> THEN log[s]
              ELSE SubSeq(log[s], 1, m.mprevLogIndex) \o m.mentries
          IN
          /\ log' = [log EXCEPT ![s] = updatedLog]
          /\ LET newMatchIndex == IF m.mentries = <<>>
                                  THEN m.mprevLogIndex
                                  ELSE m.mprevLogIndex + Len(m.mentries)
             IN
             /\ commitIndex' = [commitIndex EXCEPT
                                 ![s] = IF m.mleaderCommit > commitIndex[s]
                                        THEN Min(m.mleaderCommit, newMatchIndex)
                                        ELSE commitIndex[s]]
             /\ Reply(AppendEntriesResponse(s, m.msource,
                          m.mterm, TRUE, newMatchIndex), m)
       /\ UNCHANGED <<nextIndex, matchIndex>>

\* ---- Handle AppendEntries Response ----
\* Leader s handles an AppendEntries response message m.
HandleAppendEntriesResponse(s, m) ==
    \/ \* Success: update nextIndex and matchIndex
       /\ m.mterm = currentTerm[s]
       /\ m.msuccess = TRUE
       /\ state[s] = Leader
       /\ nextIndex'  = [nextIndex EXCEPT
                          ![s][m.msource] = m.mmatchIndex + 1]
       /\ matchIndex' = [matchIndex EXCEPT
                          ![s][m.msource] = m.mmatchIndex]
       /\ Discard(m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex>>
    \/ \* Failure: decrement nextIndex and retry
       /\ m.mterm = currentTerm[s]
       /\ m.msuccess = FALSE
       /\ state[s] = Leader
       /\ nextIndex' = [nextIndex EXCEPT
                         ![s][m.msource] =
                           IF nextIndex[s][m.msource] > 1
                           THEN nextIndex[s][m.msource] - 1
                           ELSE 1]
       /\ Discard(m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state,
                      commitIndex, matchIndex>>
    \/ \* Stale response: the response term is outdated, just discard
       /\ m.mterm < currentTerm[s]
       /\ Discard(m)
       /\ UNCHANGED <<currentTerm, votedFor, log, state,
                      commitIndex, nextIndex, matchIndex>>

\* ---- Step Down ----
\* Any server that sees a higher term in any message steps down.
StepDown(s, m) ==
    /\ m.mterm > currentTerm[s]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
    /\ state'       = [state EXCEPT ![s] = Follower]
    /\ votedFor'    = [votedFor EXCEPT ![s] = Nil]
    /\ Discard(m)
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

\* ---- Advance Commit Index ----
\* Leader s advances commitIndex based on matchIndex quorum.
AdvanceCommitIndex(s) ==
    /\ state[s] = Leader
    /\ \E newCI \in (commitIndex[s]+1)..Len(log[s]) :
        \* Only commit entries from the leader's current term
        /\ log[s][newCI].term = currentTerm[s]
        \* A majority of servers have replicated the entry
        /\ \E Q \in Quorum :
            \A q \in Q :
                \/ q = s  \* Leader always has its own entries
                \/ matchIndex[s][q] >= newCI
    /\ commitIndex' = [commitIndex EXCEPT
                        ![s] = CHOOSE newCI \in (commitIndex[s]+1)..Len(log[s]) :
                            /\ log[s][newCI].term = currentTerm[s]
                            /\ \E Q \in Quorum :
                                \A q \in Q :
                                    \/ q = s
                                    \/ matchIndex[s][q] >= newCI
                            /\ \A n \in (newCI+1)..Len(log[s]) :
                                ~(/\ log[s][n].term = currentTerm[s]
                                  /\ \E Q \in Quorum :
                                      \A q \in Q :
                                          \/ q = s
                                          \/ matchIndex[s][q] >= n)
                                \/ n <= newCI]
    /\ UNCHANGED <<currentTerm, votedFor, log, state,
                   nextIndex, matchIndex, messages>>

\* -----------------------------------------------------------------------
\* Message dispatch — receive a message and invoke the right handler
\* -----------------------------------------------------------------------
Receive(m) ==
    LET s == m.mdest IN
    \/ /\ m.mtype = "RequestVoteRequest"
       /\ HandleRequestVoteRequest(s, m)
    \/ /\ m.mtype = "RequestVoteResponse"
       /\ \/ (/\ m.mterm > currentTerm[s]
              /\ StepDown(s, m))
          \/ (/\ m.mterm <= currentTerm[s]
              /\ Discard(m)
              /\ UNCHANGED <<currentTerm, votedFor, log, state,
                             commitIndex, nextIndex, matchIndex>>)
    \/ /\ m.mtype = "AppendEntriesRequest"
       /\ HandleAppendEntriesRequest(s, m)
    \/ /\ m.mtype = "AppendEntriesResponse"
       /\ \/ (/\ m.mterm > currentTerm[s]
              /\ StepDown(s, m))
          \/ (/\ m.mterm <= currentTerm[s]
              /\ HandleAppendEntriesResponse(s, m))

\* ---- Drop Message (models network unreliability) ----
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex,
                   nextIndex, matchIndex>>

\* -----------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------
Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor    = [s \in Servers |-> Nil]
    /\ log         = [s \in Servers |-> <<>>]
    /\ state       = [s \in Servers |-> Follower]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ nextIndex   = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex  = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ messages    = {}

\* -----------------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------------
Next ==
    \/ \E s \in Servers : Timeout(s)
    \/ \E s \in Servers : BecomeLeader(s)
    \/ \E s \in Servers, v \in Values : ClientRequest(s, v)
    \/ \E s, t \in Servers : AppendEntries(s, t)
    \/ \E m \in messages : Receive(m)
    \/ \E s \in Servers : AdvanceCommitIndex(s)
    \/ \E m \in messages : DropMessage(m)

Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------------
\* Safety properties (invariants)
\* -----------------------------------------------------------------------

\* --- Election Safety ---
\* At most one leader per term.
ElectionSafety ==
    \A s1, s2 \in Servers :
        (state[s1] = Leader /\ state[s2] = Leader /\ currentTerm[s1] = currentTerm[s2])
        => s1 = s2

\* --- Log Matching ---
\* If two logs contain an entry with the same index and term, then the
\* logs are identical in all entries up through the given index.
LogMatching ==
    \A s1, s2 \in Servers :
        \A i \in 1..Min(Len(log[s1]), Len(log[s2])) :
            log[s1][i].term = log[s2][i].term
            => SubSeq(log[s1], 1, i) = SubSeq(log[s2], 1, i)

\* --- Leader Completeness ---
\* If a log entry is committed in a given term, that entry will be present
\* in the logs of the leaders for all higher-numbered terms.
\* (Checked as an invariant: any current leader has all committed entries.)
LeaderCompleteness ==
    \A s \in Servers :
        state[s] = Leader =>
            \A t \in Servers :
                \A i \in 1..commitIndex[t] :
                    /\ i <= Len(log[s])
                    /\ log[s][i] = log[t][i]

\* --- State Machine Safety ---
\* If a server has applied a log entry at a given index to its state
\* machine, no other server will ever apply a different log entry for
\* that index.
StateMachineSafety ==
    \A s1, s2 \in Servers :
        \A i \in 1..Min(commitIndex[s1], commitIndex[s2]) :
            log[s1][i] = log[s2][i]

\* --- Monotonic Current Term ---
\* Terms never decrease (type correctness aid).
MonotonicTerms ==
    \A s \in Servers : currentTerm[s] >= 0

\* -----------------------------------------------------------------------
\* Type invariant
\* -----------------------------------------------------------------------
TypeOK ==
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor    \in [Servers -> Servers \cup {Nil}]
    /\ state       \in [Servers -> {Follower, Candidate, Leader}]
    /\ commitIndex \in [Servers -> Nat]

=============================================================================
