------------------------------ MODULE RaftTest --------------------------------
\* Test harness for the Raft consensus protocol.
\*
\* Instantiates the Raft specification with a small configuration and
\* checks core safety invariants plus useful liveness properties.
\*
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Servers, Values, MaxTerm, MaxLogLength

VARIABLES
    currentTerm, votedFor, log, state, commitIndex,
    nextIndex, matchIndex, messages

R == INSTANCE Raft

vars == <<currentTerm, votedFor, log, state, commitIndex,
          nextIndex, matchIndex, messages>>

\* -----------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------
Init == R!Init

Next == R!Next

Spec == Init /\ [][Next]_vars
             /\ WF_vars(Next)

\* -----------------------------------------------------------------------
\* Helpers
\* -----------------------------------------------------------------------
Nil == "nil"

Follower  == "Follower"
Candidate == "Candidate"
Leader    == "Leader"

\* -----------------------------------------------------------------------
\* Safety properties — invariants
\* -----------------------------------------------------------------------

\* Type correctness
TypeOK == R!TypeOK

\* (Election Safety) At most one leader per term.
InvariantElectionSafety == R!ElectionSafety

\* (Log Matching) If two logs contain an entry with the same index and
\* term, then the logs are identical in all preceding entries.
InvariantLogMatching == R!LogMatching

\* (State Machine Safety) If a server has applied a log entry at a given
\* index, no other server will ever apply a different entry at that index.
InvariantStateMachineSafety == R!StateMachineSafety

\* (Leader Completeness) If a log entry is committed in a given term,
\* that entry is present in the logs of all leaders of higher terms.
InvariantLeaderCompleteness == R!LeaderCompleteness

\* -----------------------------------------------------------------------
\* Liveness properties — temporal
\* -----------------------------------------------------------------------

\* Eventually some server becomes a leader.
PropertyEventualLeader ==
    <>(\E s \in Servers : state[s] = Leader)

\* If a value is proposed by a client, it eventually appears committed on
\* some server (under fairness).
PropertyEventualCommit ==
    \A v \in Values :
        <>(\E s \in Servers : \E i \in 1..commitIndex[s] : log[s][i].value = v)

\* -----------------------------------------------------------------------
\* Useful for debugging / exploration
\* -----------------------------------------------------------------------

\* An alias for displaying in the TLC error trace
Alias ==
    [
        currentTerm |-> currentTerm,
        state       |-> state,
        votedFor    |-> votedFor,
        log         |-> log,
        commitIndex |-> commitIndex,
        nextIndex   |-> nextIndex,
        matchIndex  |-> matchIndex,
        numMessages |-> Cardinality(messages)
    ]

=============================================================================
