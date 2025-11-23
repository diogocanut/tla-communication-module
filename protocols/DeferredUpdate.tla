----------------------------- MODULE DeferredUpdate -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

PLF == INSTANCE PerfectLinkFIFO
ABC == INSTANCE AtomicBroadcast

CONSTANTS
    Transactions,
    Servers,
    Keys,
    Groups

VARIABLES
    db,
    c2s,
    s2c,
    abcastQueue,
    outcomes,
    operations,
    writeSet,
    readSet,
    versions,
    pc,
    pendingRead,
    sent,
    received,
    decided
    
NULL == 0

NoMsg == [transaction |-> "none", rs |-> <<>>, ws |-> [x \in Keys |-> NULL]]

vars == <<db, c2s, s2c, abcastQueue, outcomes, operations, writeSet, readSet, versions, pc, pendingRead, sent, received, decided>>

Init ==
    /\ db = [s \in Servers |-> [k \in Keys |-> [val |-> NULL, ver |-> NULL]]]
    /\ c2s = PLF!PerfectLinkFIFO(Transactions, Servers)
    /\ s2c = PLF!PerfectLinkFIFO(Servers, Transactions)
    /\ abcastQueue = ABC!Channel(Groups, Servers)
    /\ outcomes = [t \in Transactions |-> "unknown"]
    /\ writeSet = [t \in Transactions |-> [k \in Keys |-> NULL]]
    /\ readSet = [t \in Transactions |-> <<>>]
    /\ versions = [t \in Transactions |-> NULL]
    /\ pc = [t \in Transactions |-> 1]
    /\ operations = 
        [ t \in Transactions |->
            IF t = "t1" THEN
                << [type |-> "write", key |-> "x", value |-> 11],
                [type |-> "read", key |-> "y"],
                [type |-> "write", key |-> "y", value |-> 21],
                [type |-> "commit"] >>
            ELSE IF t = "t2" THEN
                << [type |-> "read", key |-> "y"],
                [type |-> "read", key |-> "x"],
                [type |-> "write", key |-> "x", value |-> 12],
                [type |-> "commit"] >>
            ELSE
                << [type |-> "read", key |-> "x"],
                [type |-> "read", key |-> "y"],
                [type |-> "write", key |-> "y", value |-> 22],
                [type |-> "commit"] >>
        ]
    /\ pendingRead = [t \in Transactions |-> NULL]
    /\ sent = [t \in Transactions |-> {}]
    /\ received = [t \in Transactions |-> {}]
    /\ decided = [s \in Servers |-> [t \in Transactions |-> "none"]]

HasWritten(t, k) == writeSet[t][k] /= NULL

TransactionWrite(t, k, v) ==
    /\ writeSet' = [writeSet EXCEPT ![t][k] = v]
    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\ UNCHANGED <<db, c2s, s2c, abcastQueue, outcomes, operations, readSet, versions, pendingRead, sent, received, decided>>

TransactionCommit(t) ==
    /\ LET tx == [
            transaction   |-> t,
            rs            |-> readSet[t],
            ws            |-> writeSet[t]
       ] IN
        /\ abcastQueue' = ABC!Broadcast(abcastQueue, "g1", t, tx)
        /\ sent' = [sent EXCEPT ![t] =  {tx} \cup sent[t]]
        /\ outcomes' = [outcomes EXCEPT ![t] = "pending"]
        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\ UNCHANGED <<db, c2s, s2c, operations, writeSet, readSet, versions, pendingRead, received, decided>>

TransactionRead(t, op, s) ==
    \/ /\ HasWritten(t, op.key)
       /\ readSet' = [readSet EXCEPT ![t] = Append(readSet[t], <<op.key, writeSet[t][op.key], versions[t]>>)]
       /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
       /\ UNCHANGED <<db, c2s, s2c, abcastQueue, outcomes, operations, writeSet, versions, pendingRead, sent, received, decided>>

    \/ /\ ~HasWritten(t, op.key)
       /\ pendingRead[t] = NULL
       /\ c2s' = PLF!Send(c2s, t, s, [type |-> "read", key |-> op.key])
       /\ pendingRead' = [pendingRead EXCEPT ![t] = 1]
       /\ UNCHANGED <<db, s2c, abcastQueue, outcomes, operations, writeSet, readSet, versions, pc, sent, received, decided>>

    \/ /\ PLF!HasMessage(s2c, s, t)
       /\ LET msg == PLF!Message(s2c, s, t) IN
            /\ s2c' = PLF!Receive(s2c, s, t)
            /\ readSet' = [readSet EXCEPT ![t] = Append(readSet[t], <<msg.key, msg.value, msg.version>>)]
            /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
            /\ pendingRead' = [pendingRead EXCEPT ![t] = NULL]
       /\ UNCHANGED <<db, c2s, abcastQueue, outcomes, operations, writeSet, versions, sent, received, decided>>

TransactionAbort(t) ==
    /\ outcomes' = [outcomes EXCEPT ![t] = "aborted"]
    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\ UNCHANGED <<db, c2s, s2c, abcastQueue, operations, writeSet, readSet, versions, pendingRead, sent, received, decided>>

TransactionOperation(t) ==
    /\ t \in Transactions
    /\ pc[t] <= Len(operations[t])
    /\ LET op == operations[t][pc[t]] IN
        \/ /\ op.type = "read"
           /\ \E s \in Servers: TransactionRead(t, op, s) 
        \/ /\ op.type = "write"
           /\ TransactionWrite(t, op.key, op.value)
        \/ /\ op.type = "commit"
           /\ TransactionCommit(t)
        \/ /\ op.type = "abort"
           /\ TransactionAbort(t)

Valid(tx, s) ==
    \A i \in 1..Len(tx.rs):
        LET r == tx.rs[i] IN
        LET k == r[1] IN
        LET ver == r[3] IN
            db[s][k].ver <= ver

ApplyWrites(db_s, ws) ==
    [k \in DOMAIN db_s |->
        IF k \in DOMAIN ws
        THEN [val |-> ws[k], ver |-> db_s[k].ver + 1]
        ELSE db_s[k]
    ]

ServerApplyCommit(s) ==
    /\ ABC!HasMessage(abcastQueue, "g1", s) 
    /\ LET tx == ABC!Message(abcastQueue, "g1", s) IN
        /\ abcastQueue' = ABC!Deliver(abcastQueue, "g1", s)
        /\ received' = [received EXCEPT ![tx.transaction] = {tx} 
                            \cup received[tx.transaction]]
        /\ IF Valid(tx, s)
            THEN 
                /\ db' = [db EXCEPT ![s] = ApplyWrites(db[s], tx.ws)]
                /\ s2c' = PLF!Send( s2c, s, tx.transaction,
                        [ type    |-> "commitResponse",
                          outcome |-> "committed"])
                /\ decided' = [decided EXCEPT ![s][tx.transaction] = "committed"]
            ELSE
                /\ UNCHANGED db
                /\ s2c' = PLF!Send(s2c, s, tx.transaction,
                        [ type    |-> "commitResponse",
                          outcome |-> "aborted"])
                /\ decided' = [decided EXCEPT ![s][tx.transaction] = "aborted"]
        /\ UNCHANGED << c2s, writeSet, readSet, versions,
                        operations, pc, pendingRead, outcomes, sent >>

TransactionOutcome(t) ==
    /\ t \in Transactions
    /\ outcomes[t] = "pending"
    /\ \E s \in Servers:
        /\ PLF!HasMessage(s2c, s, t)
        /\ LET msg == PLF!Message(s2c, s, t) IN
               /\ s2c' = PLF!Receive(s2c, s, t)
               /\ msg.type = "commitResponse"
               /\ outcomes' = [outcomes EXCEPT ![t] = msg.outcome]
               /\ UNCHANGED <<db, c2s, abcastQueue, writeSet, readSet, versions, pc, operations, pendingRead, sent, received, decided>>

ServerRespondRead(s) ==
    \E t \in DOMAIN c2s :
        /\ PLF!HasMessage(c2s, t, s)
        /\ LET msg == PLF!Message(c2s, t, s) IN
               /\ c2s' = PLF!Receive(c2s, t, s)
               /\ IF msg.type = "read"
                  THEN
                      LET k == msg.key IN
                      LET response == [
                          type    |-> "readResponse",
                          key     |-> k,
                          value   |-> db[s][k].val,
                          version |-> db[s][k].ver
                      ] IN
                      /\ s2c' = PLF!Send(s2c, s, t, response)
                  ELSE
                      /\ UNCHANGED s2c
               /\ UNCHANGED <<db, abcastQueue, outcomes, writeSet, readSet, versions, operations, pc, pendingRead, sent, received, decided>>

Terminating ==
    /\ \A t \in Transactions: (outcomes[t] = "committed" \/ outcomes[t] = "aborted")
    /\ UNCHANGED vars

Next ==
    \/ \E t \in Transactions: TransactionOperation(t)
    \/ \E t \in Transactions: TransactionOutcome(t)
    \/ \E s \in Servers: ServerApplyCommit(s)
    \/ \E s \in Servers: ServerRespondRead(s)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Transactions:
         SF_vars(TransactionOperation(t))
       /\ SF_vars(TransactionOutcome(t))
    /\ \A s \in Servers:
         SF_vars(ServerApplyCommit(s))
       /\ SF_vars(ServerRespondRead(s))

\* abcast properties

ValidMessageDelivered(t) ==
  \A m \in sent[t]: m \in received[t]

\* Validaty
PropertyAmcValidity ==
  \A t \in Transactions: []<>(ValidMessageDelivered(t))

\* No Creation
PropertyAmcNoCreation ==
  \A t \in Transactions:
    \A m \in received[t]:
      \E t2 \in Transactions: m \in sent[t2]


\* REPLICATION PROPERTIES:
\* Transaction Termination
\* Uniform Total Order
\* DB1 – Uniform Consistency
\* DB2 – Uniform Consistency (Values)
\* TDB1 – Agreement


TransactionStarted(t) == pc[t] > 1
TransactionDecided(t) == outcomes[t] = "committed" \/ outcomes[t] = "aborted"

\* Transaction termination
PropertyTransactionTermination ==
  \A t \in Transactions:
    [](TransactionStarted(t) => <>(TransactionDecided(t)))

ServerFinished(s, t) ==
  decided[s][t] = "committed" \/ decided[s][t] = "aborted"
  
\* Uniform total order
PropertyUniformTotalOrder ==
  \A s1, s2 \in Servers:
    \A t1, t2 \in Transactions:
      [](ServerFinished(s1, t1) => <>ServerFinished(s1, t2)) 
        => [](ServerFinished(s2, t1) => <>ServerFinished(s2, t2))

\* DB1
PropertyDB1UniformConsistency ==
  \A s1, s2 \in Servers:
    \A k \in Keys:
      \A v \in 0..1:
        ([](db[s1][k].ver = v) => <>(db[s1][k].ver = v + 1))
        => ([](db[s2][k].ver = v) => <>(db[s2][k].ver = v + 1))

\* DB2
PropertyDB2ValueAgreement ==
  [](
       \A s1, s2 \in Servers:
         \A x \in Keys:
              db[s1][x].ver = db[s2][x].ver
           => db[s1][x].val = db[s2][x].val
     )

\* Isolation level properties
Read(t, k, v) ==
  \E i \in 1 .. Len(readSet[t]) :
       LET tup == readSet[t][i] IN tup[1] = k /\ tup[3] = v

ReadVal(t, k, val) ==
  \E i \in 1 .. Len(readSet[t]) :
       LET tup == readSet[t][i] IN tup[1] = k /\ tup[2] = val

WriteVal(t, k, val) ==
  writeSet[t][k] = val

TxCommitted(t) == outcomes[t] = "committed"
TxAborted(t)   == outcomes[t] = "aborted"
TxEnded(t)     == TxCommitted(t) \/ TxAborted(t)

\* Non-Repeatable Read: If a transaction reads two different versions for the same item, it must abort
TwoVersionsRead(t, k) ==
   \E i, j \in 1 .. Len(readSet[t]) :
        i # j /\
        readSet[t][i][1] = k /\
        readSet[t][j][1] = k /\
        readSet[t][i][3] # readSet[t][j][3]

Property_NonRepeatableRead ==
  \A t \in Transactions :
    []( TwoVersionsRead(t, "x") => <> TxAborted(t) )

\* Lost Update: Values written locally must be read locally before commit
Property_NoLostUpdate ==
  []( WriteVal("t2", "x", 12) => <> ReadVal("t2", "x", 12) )

\* Dirty Read: A transaction must not read a value from a transaction that aborts
Property_NoDirtyRead ==
  []~ReadVal("t2", "x", 11)

\* Write-Skew: If one transaction reads an updated value from another transaction committed before its own commit, the transaction must abort
T1CommittedBeforeT2ReadY ==
     TxCommitted("t1")
  /\ ReadVal("t2", "y", 21)

Property_NoWriteSkew ==
  []~(\E s \in Servers: TxCommitted("t1") /\ TxCommitted("t2")
                     /\ db[s]["x"].val = 12
                     /\ db[s]["y"].val = 21)

=============================================================================