---------------------------- MODULE FairLossLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxDrops

LOCAL InitLink(senders, receivers) == 
    [links |-> [s \in senders |-> [ r \in receivers |-> {} ]], totalDrops |-> 0]

LOCAL ShouldDrop(link) == link.totalDrops < MaxDrops

LOCAL AppendMessage(set, msg) == set \union {msg}

LOCAL ReliableSend(link, sender, receiver, msg) == [
    links |-> [link.links EXCEPT ![sender][receiver] = AppendMessage(@, msg)],
    totalDrops |-> link.totalDrops
]

LOCAL DropMessage(link) == [
    links |-> link.links,
    totalDrops |-> link.totalDrops + 1
]

FairLossLink(senders, receivers) == InitLink(senders, receivers)

Messages(link, sender, receiver) == 
    link.links[sender][receiver]

\* Non-deterministic send: returns SET of possible next states (can deliver or drop)
Send(link, sender, receiver, msg) ==
    {ReliableSend(link, sender, receiver, msg)} \union
    (IF ShouldDrop(link) THEN {DropMessage(link)} ELSE {})

Receive(link, sender, receiver, msg) == 
    [links |-> [link.links EXCEPT ![sender][receiver] = link.links[sender][receiver] \ {msg}],
     totalDrops |-> link.totalDrops]

=============================================================================
