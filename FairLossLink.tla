---------------------------- MODULE FairLossLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxDrops

LOCAL InitLink(senders, receivers) == 
    [links |-> [ s \in senders |-> [ r \in receivers |-> {} ] ], totalDrops |-> 0]

LOCAL ShouldDrop(link) == link.totalDrops < MaxDrops

LOCAL ReliableSend(link, sender, receiver, msg) == [
    links |-> [link.links EXCEPT ![sender][receiver] = link.links[sender][receiver] \union {msg}],
    totalDrops |-> link.totalDrops
]

LOCAL DropMessage(link) == [
    links |-> link.links,
    totalDrops |-> link.totalDrops + 1
]

FairLossLink(senders, receivers) == InitLink(senders, receivers)

HasMessage(link, sender, receiver) == 
    link.links[sender][receiver] /= {}

Messages(link, sender, receiver) == 
    link.links[sender][receiver]

\* Non-deterministic send: can either deliver or drop the message
Send(link, sender, receiver, msg) ==
    \/ /\ ShouldDrop(link)
       /\ DropMessage(link)
    \/ ReliableSend(link, sender, receiver, msg)

Receive(link, sender, receiver, msg) == 
    [links |-> [link.links EXCEPT ![sender][receiver] = link.links[sender][receiver] \ {msg}],
     totalDrops |-> link.totalDrops]

=============================================================================
