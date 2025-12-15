---------------------------- MODULE FairLossLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxDrops

LOCAL InitLink(linksPerProcess) == [links |-> linksPerProcess, totalDrops |-> 0]

LOCAL WrapMessage(sender, receiver, msg) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg ]

LOCAL AppendMessage(link, sender, receiver, msg) == 
    link.links[receiver] \union { WrapMessage(sender, receiver, msg) }

LOCAL ShouldDrop(link) == link.totalDrops < MaxDrops

LOCAL ReliableSend(link, sender, receiver, msg) == [
    links |-> [link.links EXCEPT ![receiver] = AppendMessage(link, sender, receiver, msg)],
    totalDrops |-> link.totalDrops
]

LOCAL DropMessage(link) == [
    links |-> link.links,
    totalDrops |-> link.totalDrops + 1
]

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

FairLossLink(processes) == InitLink([ p \in processes |-> {} ])

HasMessage(link, process) == link.links[process] /= {}

Messages(link, process) == { UnwrapMessage(m) : m \in link.links[process] }

\* Non-deterministic send: can either deliver or drop the message
Send(link, sender, receiver, msg) ==
    \/ /\ ShouldDrop(link)
       /\ DropMessage(link)
    \/ ReliableSend(link, sender, receiver, msg)

Receive(link, process, msg) == 
    LET wrapped == CHOOSE m \in link.links[process] : UnwrapMessage(m) = msg
    IN [links |-> [link.links EXCEPT ![process] = link.links[process] \ {wrapped}],
        totalDrops |-> link.totalDrops]

=============================================================================
