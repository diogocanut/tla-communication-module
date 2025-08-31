---------------------------- MODULE FairLossLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxDrops

LOCAL InitLink(linksPerProcess) == [links |-> linksPerProcess, nextMessageId |-> 0, totalDrops |-> 0]

LOCAL WrapMessage(sender, receiver, msg, id) == [ sender |-> sender, receiver |-> receiver, message |-> msg, messageId |-> id ]

LOCAL AppendMessage(link, sender, receiver, msg) == (link.links[receiver] \union {WrapMessage(sender, receiver, msg, link.nextMessageId)})

LOCAL ShouldDrop(link) == link.totalDrops < MaxDrops

LOCAL ReliableSend(link, sender, receiver, msg) == [
    links |-> [link.links EXCEPT ![receiver] = AppendMessage(link, sender, receiver, msg)],
    nextMessageId |-> link.nextMessageId + 1,
    totalDrops |-> link.totalDrops
]

LOCAL DropMessage(link) == [
    links |-> link.links,
    nextMessageId |-> link.nextMessageId,
    totalDrops |-> link.totalDrops + 1
]

UnwrapMessage(wrappedMessage) == wrappedMessage.message

FairLossLink(processes) == InitLink([ p \in processes |-> {} ])

HasMessage(link, process) == link.links[process] /= {}

Messages(link, process) == link.links[process]

Send(link, sender, receiver, msg, nonDeterministicShouldDrop) ==
        IF nonDeterministicShouldDrop /\ ShouldDrop(link)
        THEN DropMessage(link)
        ELSE ReliableSend(link, sender, receiver, msg)

Receive(link, process, wrappedMessage) == [
    links |-> [link.links EXCEPT ![process] = { m \in link.links[process]: m # wrappedMessage }],
    nextMessageId |-> link.nextMessageId,
    totalDrops |-> link.totalDrops
]

=============================================================================
