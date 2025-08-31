---------------------------- MODULE StubbornLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxCopies

LOCAL InitLink(linksPerProcess) == [links |-> linksPerProcess, nextMessageId |-> 0]

LOCAL WrapMessage(sender, receiver, msg, id, numCopy) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg, messageId |-> id, copy |-> numCopy ]

LOCAL DuplicableAppendMessage(link, sender, receiver, msg) == 
    (link.links[receiver] \union { WrapMessage(sender, receiver, msg, link.nextMessageId, copy) : copy \in 1..MaxCopies })

LOCAL DuplicableSend(link, sender, receiver, msg) == [
    links |-> [link.links EXCEPT ![receiver] = DuplicableAppendMessage(link, sender, receiver, msg)],
    nextMessageId |-> link.nextMessageId + 1 
]

UnwrapMessage(wrappedMessage) == wrappedMessage.message

StubbornLink(processes) == InitLink([ p \in processes |-> {} ])

HasMessage(link, process) == link.links[process] /= {}

Messages(link, process) == link.links[process]

Send(link, sender, receiver, msg) ==
    DuplicableSend(link, sender, receiver, msg)

Receive(link, process, wrappedMessage) == [
    links |-> [link.links EXCEPT ![process] = { m \in link.links[process]: m # wrappedMessage }],
    nextMessageId |-> link.nextMessageId
]

=============================================================================
