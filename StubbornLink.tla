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

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

StubbornLink(processes) == InitLink([ p \in processes |-> {} ])

HasMessage(link, process) == link.links[process] /= {}

Messages(link, process) == { UnwrapMessage(m) : m \in link.links[process] }

Send(link, sender, receiver, msg) ==
    DuplicableSend(link, sender, receiver, msg)

Receive(link, process, msg) == 
    LET wrapped == CHOOSE m \in link.links[process] : UnwrapMessage(m) = msg
    IN [links |-> [link.links EXCEPT ![process] = link.links[process] \ {wrapped}],
        nextMessageId |-> link.nextMessageId]

=============================================================================
