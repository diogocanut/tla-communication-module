---------------------------- MODULE StubbornLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxCopies

LOCAL WrapMessage(sender, receiver, msg, numCopy) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg, copy |-> numCopy ]

LOCAL DuplicableAppendMessage(link, sender, receiver, msg) == 
    link[receiver] \union { WrapMessage(sender, receiver, msg, copy) : copy \in 1..MaxCopies }

LOCAL DuplicableSend(link, sender, receiver, msg) == 
    [link EXCEPT ![receiver] = DuplicableAppendMessage(link, sender, receiver, msg)]

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

StubbornLink(processes) == [ p \in processes |-> {} ]

HasMessage(link, process) == link[process] /= {}

Messages(link, process) == { UnwrapMessage(m) : m \in link[process] }

Send(link, sender, receiver, msg) ==
    DuplicableSend(link, sender, receiver, msg)

Receive(link, process, msg) == 
    LET wrapped == CHOOSE m \in link[process] : UnwrapMessage(m) = msg
    IN [link EXCEPT ![process] = link[process] \ {wrapped}]

=============================================================================
