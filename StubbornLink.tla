---------------------------- MODULE StubbornLink ----------------------------
EXTENDS Integers, Sequences

CONSTANT MaxCopies

LOCAL WrapMessage(msg, numCopy) == 
    [ message |-> msg, copy |-> numCopy ]

LOCAL AppendMessage(set, msg) == set \union { WrapMessage(msg, copy) : copy \in 1..MaxCopies }

LOCAL DuplicableSend(link, sender, receiver, msg) == 
    [link EXCEPT ![sender][receiver] = AppendMessage(@, msg)]

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

StubbornLink(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> {} ] ]

Messages(link, sender, receiver) == 
    { UnwrapMessage(m) : m \in link[sender][receiver] }

Send(link, sender, receiver, msg) ==
    DuplicableSend(link, sender, receiver, msg)

Receive(link, sender, receiver, msg) == 
    LET wrapped == CHOOSE m \in link[sender][receiver] : UnwrapMessage(m) = msg
    IN [link EXCEPT ![sender][receiver] = link[sender][receiver] \ {wrapped}]

=============================================================================
