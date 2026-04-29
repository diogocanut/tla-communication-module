---------------------------- MODULE StubbornLink ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxCopies, MaxCrashes

LOCAL WrapMessage(msg, numCopy) ==
    [ message |-> msg, copy |-> numCopy ]

LOCAL AppendMessage(set, msg) == set \union { WrapMessage(msg, copy) : copy \in 1..MaxCopies }

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

StubbornLink(senders, receivers) ==
    [links |-> [ s \in senders |-> [ r \in receivers |-> {} ] ],
     crashed |-> {}]

IsCrashed(link, process) ==
    process \in link.crashed

CanCrash(link) ==
    Cardinality(link.crashed) < MaxCrashes

Crash(link, process) ==
    [link EXCEPT !.crashed = link.crashed \union {process}]

HasMessage(link, sender, receiver) ==
    /\ ~IsCrashed(link, receiver)
    /\ link.links[sender][receiver] /= {}

Messages(link, sender, receiver) ==
    IF IsCrashed(link, receiver) THEN {}
    ELSE { UnwrapMessage(m) : m \in link.links[sender][receiver] }

Send(link, sender, receiver, msg) ==
    [link EXCEPT !.links[sender][receiver] = AppendMessage(@, msg)]

Receive(link, sender, receiver, msg) ==
    LET wrapped == CHOOSE m \in link.links[sender][receiver] : UnwrapMessage(m) = msg
    IN [link EXCEPT !.links[sender][receiver] = link.links[sender][receiver] \ {wrapped}]

=============================================================================
