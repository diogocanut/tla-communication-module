---------------------------- MODULE StubbornLink ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT MaxCopies

LOCAL CS == INSTANCE CrashStop

LOCAL WrapMessage(msg, numCopy) ==
    [ message |-> msg, copy |-> numCopy ]

LOCAL AppendMessage(set, msg) == set \union { WrapMessage(msg, copy) : copy \in 1..MaxCopies }

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

StubbornLink(senders, receivers) ==
    [links |-> [ s \in senders |-> [ r \in receivers |-> {} ] ]]

HasMessage(link, fm, sender, receiver) ==
    /\ ~CS!IsCrashed(fm, receiver)
    /\ link.links[sender][receiver] /= {}

Messages(link, fm, sender, receiver) ==
    IF CS!IsCrashed(fm, receiver) THEN {}
    ELSE { UnwrapMessage(m) : m \in link.links[sender][receiver] }

Send(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, sender) \/ CS!IsCrashed(fm, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = AppendMessage(@, msg)]

\* Total: receiving a message that is not in the buffer (or on a crashed
\* receiver) is a no-op, so callers need no guard beyond HasMessage/Messages.
Receive(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, receiver)
       \/ ~\E m \in link.links[sender][receiver] : UnwrapMessage(m) = msg
    THEN link
    ELSE LET wrapped == CHOOSE m \in link.links[sender][receiver] : UnwrapMessage(m) = msg
         IN [link EXCEPT !.links[sender][receiver] = link.links[sender][receiver] \ {wrapped}]

=============================================================================
