---------------------------- MODULE PerfectLink  ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT MaxCrashes

LOCAL AppendMessage(set, msg) == set \cup {msg}

PerfectLink(senders, receivers) ==
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
    ELSE link.links[sender][receiver]

Send(link, sender, receiver, msg) ==
    [link EXCEPT !.links[sender][receiver] = AppendMessage(@, msg)]

Receive(link, sender, receiver, msg) ==
    [link EXCEPT !.links[sender][receiver] = link.links[sender][receiver] \ {msg}]

=============================================================================
