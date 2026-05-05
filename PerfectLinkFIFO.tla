-------------------------- MODULE PerfectLinkFIFO --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MaxCrashes

PerfectLinkFIFO(senders, receivers) ==
    [links |-> [ s \in senders |-> [ r \in receivers |-> <<>> ] ],
     crashed |-> {}]

IsCrashed(link, process) ==
    process \in link.crashed

CanCrash(link) ==
    Cardinality(link.crashed) < MaxCrashes

Crash(link, process) ==
    [link EXCEPT !.crashed = link.crashed \union {process}]

Send(link, sender, receiver, msg) ==
    IF IsCrashed(link, sender) \/ IsCrashed(link, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = Append(@, msg)]

HasMessage(link, sender, receiver) ==
    /\ ~IsCrashed(link, receiver)
    /\ link.links[sender][receiver] /= <<>>

Messages(link, sender, receiver) ==
    IF IsCrashed(link, receiver) \/ link.links[sender][receiver] = <<>> THEN {}
    ELSE {Head(link.links[sender][receiver])}

Receive(link, sender, receiver) ==
    [link EXCEPT !.links[sender][receiver] = Tail(@)]


=============================================================================
