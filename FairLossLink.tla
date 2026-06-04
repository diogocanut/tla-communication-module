---------------------------- MODULE FairLossLink ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxDrops, MaxCrashes

LOCAL InitLink(senders, receivers) ==
    [links |-> [s \in senders |-> [ r \in receivers |-> {} ]],
     totalDrops |-> 0,
     crashed |-> {}]

LOCAL ShouldDrop(link) == link.totalDrops < MaxDrops

LOCAL AppendMessage(set, msg) == set \union {msg}

LOCAL ReliableSend(link, sender, receiver, msg) ==
    [link EXCEPT !.links[sender][receiver] = AppendMessage(@, msg)]

LOCAL DropMessage(link) ==
    [link EXCEPT !.totalDrops = link.totalDrops + 1]

FairLossLink(senders, receivers) == InitLink(senders, receivers)

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

\* Non-deterministic send: returns SET of possible next states (can deliver or drop).
\* If either endpoint has crashed, the send is a no-op.
Send(link, sender, receiver, msg) ==
    IF IsCrashed(link, sender) \/ IsCrashed(link, receiver) THEN {link}
    ELSE {ReliableSend(link, sender, receiver, msg)} \union
         (IF ShouldDrop(link) THEN {DropMessage(link)} ELSE {})

Receive(link, sender, receiver, msg) ==
    [link EXCEPT !.links[sender][receiver] = link.links[sender][receiver] \ {msg}]

=============================================================================
