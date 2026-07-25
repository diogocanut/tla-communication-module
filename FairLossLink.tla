---------------------------- MODULE FairLossLink ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT MaxDrops

LOCAL CS == INSTANCE CrashStop

LOCAL InitLink(senders, receivers) ==
    [links |-> [s \in senders |-> [ r \in receivers |-> {} ]],
     totalDrops |-> 0]

LOCAL ShouldDrop(link) == link.totalDrops < MaxDrops

LOCAL AppendMessage(set, msg) == set \union {msg}

LOCAL ReliableSend(link, sender, receiver, msg) ==
    [link EXCEPT !.links[sender][receiver] = AppendMessage(@, msg)]

LOCAL DropMessage(link) ==
    [link EXCEPT !.totalDrops = link.totalDrops + 1]

FairLossLink(senders, receivers) == InitLink(senders, receivers)

HasMessage(link, fm, sender, receiver) ==
    /\ ~CS!IsCrashed(fm, receiver)
    /\ link.links[sender][receiver] /= {}

Messages(link, fm, sender, receiver) ==
    IF CS!IsCrashed(fm, receiver) THEN {}
    ELSE link.links[sender][receiver]

\* Non-deterministic send: returns SET of possible next states (can deliver or drop).
\* If either endpoint has crashed, the send is a no-op.
Send(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, sender) \/ CS!IsCrashed(fm, receiver) THEN {link}
    ELSE {ReliableSend(link, sender, receiver, msg)} \union
         (IF ShouldDrop(link) THEN {DropMessage(link)} ELSE {})

Receive(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = link.links[sender][receiver] \ {msg}]

=============================================================================
