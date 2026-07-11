---------------------------- MODULE PerfectLink  ----------------------------
EXTENDS Integers, Sequences, FiniteSets

LOCAL CS == INSTANCE CrashStop

LOCAL AppendMessage(set, msg) == set \cup {msg}

PerfectLink(senders, receivers) ==
    [links |-> [ s \in senders |-> [ r \in receivers |-> {} ] ]]

HasMessage(link, fm, sender, receiver) ==
    /\ ~CS!IsCrashed(fm, receiver)
    /\ link.links[sender][receiver] /= {}

Messages(link, fm, sender, receiver) ==
    IF CS!IsCrashed(fm, receiver) THEN {}
    ELSE link.links[sender][receiver]

Send(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, sender) \/ CS!IsCrashed(fm, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = AppendMessage(@, msg)]

Receive(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = link.links[sender][receiver] \ {msg}]

=============================================================================
