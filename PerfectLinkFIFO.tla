-------------------------- MODULE PerfectLinkFIFO --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

LOCAL CS == INSTANCE CrashStop

PerfectLinkFIFO(senders, receivers) ==
    [links |-> [ s \in senders |-> [ r \in receivers |-> <<>> ] ]]

Send(link, fm, sender, receiver, msg) ==
    IF CS!IsCrashed(fm, sender) \/ CS!IsCrashed(fm, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = Append(@, msg)]

HasMessage(link, fm, sender, receiver) ==
    /\ ~CS!IsCrashed(fm, receiver)
    /\ link.links[sender][receiver] /= <<>>

Messages(link, fm, sender, receiver) ==
    IF CS!IsCrashed(fm, receiver) \/ link.links[sender][receiver] = <<>> THEN {}
    ELSE {Head(link.links[sender][receiver])}

Receive(link, fm, sender, receiver) ==
    IF CS!IsCrashed(fm, receiver) THEN link
    ELSE [link EXCEPT !.links[sender][receiver] = Tail(@)]

=============================================================================
