-------------------------- MODULE PerfectLinkFIFO --------------------------
EXTENDS Integers, Sequences, TLC


PerfectLinkFIFO(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> <<>> ] ]

Send(link, sender, receiver, msg) ==
    [link EXCEPT ![sender][receiver] = Append(@, msg)]

Messages(link, sender, receiver) ==
    IF link[sender][receiver] = <<>> THEN {}
    ELSE {Head(link[sender][receiver])}

Receive(link, sender, receiver) ==
    [link EXCEPT ![sender][receiver] = Tail(@)]


=============================================================================