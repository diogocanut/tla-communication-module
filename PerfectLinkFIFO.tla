-------------------------- MODULE PerfectLinkFIFO --------------------------
EXTENDS Integers, Sequences, TLC


PerfectLinkFIFO(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> <<>> ] ]

Send(link, sender, receiver, msg) ==
    [link EXCEPT ![sender][receiver] = Append(@, msg)]

HasMessage(link, sender, receiver) ==
    link[sender][receiver] /= <<>>

Message(link, sender, receiver) ==
    Head(link[sender][receiver])

Receive(link, sender, receiver) ==
    [link EXCEPT ![sender][receiver] = Tail(@)]


=============================================================================