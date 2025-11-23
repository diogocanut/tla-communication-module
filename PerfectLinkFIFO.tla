-------------------------- MODULE PerfectLinkFIFO --------------------------
EXTENDS Integers, Sequences, TLC


LOCAL WrapMessage(sender, receiver, msg) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg ]

LOCAL UnwrapMessage(wrappedMessage) ==
    wrappedMessage.message

PerfectLinkFIFO(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> <<>> ] ]

Send(link, sender, receiver, msg) ==
    [link EXCEPT ![sender][receiver] = Append(@, WrapMessage(sender, receiver, msg))]

HasMessage(link, sender, receiver) ==
    link[sender][receiver] /= <<>>

Message(link, sender, receiver) ==
    UnwrapMessage(Head(link[sender][receiver]))

Receive(link, sender, receiver) ==
    [link EXCEPT ![sender][receiver] = Tail(@)]


=============================================================================