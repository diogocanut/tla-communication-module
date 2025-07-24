-------------------------- MODULE PerfectLinkFIFO --------------------------
EXTENDS Integers, Sequences, TLC


LOCAL WrapMessage(sender, receiver, msg) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg ]

PerfectLinkFIFO(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> <<>> ] ]

Send(link, sender, receiver, msg) ==
    [link EXCEPT ![sender][receiver] = Append(@, WrapMessage(sender, receiver, msg))]

HasMessage(link, sender, receiver) ==
    link[sender][receiver] /= <<>>

Message(link, sender, receiver) ==
    Head(link[sender][receiver])

UnwrapMessage(wrappedMessage) ==
    wrappedMessage.message

Receive(link, sender, receiver) ==
    [link EXCEPT ![sender][receiver] = Tail(@)]


=============================================================================