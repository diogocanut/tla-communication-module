---------------------------- MODULE PerfectLink  ----------------------------
EXTENDS Integers, Sequences


LOCAL AppendMessage(set, msg) == set \cup {msg}

PerfectLink(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> {} ] ]

Messages(link, sender, receiver) == 
    link[sender][receiver]

Send(link, sender, receiver, msg) == 
    [link EXCEPT ![sender][receiver] = AppendMessage(@, msg)]

Receive(link, sender, receiver, msg) == 
    [link EXCEPT ![sender][receiver] = link[sender][receiver] \ {msg}]

=============================================================================