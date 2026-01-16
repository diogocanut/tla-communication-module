---------------------------- MODULE PerfectLink  ----------------------------
EXTENDS Integers, Sequences


PerfectLink(senders, receivers) == 
    [ s \in senders |-> [ r \in receivers |-> {} ] ]

Messages(link, sender, receiver) == 
    link[sender][receiver]

Send(link, sender, receiver, msg) == 
    [link EXCEPT ![sender][receiver] = link[sender][receiver] \cup {msg}]

Receive(link, sender, receiver, msg) == 
    [link EXCEPT ![sender][receiver] = link[sender][receiver] \ {msg}]

=============================================================================