---------------------------- MODULE PerfectLink  ----------------------------
EXTENDS Integers, Sequences


LOCAL WrapMessage(sender, receiver, msg) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg ]

LOCAL AppendMessage(link, sender, receiver, msg) == 
    link[receiver] \cup { WrapMessage(sender, receiver, msg) }

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

PerfectLink(processes) == [ p \in processes |-> {} ]

HasMessage(link, process) == link[process] /= {}

Messages(link, process) == { UnwrapMessage(m) : m \in link[process] }

Send(link, sender, receiver, msg) == 
    [link EXCEPT ![receiver] = AppendMessage(link, sender, receiver, msg)]

Receive(link, process, msg) == 
    LET wrapped == CHOOSE m \in link[process] : UnwrapMessage(m) = msg
    IN [link EXCEPT ![process] = link[process] \ {wrapped}]

=============================================================================