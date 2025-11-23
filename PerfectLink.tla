---------------------------- MODULE PerfectLink  ----------------------------
EXTENDS Integers, Sequences


LOCAL InitLink(linksPerProcess) == [links |-> linksPerProcess, nextMessageId |-> 0]

LOCAL WrapMessage(sender, receiver, msg, id) == 
    [ sender |-> sender, receiver |-> receiver, message |-> msg, messageId |-> id ]

LOCAL AppendMessage(link, sender, receiver, msg) == 
    link.links[receiver] \cup { WrapMessage(sender, receiver, msg, link.nextMessageId) }

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

PerfectLink(processes) == InitLink([ p \in processes |-> {} ])

HasMessage(link, process) == link.links[process] /= {}

Messages(link, process) == { UnwrapMessage(m) : m \in link.links[process] }

Send(link, sender, receiver, msg) == [
    links |-> [link.links EXCEPT ![receiver] = AppendMessage(link, sender, receiver, msg)],
    nextMessageId |-> link.nextMessageId + 1 
]

Receive(link, process, msg) == 
    LET wrapped == CHOOSE m \in link.links[process] : UnwrapMessage(m) = msg
    IN [links |-> [link.links EXCEPT ![process] = link.links[process] \ {wrapped}],
        nextMessageId |-> link.nextMessageId]

=============================================================================