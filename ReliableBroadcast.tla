-------------------------- MODULE ReliableBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets


LOCAL WrapMessage(sender, receiver, msg) == 
  [sender |-> sender, receiver |-> receiver, message |-> msg]

LOCAL InitChannel(groups, processes) == 
  [g \in groups |-> [ p \in processes |-> {} ]]

LOCAL AppendMessage(channel, sender, group, receiver, msg) ==
  channel[group][receiver] \union {
    WrapMessage(sender, receiver, msg)
  }

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

Channel(groups, processes) == 
  [links |-> InitChannel(groups, processes)]

Messages(channel, group, process) ==
  { UnwrapMessage(m) : m \in channel.links[group][process] }

Broadcast(channel, group, sender, msg) ==
  [
    links |-> [ g \in DOMAIN channel.links |->
                IF g = group THEN
                  [ p \in DOMAIN channel.links[g] |->
                    AppendMessage(channel.links, sender, g, p, msg)
                  ]
                ELSE channel.links[g]
              ]
  ]

Deliver(channel, group, process, msg) ==
  LET wrapped == CHOOSE m \in channel.links[group][process] : UnwrapMessage(m) = msg
  IN [
    links |-> [ channel.links EXCEPT
                ![group][process] = channel.links[group][process] \ {wrapped}
              ]
  ]
==============================================================================
