-------------------------- MODULE ReliableBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets


LOCAL InitChannel(groups, processes) == 
  [g \in groups |-> [ p \in processes |-> {} ]]

LOCAL AppendMessage(channel, group, receiver, msg) ==
  channel[group][receiver] \union {msg}

Channel(groups, processes) == 
  [links |-> InitChannel(groups, processes)]

Messages(channel, group, process) ==
  channel.links[group][process]

Broadcast(channel, group, sender, msg) ==
  [
    links |-> [ g \in DOMAIN channel.links |->
                IF g = group THEN
                  [ p \in DOMAIN channel.links[g] |->
                    AppendMessage(channel.links, g, p, msg)
                  ]
                ELSE channel.links[g]
              ]
  ]

Deliver(channel, group, process, msg) ==
  [
    links |-> [ channel.links EXCEPT
                ![group][process] = channel.links[group][process] \ {msg}
              ]
  ]
==============================================================================
