-------------------------- MODULE ReliableBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT MaxCrashes

LOCAL InitChannel(groups, processes) == 
  [g \in groups |-> [ p \in processes |-> {} ]]

LOCAL AppendMessage(channel, group, receiver, msg) ==
  channel[group][receiver] \union {msg}

LOCAL UpdateChannelLinks(channel, group, newGroupLinks) ==
  [ g \in DOMAIN channel.links |->
    IF g = group THEN newGroupLinks ELSE channel.links[g]
  ]

Channel(groups, processes) == 
  [links |-> InitChannel(groups, processes), crashed |-> {}]

IsCrashed(channel, process) ==
  process \in channel.crashed

CanCrash(channel) ==
  Cardinality(channel.crashed) < MaxCrashes

Crash(channel, process) ==
  [channel EXCEPT !.crashed = channel.crashed \union {process}]

HasMessage(channel, group, process) ==
  ~IsCrashed(channel, process) /\ channel.links[group][process] /= {}

Messages(channel, group, process) ==
  IF IsCrashed(channel, process) THEN {}
  ELSE channel.links[group][process]

LOCAL BroadcastToAll(channel, group, msg, receivers) ==
  [ p \in DOMAIN channel.links[group] |->
    IF p \in receivers THEN
      AppendMessage(channel.links, group, p, msg)
    ELSE
      channel.links[group][p]
  ]

Broadcast(channel, group, sender, msg) ==
  IF IsCrashed(channel, sender) THEN channel
  ELSE
    LET aliveReceivers == { p \in DOMAIN channel.links[group] :
                            ~IsCrashed(channel, p) }
    IN
    [
      links   |-> UpdateChannelLinks(channel, group,
                     BroadcastToAll(channel, group, msg, aliveReceivers)),
      crashed |-> channel.crashed
    ]

Deliver(channel, group, process, msg) ==
  [
    links   |-> [ channel.links EXCEPT
                    ![group][process] = channel.links[group][process] \ {msg}
                ],
    crashed |-> channel.crashed
  ]
==============================================================================
