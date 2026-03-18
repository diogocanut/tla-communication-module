------------------------- MODULE BestEffortBroadcast -------------------------
EXTENDS Integers, FiniteSets, Sequences

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

Messages(channel, group, process) ==
  IF IsCrashed(channel, process) THEN {}
  ELSE channel.links[group][process]

LOCAL BroadcastToSubset(channel, group, msg, receivers) ==
  [ p \in DOMAIN channel.links[group] |->
    IF p \in receivers THEN
      AppendMessage(channel.links, group, p, msg)
    ELSE
      channel.links[group][p]
  ]

Broadcast(channel, group, sender, msg) ==
  IF IsCrashed(channel, sender) THEN {channel}
  ELSE
    LET aliveReceivers == { p \in DOMAIN channel.links[group] :
                            ~IsCrashed(channel, p) }
        noCrash ==
          [
            links   |-> UpdateChannelLinks(channel, group,
                           BroadcastToSubset(channel, group, msg, aliveReceivers)),
            crashed |-> channel.crashed
          ]
        crashOutcomes ==
          IF CanCrash(channel) THEN
            { [
                links   |-> UpdateChannelLinks(channel, group,
                               BroadcastToSubset(channel, group, msg, subset)),
                crashed |-> channel.crashed \union {sender}
              ] : subset \in SUBSET aliveReceivers }
          ELSE {}
    IN
    {noCrash} \union crashOutcomes

Deliver(channel, group, process, msg) ==
  [
    links   |-> [ channel.links EXCEPT
                    ![group][process] = channel.links[group][process] \ {msg}
                ],
    crashed |-> channel.crashed
  ]
=============================================================================
