------------------------- MODULE BestEffortBroadcast -------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT MaxDrops

LOCAL InitChannel(groups, processes) ==
  [g \in groups |-> [ p \in processes |-> {} ]]

LOCAL WrapMessage(sender, receiver, msg) ==
  [sender |-> sender, receiver |-> receiver, message |-> msg]

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

LOCAL AppendMessage(channel, sender, group, receiver, msg) ==
  channel[group][receiver] \union {
    WrapMessage(sender, receiver, msg)
  }

LOCAL IsReceiverToDrop(p, receiversToDrop) == 
  p \in receiversToDrop

LOCAL CountDrops(receiversToDrop) == 
  Cardinality(receiversToDrop)

LOCAL CanDrop(receiversToDrop, totalDrops) ==
  (CountDrops(receiversToDrop) + totalDrops) <= MaxDrops

LOCAL BroadcastToGroup(channel, group, sender, msg, receiversToDrop) ==
  [ p \in DOMAIN channel.links[group] |->
    IF IsReceiverToDrop(p, receiversToDrop) THEN
      channel.links[group][p]
    ELSE
      AppendMessage(channel.links, sender, group, p, msg)
  ]

LOCAL UpdateChannelLinks(channel, group, newGroupLinks) ==
  [ g \in DOMAIN channel.links |->
    IF g = group THEN newGroupLinks ELSE channel.links[g]
  ]

Channel(groups, processes) ==
  [links |-> InitChannel(groups, processes), totalDrops |-> 0]

HasMessage(channel, group, process) ==
  channel.links[group][process] /= {}

Messages(channel, group, process) ==
  { UnwrapMessage(m) : m \in channel.links[group][process] }

LOCAL BroadcastWithDrops(channel, group, sender, msg, receiversToDrop) ==
  LET newGroupLinks == BroadcastToGroup(channel, group, sender, msg, receiversToDrop)
      actualDrops == CountDrops(receiversToDrop)
  IN
  [
    links |-> UpdateChannelLinks(channel, group, newGroupLinks),
    totalDrops |-> channel.totalDrops + actualDrops
  ]

\* Non-deterministic broadcast: returns SET of all possible next channel states
\* User writes: channel' \in Broadcast(channel, "g1", "p1", "msg")
Broadcast(channel, group, sender, msg) ==
  { BroadcastWithDrops(channel, group, sender, msg, receiversToDrop) :
      receiversToDrop \in { r \in SUBSET DOMAIN channel.links[group] :
                            CanDrop(r, channel.totalDrops) } }

Deliver(channel, group, process, msg) ==
  LET wrapped == CHOOSE m \in channel.links[group][process] : UnwrapMessage(m) = msg
  IN [
    links |-> [ channel.links EXCEPT
                  ![group][process] = channel.links[group][process] \ {wrapped}
              ],
    totalDrops |-> channel.totalDrops
  ]
=============================================================================
