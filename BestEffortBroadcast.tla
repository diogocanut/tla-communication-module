------------------------- MODULE BestEffortBroadcast -------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT MaxDrops

LOCAL WrapMessage(sender, receiver, msg, id) ==
  [sender |-> sender, receiver |-> receiver, message |-> msg, messageId |-> id]

LOCAL InitChannel(groups, processes) ==
  [g \in groups |-> [ p \in processes |-> {} ]]

  Channel(groups, processes) ==
  [links |-> InitChannel(groups, processes), nextMessageId |-> 0, totalDrops |-> 0 ]

LOCAL AppendMessage(channel, sender, group, receiver, msg, id) ==
  channel[group][receiver] \union {
    WrapMessage(sender, receiver, msg, id)
  }

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

HasMessage(channel, group, process) ==
  channel.links[group][process] /= {}

Messages(channel, group, process) ==
  { UnwrapMessage(m) : m \in channel.links[group][process] }

LOCAL ShouldDrop(receiversToDrop, totalDrops) ==
  (Cardinality(receiversToDrop) + totalDrops) <= MaxDrops

Broadcast(channel, group, sender, msg, receiversToDrop) ==
  LET 
    isReceiverToDrop(p) == p \in receiversToDrop
    actualDrops == IF ShouldDrop(receiversToDrop, channel.totalDrops)
            THEN Cardinality(receiversToDrop)
            ELSE 0
  IN
  [
    links |-> [
      g \in DOMAIN channel.links |->
        IF g = group THEN
          [ p \in DOMAIN channel.links[g] |->
            IF ShouldDrop(receiversToDrop, channel.totalDrops) /\ isReceiverToDrop(p) THEN
              channel.links[g][p]
            ELSE
              AppendMessage(channel.links, sender, g, p, msg, channel.nextMessageId)
          ]
        ELSE channel.links[g]
    ],
    nextMessageId |-> channel.nextMessageId + 1,
    totalDrops |-> channel.totalDrops + actualDrops
  ]

Deliver(channel, group, process, msg) ==
  LET wrapped == CHOOSE m \in channel.links[group][process] : UnwrapMessage(m) = msg
  IN [
    links |-> [ channel.links EXCEPT
                  ![group][process] = channel.links[group][process] \ {wrapped}
              ],
    nextMessageId |-> channel.nextMessageId,
    totalDrops |-> channel.totalDrops
  ]
=============================================================================
