-------------------------- MODULE ReliableBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets


LOCAL WrapMessage(sender, receiver, msg, id) == 
  [sender |-> sender, receiver |-> receiver, message |-> msg, messageId |-> id]

LOCAL InitChannel(groups, processes) == 
  [g \in groups |-> [ p \in processes |-> {} ]]

LOCAL AppendMessage(channel, sender, group, receiver, msg, id) ==
  channel[group][receiver] \union {
    WrapMessage(sender, receiver, msg, id)
  }

Channel(groups, processes) == 
  [links |-> InitChannel(groups, processes), nextMessageId |-> 0]

HasMessage(channel, group, process) ==
  channel.links[group][process] /= {}

Messages(channel, group, process) ==
  channel.links[group][process]

UnwrapMessage(wrappedMessage) == wrappedMessage.message

Broadcast(channel, group, sender, msg) ==
  [
    links |-> [ g \in DOMAIN channel.links |->
                IF g = group THEN
                  [ p \in DOMAIN channel.links[g] |->
                    AppendMessage(channel.links, sender, g, p, msg, channel.nextMessageId)
                  ]
                ELSE channel.links[g]
              ],
    nextMessageId |-> channel.nextMessageId + 1
  ]

Deliver(channel, group, process, wrappedMessage) ==
  [
    links |-> [ channel.links EXCEPT
                ![group][process] = { m \in channel.links[group][process] : m # wrappedMessage }
              ],
    nextMessageId |-> channel.nextMessageId
  ]
==============================================================================
