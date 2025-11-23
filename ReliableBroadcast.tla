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

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

Channel(groups, processes) == 
  [links |-> InitChannel(groups, processes), nextMessageId |-> 0]

HasMessage(channel, group, process) ==
  channel.links[group][process] /= {}

Messages(channel, group, process) ==
  { UnwrapMessage(m) : m \in channel.links[group][process] }

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

Deliver(channel, group, process, msg) ==
  LET wrapped == CHOOSE m \in channel.links[group][process] : UnwrapMessage(m) = msg
  IN [
    links |-> [ channel.links EXCEPT
                ![group][process] = channel.links[group][process] \ {wrapped}
              ],
    nextMessageId |-> channel.nextMessageId
  ]
==============================================================================
