-------------------------- MODULE AtomicBroadcast --------------------------
EXTENDS Integers, Sequences, TLC


LOCAL WrapMessage(sender, receiver, msg) == 
  [sender |-> sender, receiver |-> receiver, message |-> msg]

LOCAL AppendMessage(groupChannel, sender, receiver, msg) == 
  Append(groupChannel[receiver], WrapMessage(sender, receiver, msg))

LOCAL UnwrapMessage(wrappedMessage) == wrappedMessage.message

Channel(groups, processes) == 
  [g \in groups |-> [p \in processes |-> <<>>]]

HasMessage(channel, group, process) ==
  channel[group][process] /= <<>>

Message(channel, group, process) ==
  UnwrapMessage(Head(channel[group][process]))

Deliver(channel, group, process) ==
  [ g \in DOMAIN channel |->
      IF g = group THEN
        [ p \in DOMAIN channel[g] |->
            IF p = process THEN Tail(channel[g][p])
            ELSE channel[g][p]
        ]
      ELSE
        channel[g]
  ]

Broadcast(channel, group, sender, msg) ==
  [ g \in DOMAIN channel |->
      IF g = group THEN
        [ p \in DOMAIN channel[g] |->
             AppendMessage(channel[g], sender, p, msg)
        ]
      ELSE
        channel[g]
  ]

=============================================================================