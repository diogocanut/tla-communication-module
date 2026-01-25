-------------------------- MODULE AtomicBroadcast --------------------------
EXTENDS Integers, Sequences, TLC


Channel(groups, processes) == 
  [g \in groups |-> [p \in processes |-> <<>>]]

HasMessage(channel, group, process) ==
  channel[group][process] /= <<>>

Messages(channel, group, process) ==
  IF channel[group][process] = <<>> THEN {}
  ELSE {Head(channel[group][process])}

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
             Append(channel[g][p], msg)
        ]
      ELSE
        channel[g]
  ]

=============================================================================