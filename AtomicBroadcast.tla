-------------------------- MODULE AtomicBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MaxCrashes

Channel(groups, processes) == 
  [links |-> [g \in groups |-> [p \in processes |-> <<>>]], crashed |-> {}]

IsCrashed(channel, process) ==
  process \in channel.crashed

CanCrash(channel) ==
  Cardinality(channel.crashed) < MaxCrashes

Crash(channel, process) ==
  [channel EXCEPT !.crashed = channel.crashed \union {process}]

HasMessage(channel, group, process) ==
  ~IsCrashed(channel, process) /\ channel.links[group][process] /= <<>>

Messages(channel, group, process) ==
  IF IsCrashed(channel, process) THEN {}
  ELSE IF channel.links[group][process] = <<>> THEN {}
  ELSE {Head(channel.links[group][process])}

Deliver(channel, group, process) ==
  [
    links   |-> [ g \in DOMAIN channel.links |->
                    IF g = group THEN
                      [ p \in DOMAIN channel.links[g] |->
                          IF p = process THEN Tail(channel.links[g][p])
                          ELSE channel.links[g][p]
                      ]
                    ELSE channel.links[g]
                ],
    crashed |-> channel.crashed
  ]

Broadcast(channel, group, sender, msg) ==
  IF IsCrashed(channel, sender) THEN {channel}
  ELSE
    LET aliveReceivers == { p \in DOMAIN channel.links[group] :
                            ~IsCrashed(channel, p) }
        noCrash ==
          [
            links   |-> [ g \in DOMAIN channel.links |->
                            IF g = group THEN
                              [ p \in DOMAIN channel.links[g] |->
                                  IF p \in aliveReceivers THEN
                                    Append(channel.links[g][p], msg)
                                  ELSE channel.links[g][p]
                              ]
                            ELSE channel.links[g]
                          ],
            crashed |-> channel.crashed
          ]
        crashOutcome ==
          IF CanCrash(channel) THEN
            {[
              links   |-> channel.links,
              crashed |-> channel.crashed \union {sender}
            ]}
          ELSE {}
    IN
    {noCrash} \union crashOutcome

=============================================================================