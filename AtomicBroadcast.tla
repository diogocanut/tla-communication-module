-------------------------- MODULE AtomicBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

LOCAL IsCrashed(fm, process) == process \in fm.crashed

Channel(groups, processes) ==
  [links |-> [g \in groups |-> [p \in processes |-> <<>>]]]

HasMessage(channel, fm, group, process) ==
  ~IsCrashed(fm, process) /\ channel.links[group][process] /= <<>>

Messages(channel, fm, group, process) ==
  IF IsCrashed(fm, process) THEN {}
  ELSE IF channel.links[group][process] = <<>> THEN {}
  ELSE {Head(channel.links[group][process])}

Deliver(channel, fm, group, process) ==
  IF IsCrashed(fm, process) THEN channel
  ELSE [channel EXCEPT !.links[group][process] = Tail(@)]

Broadcast(channel, fm, group, sender, msg) ==
  IF IsCrashed(fm, sender) THEN channel
  ELSE
    LET aliveReceivers == { p \in DOMAIN channel.links[group] :
                            ~IsCrashed(fm, p) }
    IN [channel EXCEPT !.links[group] =
         [ p \in DOMAIN channel.links[group] |->
             IF p \in aliveReceivers
             THEN Append(channel.links[group][p], msg)
             ELSE channel.links[group][p] ]]

=============================================================================
