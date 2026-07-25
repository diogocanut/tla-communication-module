-------------------------- MODULE ReliableBroadcast --------------------------
EXTENDS Integers, Sequences, FiniteSets

LOCAL CS == INSTANCE CrashStop

Channel(groups, processes) ==
  [links |-> [g \in groups |-> [ p \in processes |-> {} ]]]

HasMessage(channel, fm, group, process) ==
  ~CS!IsCrashed(fm, process) /\ channel.links[group][process] /= {}

Messages(channel, fm, group, process) ==
  IF CS!IsCrashed(fm, process) THEN {}
  ELSE channel.links[group][process]

Broadcast(channel, fm, group, sender, msg) ==
  IF CS!IsCrashed(fm, sender) THEN channel
  ELSE
    LET aliveReceivers == { p \in DOMAIN channel.links[group] :
                            ~CS!IsCrashed(fm, p) }
    IN [channel EXCEPT !.links[group] =
         [ p \in DOMAIN channel.links[group] |->
             IF p \in aliveReceivers
             THEN channel.links[group][p] \union {msg}
             ELSE channel.links[group][p] ]]

Deliver(channel, fm, group, process, msg) ==
  IF CS!IsCrashed(fm, process) THEN channel
  ELSE [channel EXCEPT !.links[group][process] = channel.links[group][process] \ {msg}]

==============================================================================
