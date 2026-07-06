------------------------- MODULE BestEffortBroadcast -------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT MaxCrashes

LOCAL CS == INSTANCE CrashStop

Channel(groups, processes) ==
  [links |-> [g \in groups |-> [ p \in processes |-> {} ]]]

HasMessage(channel, fm, group, process) ==
  ~CS!IsCrashed(fm, process) /\ channel.links[group][process] /= {}

Messages(channel, fm, group, process) ==
  IF CS!IsCrashed(fm, process) THEN {}
  ELSE channel.links[group][process]

LOCAL DeliverTo(channel, group, msg, receivers) ==
  [channel EXCEPT !.links[group] =
    [ p \in DOMAIN channel.links[group] |->
        IF p \in receivers
        THEN channel.links[group][p] \union {msg}
        ELSE channel.links[group][p] ]]

\* A correct sender reaches every alive receiver (BEB1 - Validity). Reaching
\* only a subset is possible solely when the sender crashes mid-broadcast
\* (Cachin: only a faulty sender may reach a subset), so each partial
\* delivery also records the sender's crash in the failure model, guarded by
\* the crash budget. Broadcast therefore returns a set of records
\* [channel |-> c, fm |-> f]; the caller picks one and updates both state
\* variables from it:
\*   \E out \in Broadcast(channel, fm, g, p, m): channel' = out.channel
\*                                            /\ fm' = out.fm
Broadcast(channel, fm, group, sender, msg) ==
  IF CS!IsCrashed(fm, sender) THEN {[channel |-> channel, fm |-> fm]}
  ELSE
    LET aliveReceivers == { p \in DOMAIN channel.links[group] :
                            ~CS!IsCrashed(fm, p) }
        fullDelivery ==
          { [channel |-> DeliverTo(channel, group, msg, aliveReceivers),
             fm      |-> fm] }
        partialDelivery ==
          IF ~CS!CanCrash(fm) THEN {}
          ELSE { [channel |-> DeliverTo(channel, group, msg, subset),
                  fm      |-> CS!Crash(fm, sender)]
                 : subset \in SUBSET (aliveReceivers \ {sender}) }
    IN fullDelivery \union partialDelivery

Deliver(channel, fm, group, process, msg) ==
  IF CS!IsCrashed(fm, process) THEN channel
  ELSE [channel EXCEPT !.links[group][process] = channel.links[group][process] \ {msg}]

=============================================================================
