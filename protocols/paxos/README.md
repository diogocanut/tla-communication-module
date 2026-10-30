# Paxos over the communication module

`PaxosBEB.tla` rebuilds Lamport's single-decree Paxos (`Paxos.tla` from
[tlaplus/Examples](https://github.com/tlaplus/Examples/tree/master/specifications/Paxos),
MIT) on top of `BestEffortBroadcast`, `PerfectLink` and `CrashStop`. Phase 1a and 2a
messages are broadcast by the ballot owner to the acceptors, phase 1b and 2b messages
travel from each acceptor to the ballot owner, and every channel operator consults the
shared failure model. Proposers are explicit processes: ballot `b` belongs to proposer
`b % |Proposer|`.

The module instantiates the upstream `Voting` module and checks, besides its own type
invariant, Lamport's inductive invariant `Inv` with the message pool replaced by the
derived histories `Sent1b` and `Sent2a`, the consensus property `InvOneChosen`
(`Cardinality(V!chosen) <= 1`), `InvLearned` (a value a proposer learned from a quorum of
2b messages is chosen) and the refinement `VotingSpecBar == V!Spec`. Only safety is
checked: Paxos does not guarantee termination with competing proposers.

## Scenarios

All scenarios use 3 acceptors (`a1, a2, a3`), 2 proposers (`0, 1`), 2 values (`v1, v2`)
and majority quorums. Proposer 0 owns the even ballots and proposer 1 the odd ones, so
with `MaxBallot = 2` ballot 2 competes with ballot 1 and must inherit its value.

| Configuration | `MaxBallot` | `MaxCrashes` |
|---|---|---|
| `PaxosBEB_b1_nocrash.cfg` | 1 | 0 |
| `PaxosBEB_b1_crash.cfg` | 1 | 1 |
| `PaxosBEB_b2_nocrash.cfg` | 2 | 0 |
| `PaxosBEB_b2_crash.cfg` | 2 | 1 |

Run from the repository root with the library and the upstream directory on the module
path, with deadlock checking disabled because every finite-ballot run terminates:

```
java -DTLA-Library=".:protocols/paxos:protocols/paxos/upstream" -cp tla2tools.jar tlc2.TLC \
  -deadlock -config protocols/paxos/PaxosBEB_b2_crash.cfg PaxosBEB
```

## Upstream

`upstream/` vendors the unmodified `Consensus.tla`, `Voting.tla`, `Paxos.tla`,
`MCPaxos.tla`, `MCPaxos.cfg` and `README` from tlaplus/Examples at commit
`47b0e2cc0268836b89f5ce451f38e5df5f1cf773`. `Voting` and `Consensus` extend `TLAPS` and
`FiniteSetTheorems`, which are not shipped with `tla2tools.jar`, so `upstream/` also
holds two stubs that declare the theorem names used in their proofs. `MCPaxos3.tla` and
its `MCPaxos3_b<n>.cfg` files instantiate the upstream `Paxos` with the same acceptors,
values and quorums as the scenarios above, and give the baseline for the side-by-side
comparison of model-checking cost.
