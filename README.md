# TLA+ Communication Module

A reusable and modular TLA+ library for modeling communication primitives over point-to-point and broadcast abstractions. It enables designers to formally describe and verify distributed protocols by composing these primitives as building blocks. Each module exposes a small, uniform API (`Send`/`Broadcast`, `Receive`/`Deliver`, `HasMessage`, `Messages`), and process failures are modeled by a dedicated `CrashStop` module whose failure-model value is passed to every channel operator, allowing protocols to be specified once and verified against communication channels with different reliability guarantees.

## Reliability hierarchy

The library follows the abstractions and terminology of Cachin, Guerraoui, and Rodrigues (*Introduction to Reliable and Secure Distributed Programming*). Point-to-point links and broadcast channels are each organized as an independent hierarchy of increasing reliability:

```
PerfectLinkFIFO      AtomicBroadcast
     |                    |
 PerfectLink         ReliableBroadcast
     |                    |
 StubbornLink        BestEffortBroadcast
     |
 FairLossLink
```

Within each hierarchy, weaker modules expose failures explicitly (message loss, duplication, reordering), while stronger ones eliminate them. The broadcast modules specify their guarantees directly over an abstract channel rather than implementing them on top of point-to-point links.

## Crash-stop failure model

Process failures follow the crash-stop process abstraction of Cachin, Guerraoui & Rodrigues and live in a dedicated `CrashStop` module, separate from the channels: crashing is a property of a process, not of any one channel. A specification declares a single failure-model value, constructed with its crash budget (`fm = CrashStop(maxCrashes)`), and passes it to every channel operator; the module exposes `IsCrashed`, `CanCrash`, and `Crash`, with the budget carried inside the value itself (`fm.max`) — no module declares a failure constant. Because the value is shared, all channels in a specification observe the same set of crashed processes, and a crash is recorded exactly once no matter how many primitives the protocol composes. `BestEffortBroadcast` is the one channel that can itself cause a crash (a sender halting mid-broadcast may reach only a subset of receivers), so its `Broadcast` returns `[channel |-> c, fm |-> f]` records carrying both updated values.

## Message payloads

The set-based modules (`FairLossLink`, `StubbornLink`, `PerfectLink`, `BestEffortBroadcast`, `ReliableBroadcast`) store in-flight messages in sets, so sending the same payload twice to the same destination collapses into a single delivery. Give messages distinguishing fields (an id, a sequence number, the sender) if repeated sends must be delivered repeatedly. The sequence-based modules (`PerfectLinkFIFO`, `AtomicBroadcast`) do not have this constraint.

## Project structure

```
/                   core library modules
tests/              test specs and TLC configurations for each module
protocols/          case studies built on top of the core modules
```

## Point-to-point modules

| Module | Loss | Duplication | Reordering | Guarantees |
|---|---|---|---|---|
| `FairLossLink` | yes (bounded by `MaxDrops`) | no | yes | Models a fair-loss channel where messages may be dropped non-deterministically. Useful for studying retransmission protocols. |
| `StubbornLink` | no | yes (bounded by `MaxCopies`) | yes | Models stubborn delivery: each send produces multiple copies, capturing the effect of repeated retransmissions over a fair-loss link. |
| `PerfectLink` | no | no | yes | Reliable delivery with no duplication, but messages may be delivered in any order. |
| `PerfectLinkFIFO` | no | no | no | Reliable, exactly-once, order-preserving delivery between each sender/receiver pair. |

## Broadcast modules

| Module | Loss | Duplication | Reordering | Guarantees |
|---|---|---|---|---|
| `BestEffortBroadcast` | yes (non-deterministic subset of correct processes) | no | yes | Captures unreliable broadcast where a faulty sender may reach only some recipients. No agreement across processes. |
| `ReliableBroadcast` | no | no | yes | If any correct process delivers a message, every correct process eventually delivers it (uniform agreement on delivery). |
| `AtomicBroadcast` | no | no | no | Reliable delivery plus a total order: every correct process delivers the same sequence of messages. Implemented with per-process FIFO queues. |

## Tests

The `tests/` directory contains one TLA+ specification and one `.cfg` per module, suitable for TLC model checking. Each test instantiates the corresponding module with small constants and checks invariants and temporal properties such as no-creation, no-duplication, validity, agreement, and (for `AtomicBroadcast`) total order. The composition test `StubbornDeliveryOverFairLossTest` verifies that a stubborn link built on top of a fair-loss link satisfies the expected stubborn delivery property.

## Case studies

The `protocols/` directory contains protocol specifications written against the library:

- `protocols/echo/` contains the Echo protocol verified over three different links (`EchoPerfect`, `EchoStubborn`, `EchoFairLoss`), illustrating how the same protocol behaves under different reliability assumptions.
- `protocols/DeferredUpdate.tla` specifies the Deferred Update Replication (DUR) protocol, combining `PerfectLinkFIFO` for client-server communication with `AtomicBroadcast` for replica coordination.
- `protocols/hermes/` rebuilds the Hermes replication protocol (Katsarakis et al., ASPLOS 2020) on top of `ReliableBroadcast` and `PerfectLink`, with five TLC scenario configurations (read-only, single-writer, concurrent, with and without crashes) checking its safety invariants, a crash-stop invariant, and a write-termination liveness property. `protocols/hermes/upstream/` vendors the unmodified upstream `Hermes.tla` (Apache-2.0) together with a scenario harness (`HermesScenarios.tla`) that reassembles the original actions under the same scenario dials, used for the side-by-side comparison of model-checking cost.

## Publications

- Diogo Peixoto and Odorico Machado Mendizabal. *Reusable TLA+ Communication Primitives for Modeling and Verifying Distributed Systems*. In Proceedings of the 26th Workshop on Testing and Fault Tolerance (WTF), SBC, 2025, pp. 113-125. DOI: [10.5753/wtf.2025.8866](https://doi.org/10.5753/wtf.2025.8866). [[PDF]](https://sol.sbc.org.br/index.php/wtf/article/view/35652)
- Diogo Peixoto and Odorico Mendizabal. *A Practical TLA+ Library for Designing and Verifying Distributed Systems*. In Anais do XIV Latin-American Symposium on Dependable Computing (LADC), SBC, 2025, pp. 183-200. [[PDF]](https://sol.sbc.org.br/index.php/ladc/article/view/41078)
