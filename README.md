# TLA+ Communication Module

A reusable and modular TLA+ library for modeling communication primitives over point-to-point and broadcast abstractions. It enables designers to formally describe and verify distributed protocols by composing these primitives as building blocks. Each module exposes a small, uniform API (`Send`/`Broadcast`, `Receive`/`Deliver`, `HasMessage`, `Messages`) together with a crash-stop failure model, allowing protocols to be specified once and verified against communication channels with different reliability guarantees.

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

Within each hierarchy, weaker modules expose failures explicitly (message loss, duplication, reordering), while stronger ones eliminate them. The broadcast modules specify their guarantees directly over an abstract channel rather than implementing them on top of point-to-point links. Every module shares a crash-stop interface (`IsCrashed`, `CanCrash`, `Crash`), bounded by a `MaxCrashes` constant.

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

## Publications

- Diogo Peixoto and Odorico Machado Mendizabal. *Reusable TLA+ Communication Primitives for Modeling and Verifying Distributed Systems*. In Proceedings of the 26th Workshop on Testing and Fault Tolerance (WTF), SBC, 2025, pp. 113-125. DOI: [10.5753/wtf.2025.8866](https://doi.org/10.5753/wtf.2025.8866). [[PDF]](https://sol.sbc.org.br/index.php/wtf/article/view/35652)
- Diogo Peixoto and Odorico Mendizabal. *A Practical TLA+ Library for Designing and Verifying Distributed Systems*. In Anais do XIV Latin-American Symposium on Dependable Computing (LADC), SBC, 2025, pp. 183-200. [[PDF]](https://sol.sbc.org.br/index.php/ladc/article/view/41078)
