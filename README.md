# TLA+ Communication Module

A reusable and modular TLA+ library for modeling communication primitives over point-to-point and broadcast abstractions. It enables designers to formally describe and verify distributed protocols by composing these primitives as building blocks. Each module exposes a small, uniform API (`Send`/`Broadcast`, `Receive`/`Deliver`, `HasMessage`, `Messages`) together with a crash-stop failure model, allowing protocols to be specified once and verified against communication channels with different reliability guarantees.

## Reliability hierarchy

The library follows the abstractions and terminology of Cachin, Guerraoui, and Rodrigues (*Introduction to Reliable and Secure Distributed Programming*). Point-to-point links are organized in a hierarchy of increasing reliability, and broadcast primitives are built on top of them:

```
PerfectLinkFIFO      AtomicBroadcast
     |                    |
 PerfectLink         ReliableBroadcast
     |                    |
 StubbornLink        BestEffortBroadcast
     |
 FairLossLink
```

Weaker modules expose failures explicitly (message loss, duplication, reordering), while stronger ones eliminate them. Every module models process crashes through a shared crash-stop interface (`IsCrashed`, `CanCrash`, `Crash`), bounded by a `MaxCrashes` constant.

## Project structure

```
/                   core library modules
tests/              test specs and TLC configurations for each module
protocols/          case studies built on top of the core modules
```

## Point-to-point modules

| Module | Loss | Duplication | Reordering | Notes |
|---|---|---|---|---|
| `FairLossLink` | yes (bounded by `MaxDrops`) | no | yes | Models a fair-loss channel where messages may be dropped non-deterministically. Useful for studying retransmission protocols. |
| `StubbornLink` | no | yes (bounded by `MaxCopies`) | yes | Models stubborn delivery: each send produces multiple copies, capturing the effect of repeated retransmissions over a fair-loss link. |
| `PerfectLink` | no | no | yes | Reliable delivery with no duplication, but messages may be delivered in any order. |
| `PerfectLinkFIFO` | no | no | no | Reliable, exactly-once, order-preserving delivery between each sender/receiver pair. |

## Broadcast modules

| Module | Guarantee |
|---|---|
| `BestEffortBroadcast` | Delivery to a non-deterministic subset of correct processes. Captures the behavior of unreliable broadcast where a faulty sender may reach only some recipients. |
| `ReliableBroadcast` | If a correct process delivers a message, every correct process eventually delivers it (uniform agreement on delivery). |
| `AtomicBroadcast` | Reliable delivery plus a total order: every correct process delivers the same sequence of messages. Implemented with per-process FIFO queues. |

## Tests

The `tests/` directory contains one TLA+ specification and one `.cfg` per module, suitable for TLC model checking. Each test instantiates the corresponding module with small constants and checks invariants and temporal properties such as no-creation, no-duplication, validity, agreement, and (for `AtomicBroadcast`) total order. The composition test `StubbornDeliveryOverFairLossTest` verifies that a stubborn link built on top of a fair-loss link satisfies the expected stubborn delivery property.

## Case studies

The `protocols/` directory contains protocol specifications written against the library:

- `protocols/echo/` contains the Echo protocol verified over three different links (`EchoPerfect`, `EchoStubborn`, `EchoFairLoss`), illustrating how the same protocol behaves under different reliability assumptions.
- `protocols/DeferredUpdate.tla` specifies the Deferred Update Replication (DUR) protocol, combining `PerfectLinkFIFO` for client-server communication with `AtomicBroadcast` for replica coordination.

## Publications

- *WTF 2025*: point-to-point primitives and the Echo protocol case study.
- *LADC 2025*: broadcast primitives and verification of the Deferred Update Replication protocol.
