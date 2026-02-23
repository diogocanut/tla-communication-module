# TLA+ Communication Module

A reusable and modular TLA+ library for modeling communication primitives over point-to-point and broadcast abstractions. It enables designers to formally describe and verify solutions by providing these primitives as building blocks for communication subsystems. The library includes fault injection for analyzing system behavior under unreliable conditions, such as message loss, duplication, and out-of-order delivery.

## Project Structure

```
/                   ← core library modules (FairLossLink, StubbornLink, PerfectLink, etc.)
tests/              ← test specs and TLC configs for each module
protocols/          ← case studies built on top of the core modules
```

## Running

### VS Code

1. Install the [TLA+ extension](https://marketplace.visualstudio.com/items?itemName=tlaplus.vscode-ide) (`tlaplus.vscode-ide`).
2. Add a `.vscode/settings.json` file at the project root with the following content:

```json
{
  "tlaplus.moduleSearchPaths": [
    "/absolute/path/to/this/project"
  ]
}
```

Replace `/absolute/path/to/this/project` with the actual absolute path where you cloned the repository.

3. Open any spec under `tests/` or `protocols/` and run **TLA+: Check model** (Command Palette).

### Command Line

Requires a `tla2tools.jar`. You can download it from the [TLA+ releases page](https://github.com/tlaplus/tlaplus/releases) or use the one bundled with the VS Code extension.

Run from the repository root so relative paths to `tests/` and `protocols/` work as shown.

```bash
java -DTLA-Library=/path/to/project \
  -cp /path/to/tla2tools.jar \
  tlc2.TLC \
  -config tests/StubbornLinkTest.cfg \
  tests/StubbornLinkTest.tla
```

- Replace `/path/to/project` with the root directory of this repository.
- Replace `/path/to/tla2tools.jar` with the path to your `tla2tools.jar`.
- The `TLA-Library` JVM property tells SANY/TLC where to look for modules outside the spec's own directory.
- Substitute `StubbornLinkTest` with any other test or protocol spec as needed (and update the `-config` path accordingly).