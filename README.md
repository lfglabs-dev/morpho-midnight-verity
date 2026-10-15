# Morpho Midnight × Verity

Proves the Certora rule
[`updatePositionViewProperties`](https://github.com/morpho-org/midnight/blob/96d31343e993329e7a593dde46516a2c0cbcd142/certora/specs/UpdatePositionView.spec)
on `Midnight.updatePositionView`, imported directly from the Solidity of
[midnight@96d31343](https://github.com/morpho-org/midnight/tree/96d31343e993329e7a593dde46516a2c0cbcd142).

- [Import.lean](Midnight/Import.lean): the Solidity import
- [Spec.lean](Midnight/Spec.lean): the rule `updatePositionViewProperties` as a definition, in the CVL vocabulary, without the CVL ghosts (not needed for a single call)
- [Proof.lean](Midnight/Proof.lean): the theorem that the rule holds (supporting lemmas in [Lemmas/](Midnight/Lemmas))
- [check/](check/README.md): what is trusted and how the import is checked

```sh
git submodule update --init --recursive
./check/check.sh
```

## TickLib monotonicity

[ticklib/](ticklib/README.md) proves `TickLib.wExp` and `TickLib.tickToPrice` monotone,
on the unmodified `TickLib.sol` imported through Morpho's Certora harness
`certora/helpers/TickLibWrapper.sol`. [Spec.lean](ticklib/TickLib/Spec.lean) states
the rules of `TickToPrice.spec` and `TickToPriceIsMonotonic.spec`, and
[Proof.lean](ticklib/TickLib/Proof.lean) proves them:

- `tickToPriceIsMonotonic`: for all `uint256` ticks `t1 < t2`, if both calls succeed,
  `tickToPrice(t1) <= tickToPrice(t2)`.
- `wExpIsMonotonic`: for `-X* <= x <= y <= X*`, `X* = 135999161806159974428`, both calls
  succeed and `wExp(x) <= wExp(y)`. `wExpNotMonotonicBeyond` shows `X*` is the exact limit.
- the other `TickToPrice.spec` rules, plus `tickToPriceTotal` (every `tick <= 6744` succeeds).

`TickToPriceIsMonotonic.spec` summarizes `wExp` with a ghost axiom that it is monotone on
all `int256`. That holds on every input `tickToPrice` can produce, but not beyond `X*`, where
the shift overflows and `wExp` drops to `0`. Here `tickToPriceIsMonotonic` is proved about
the imported `wExp` itself, with no axiom or summary.

`./check/check.sh` runs the TickLib checks after the root ones. To run only TickLib:
`sh ticklib/check/check.sh`.

## Cursor Cloud environment

`.cursor/environment.json` uses `.cursor/Dockerfile` to install Lean 4.31.0.
The install hook prepares checksum-pinned solc 0.8.34, the committed Lake
dependencies, the imported model/specification, and lean-lsp-mcp 0.31.0.
Install and startup readiness checks reject Cursor's fallback/default image.

Feature-branch draft Builds can be tested but cannot be promoted directly.
A supported saved-snapshot route has now passed a no-ref Build and fresh
startup validation; activation requires Save in the Cursor Environment panel.
This infrastructure PR is optional for durable default-branch configuration.
Proof experiments use `cursor/proof-sandbox`, which removes the old proofs;
this infrastructure branch preserves them.
See `check/CURSOR_CLOUD_TEST.md` for native Build evidence and activation status.

`sh scripts/doctor.sh` checks local readiness. `sh scripts/lean-mcp.sh` runs
stdio Lean diagnostics. `.cursor/mcp.json` configures Cursor IDE; custom Cloud
MCPs additionally require account/team enablement. The server provides compiler
diagnostics and proof goals; shell verification remains available without MCP.
Run `.lake/lean-mcp/bin/python scripts/check-lean-mcp.py` for the diagnostic/goal
smoke test. Run the existing `./check/check.sh` for full verification.
