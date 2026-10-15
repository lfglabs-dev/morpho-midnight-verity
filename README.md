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

[ticklib/](ticklib/README.md) proves Midnight's `TickLib.wExp` and
`TickLib.tickToPrice` monotone. They are imported unmodified through Morpho's
Certora harness `certora/helpers/TickLibWrapper.sol`.
[Spec.lean](ticklib/TickLib/Spec.lean) states the rules and
[Proof.lean](ticklib/TickLib/Proof.lean) proves them:

- `tickToPriceIsMonotonic`: for all `uint256` ticks `t1 < t2`, if both calls
  succeed then `tickToPrice(t1) <= tickToPrice(t2)`.
- `wExpIsMonotonic`: for `-X* <= x <= y <= X*`, `X* = 135999161806159974428`, both
  calls succeed and `wExp(x) <= wExp(y)`.
- `wExpNotMonotonicBeyond`: `wExp(X*) > wExp(X* + 1) = 0`, so the range is exact.
- Ports of the other `TickToPrice.spec` rules: `maxOutputIsWExpOfMaxInput`,
  `tickToPriceIsZeroAtZero`, `tickToPriceIsOneAtMaxTick`,
  `tickToPriceUsesPriceRoundingStep`, `tickToPriceAtMostWad`, plus
  `tickToPriceTotal`: every `tick <= 6744` succeeds.

Certora's approach is different. `TickToPrice.spec` checks `wExp` with five
step rules on `[-maxInput, maxInput]`. `TickToPriceIsMonotonic.spec` then
replaces `wExp` by a ghost with the axiom
`forall x y. x <= y => wExp(x) <= wExp(y)` over all `int256`. That axiom is
false for the real code: past `X*` the shift `expR << q` overflows and `wExp`
drops from about `2^256` to `0`. Here a single chain of checked proofs goes from
the model imported from the Solidity to the monotonicity statement. It has no
axiom and no summary, and it states the exact maximal range of `wExp`. The
axiom audit shows only `propext`, `Classical.choice` and `Quot.sound`.

`ticklib/` is a separate Lake package pinned to Verity `10f697bb`, which can
import `int256` and `wExp`'s recursive call. The root package stays on
`9b472a8`, so the `updatePositionView` proof is unchanged. `./check/check.sh`
runs both. To re-run only TickLib:

```sh
git submodule update --init --recursive
sh ticklib/check/check.sh
```

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
