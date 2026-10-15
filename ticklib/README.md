# TickLib monotonicity

Proves the Certora rules of `TickToPrice.spec` and `TickToPriceIsMonotonic.spec`
on `TickLib.wExp` and `TickLib.tickToPrice` from
[midnight@96d31343](https://github.com/morpho-org/midnight/tree/96d31343e993329e7a593dde46516a2c0cbcd142).
The source is imported unmodified from the shared `../vendor/midnight` submodule,
through Morpho's harness `certora/helpers/TickLibWrapper.sol`.

| file | content |
| --- | --- |
| [Import.lean](TickLib/Import.lean) | the Solidity import |
| [Spec.lean](TickLib/Spec.lean) | the rules, as definitions |
| [Proof.lean](TickLib/Proof.lean) | the theorems that the rules hold |
| [Execution.lean](TickLib/Execution.lean) | the imported bodies, executed to word functions |
| [Signed.lean](TickLib/Signed.lean) | 256-bit signed words as integers |
| [Math.lean](TickLib/Math.lean) | why `wExp` and `tickToPrice` are monotone |
| [check/](check) | import replay, provenance and axiom audit |

This is a separate Lake package, pinned to Verity
`10f697bbb52dd9273591490137fe20593db56dde`. Older Verity revisions cannot import
`int256` or `wExp`'s recursive call. Newer ones import the root
`updatePositionView(Market, ..)` with an explicit ABI prelude, which the root
proof does not cover.

```sh
sh check/check.sh
```

## What is trusted

The trust base is the same as the root proof's (see [../check/README.md](../check/README.md)):

- solc 0.8.34 (checksum-pinned; `viaIR`, `osaka`, 466 optimizer runs) for the AST;
- Verity's Solidity-to-`CompilationModel` translator, which is not verified.
  `check/check_import.py` re-imports the current Solidity and checks that the
  result is the proved model. The proofs restate the imported bodies, and
  `Execution.lean` checks the restatement against the import by `rfl`.
- The importer inlines `wExp`'s recursive call `wExp(-x)`, with a guard that
  reverts when `-x` is still negative. That only happens at `type(int256).min`,
  which is outside every rule's range. On the wrapped call itself this matches solc.

There is no differential test (A/B/C) for TickLib in this package.
