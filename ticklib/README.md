# TickLib monotonicity

Proves the Certora rules of `TickToPrice.spec` and `TickToPriceIsMonotonic.spec`
on `TickLib.wExp` and `TickLib.tickToPrice` from
[midnight@96d31343](https://github.com/morpho-org/midnight/tree/96d31343e993329e7a593dde46516a2c0cbcd142).
The Solidity is imported unmodified from the shared `../vendor/midnight` submodule,
through Morpho's Certora harness `certora/helpers/TickLibWrapper.sol`, which exposes
the library's internal functions as external ones.

## How to read it

Three files say what is proved. The `Proof/` folder holds the supporting lemmas.

| file | role |
| --- | --- |
| [Import.lean](TickLib/Import.lean) | the Solidity import: Verity turns `TickLibWrapper.wExp` and `.tickToPrice` into Lean |
| [Spec.lean](TickLib/Spec.lean) | **what is claimed**: the nine rules, as Lean statements next to their CVL originals |
| [Proof.lean](TickLib/Proof.lean) | **the nine theorems** that the rules hold, each a few lines long |
| [Proof/Execution.lean](TickLib/Proof/Execution.lean) | step A: running the imported code returns a plain function on 256-bit words |
| [Proof/Bridge.lean](TickLib/Proof/Bridge.lean) | step B: on the rules' ranges, that word function equals the same formula on integers |
| [Proof/Signed.lean](TickLib/Proof/Signed.lean) | helper for A and B: `int256` word operations equal integer operations while nothing overflows |
| [Proof/Math.lean](TickLib/Proof/Math.lean) | step C: why the integer formulas are monotone |

How the steps chain for `wExpIsMonotonic` (`tickToPrice` follows the same path):

```
tickLib.wExp x     imported code               (Import.lean)
      │ A  Proof/Execution.lean
      ▼
wExpW x            function on 256-bit words
      │ B  Proof/Bridge.lean + Proof/Signed.lean, for -X* ≤ x ≤ X*
      ▼
wExpVal x          same formula on integers
      │ C  Proof/Math.lean: x ≤ y → wExpVal x ≤ wExpVal y
      ▼
wExpIsMonotonic    (Proof.lean)
```

The core argument, in `Proof/Math.lean`: write `x = q·ln2 + r`. Within one value of `q`,
the cubic `expR(r)` grows with `r`. When `q` increases by one, the shift doubles the result,
and `expR(ln2 - offset - 1) = 2·expR(-offset)` holds with equality, so nothing drops at the
seam. Negative inputs go through `1e36 / wExp(-x)`. `tickToPrice` rounds `1e36 / (1e18 + wExp)`,
which can only grow as `wExp` shrinks.

## Checks

`sh check/check.sh` (also run by the root `./check/check.sh` and CI) does the same checks
as the root package does for `updatePositionView`:

- **build** the proofs;
- **import replay** (`check_import.py`): re-import the current Solidity and check it is
  the model the proofs are about (`check/provenance/` holds the expected snapshot);
- **differential tests** (`differential-*.json`, `*-cases.json`): run the imported model
  and the solc-compiled bytecode on the same inputs and compare results and reverts.
  Each function gets its boundary inputs (0, ±X*, X*+1, segment edges, ticks 0/3372/6744/6745)
  plus 256 random ones;
- **axiom audit** (`AxiomAudit.lean`): every theorem depends only on Lean's three
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

This is a separate Lake package pinned to Verity
`10f697bbb52dd9273591490137fe20593db56dde`, the revision that can import `int256` and
`wExp`'s recursive call. The same revision imports the root `updatePositionView(Market, ..)`
with an explicit ABI prelude, which the root proof does not cover, so the root package stays
on its older pin.

## What is trusted

The trust base is the same as the root proof's (see [../check/README.md](../check/README.md)):

- solc 0.8.34 (checksum-pinned; `viaIR`, `osaka`, 466 optimizer runs) for the AST;
- Verity's Solidity-to-`CompilationModel` translator, which is not verified. The import
  replay and the differential tests above check it on this code.
- The importer inlines `wExp`'s recursive call `wExp(-x)` with a guard that reverts when
  `-x` is still negative. That only happens at `type(int256).min`, where the Solidity
  recurses until it runs out of gas. It is outside every rule's range and not part of the
  differential inputs.
