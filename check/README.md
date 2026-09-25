# Checking the import

`./check/check.sh` builds every proof, then:

1. re-imports the current Solidity and checks, in the kernel, that it equals the
   proved `midnight.model`; the model and the import inventory must also match
   [provenance/](provenance) ([check_import.py](check_import.py));
   [provenance/functions.txt](provenance/functions.txt) must match the status
   of each imported function (see below);
2. runs the [fixed vectors](vectors.json) plus 256 random cases through Verity's
   differential engine, comparing the original Solidity, the imported model in
   Lean, and the model compiled by Verity ([config](differential.json));
3. checks that the theorem only uses Lean's standard axioms
   `propext`, `Classical.choice` and `Quot.sound` ([AxiomAudit.lean](AxiomAudit.lean)).

## What is imported

| Solidity | Treatment |
| --- | --- |
| `Midnight.updatePositionView` | Entire body, including checked arithmetic and narrowing casts |
| `UtilsLib.mulDivDown`, `mulDivUp`, `min` | Original bodies, inlined (no summaries) |
| `position`, `marketState` | Storage layout from solc, including packed uint128 members |
| `Market market` | Projected to `market.maturity`, the only member read |

Every other declaration is excluded and listed in
[provenance/report.txt](provenance/report.txt). Unsupported Solidity reached
from `updatePositionView` makes the import fail.

## Status of the imported function

[provenance/functions.txt](provenance/functions.txt) records four separate
facts about `updatePositionView`; none implies the next:

- **importable**: the import succeeded;
- **denoteCovered**: every constructor in the model has an explicit Denote
  semantics (`midnight.covered`, checked by the kernel);
- **compilable**: Verity's compiler accepts the model. This is a compile
  attempt, not a correctness result; the compiled code is only tested (step 2);
- **compilerProofCovered**: `unavailable`. No Verity compiler-correctness
  theorem applies to the imported model.

## What is trusted

- **solc 0.8.34** (checksum-pinned; `viaIR`, `osaka`, 466 optimizer runs,
  as in Midnight's Foundry profile) for the AST and the storage layout.
- **Verity's Solidity-to-`CompilationModel` translator**, which is not formally
  verified. The differential tests support it; they do not prove it. Its
  supported subset and trust boundary are documented in
  [SOLIDITY_IMPORT.md](https://github.com/lfglabs-dev/verity/blob/9b472a8a48a9990337845f1720a20f374fa1e9cd/docs/SOLIDITY_IMPORT.md).
- **Mapping slots**: the theorem holds for any slot oracle, so it does not
  depend on Keccak, and it does not prove that the oracle is Keccak.

## What is not claimed

- Success: the theorem is about successful calls. Some calls that satisfy the
  premises revert (vector `B`).
- `lastLossFactor <= lossFactor` holding in every reachable state. It is
  assumed on the pre-state, like the rule's `require`; Certora proves it as the
  invariant `lastLossFactorLeqMarketLossFactor` in `Midnight.spec`.
- Equivalence with the deployed bytecode, ABI decoding, and gas.
