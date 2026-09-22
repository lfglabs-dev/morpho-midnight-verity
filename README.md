# morpho-midnight-verity

Pilot import of `Midnight.updatePositionView` from
`morpho-org/midnight@96d31343e993329e7a593dde46516a2c0cbcd142` into a Verity
`CompilationModel`.

The executable artifact is `midnight.model`, elaborated by
`solidity_slice_import` in `MorphoMidnight/Import.lean`. The numeric properties
in `MorphoMidnight/Spec.lean` are about the mathematical slash-and-accrue
functions. They are not yet a kernel theorem that `midnight.model` computes
those functions. See `TRUST.md`.

## Check

```sh
./scripts/check.sh
```

That builds the import, runs the original Solidity on `test/vectors.json` with
Foundry (solc 0.8.34, `via_ir`, Osaka, optimizer 466 runs), compares those
results with `denoteScalarBody` on the imported model, and prints `#print axioms`
for the numeric theorems.

The pinned solc binary must be executable at `.lake/solidity-import/solc-0.8.34`.
Its SHA-256 is the pin in Verity `Compiler/SoliditySlice/Import.lean`.

`out/slice-report.txt` is written when the import elaborates. A copy of the
report from the checked build is `provenance/slice-report.txt`. It lists the
functions the closure kept, the functions it did not lower, the `market.maturity`
projection, and the source digest.

## Licenses

`vendor/midnight` is the upstream tree, including its BUSL-1.1 and
GPL-2.0-or-later notices. This repository does not relicense that code.
