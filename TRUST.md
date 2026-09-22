# Trust boundary

## What the kernel checks

`midnight.model` is a `CompilationModel` elaborated from pinned solc's AST and
`storageLayout` for `Midnight.updatePositionView` and the helpers it reaches:
`UtilsLib.mulDivDown`, `UtilsLib.mulDivUp`, and `UtilsLib.min`.
`midnight.sliceCovered` is proved by `decide`: every constructor in that model
is in Verity's slice denotation whitelist. `midnight_body_covered` and
`midnight_storage_unchanged` are kernel theorems: a covered run does not change
`storageWords`. `MorphoMidnight.Spec` proves the five numeric properties, and
the Certora factor bridge, for the mathematical functions `q` and
`pendingAfterSlash`. Those proofs use no `sorry` and no project axiom.
`#print axioms` reports `propext` and, for `property5`, `Quot.sound`.

## What is still assumed

The Lean frontend that turns solc JSON into the model is not verified. A
theorem about `CompilationModel` execution does not relate that model to
solc's bytecode. `mappingSlot` is not Keccak; numeric statements are about the
values the denotation reads back from the words placed at its own slots.

`MorphoMidnight.Spec` is not connected to `midnight.model` by a kernel
theorem. There is no kernel proof that a successful `denoteScalarBody` run
returns `q` and `pendingAfterSlash`. The build's `#eval` checks witnesses A
`(95, 5, 5)` and B (revert) on `midnight.model`. `lake exe morpho_diff` checks
sixteen vectors against the original Solidity function, including success and
revert in both directions. Those checks are tests. The smoke twin in Verity
also has an interpreter check of the same two witnesses and a kernel proof of
its first packed `credit` read only.

## Compiler pin

solc `0.8.34+commit.80d5c536`, `viaIR = true`, `evmVersion = osaka`, optimizer
enabled with 466 runs, `bytecodeHash = none` (Foundry's Midnight profile).
Certora's `UpdatePositionView.conf` uses the same compiler, IR pipeline, and
EVM version, and does not set the optimizer. For this slice the AST and
storage layout do not depend on the optimizer; the import records the Foundry
settings. The binary SHA-256 is the pin in
`lfglabs-dev/verity` `Compiler/SoliditySlice/Import.lean`.

## Excluded

Gas, deployed bytecode, ABI decoding of the public `Market` argument (the model
takes `market_maturity`, `id`, and `user`), panic payloads, whole-contract
`preciseCreditCorrect`, storage writes, loops, external calls, and Keccak slot
identity. The rule is about successful calls. It does not prove that every
state satisfying the Certora `require`s succeeds. Witness B reverts under those
hypotheses.
