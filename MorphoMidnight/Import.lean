import Compiler.SoliditySlice.Import

/-!
Import of `Midnight.updatePositionView` at
`morpho-org/midnight@96d31343e993329e7a593dde46516a2c0cbcd142`.

The executable artifact is `midnight.model : CompilationModel`.
`midnight.sliceCovered` is the kernel check that every constructor in that
model is in the slice denotation whitelist. It is not a proof that the model
matches solc bytecode.
-/

solidity_slice_import midnight
  slice_root "vendor/midnight" slice_entry "src/Midnight.sol"
  slice_contract "Midnight" slice_function "updatePositionView"
  slice_param_tys ["struct Market", "bytes32", "address"]
  slice_solc "0.8.34+commit.80d5c536" slice_via_ir true slice_evm "osaka"
  slice_optimizer true slice_runs 466 slice_bytecode_hash "none"
