import MorphoMidnight.Witness

open Compiler.CompilationModel
open Compiler.CompilationModel.SoliditySlice
open Compiler.CompilationModel.Denote

/-- The imported body is on the slice whitelist, so the denotation theorem
`execStmtList_slice_storageWords` applies to it. This does not identify the
denotation's slots with Keccak slots. -/
theorem midnight_body_covered : stmtListCovered midnightBody = true := by
  unfold midnightBody
  decide

theorem midnight_storage_unchanged
    (oracle : DenoteOracle) (world : Verity.ContractState) (timestamp : Nat) (bindings : Env) :
    let state : DenoteState :=
      { world := { world with blockTimestamp := Verity.Core.Uint256.ofNat timestamp }
        bindings := bindings }
    preservesWorld state (execStmtList oracle midnight.model.fields state midnightBody) :=
  execStmtList_slice_storageWords oracle midnight.model.fields world timestamp bindings midnightBody
    midnight_body_covered
