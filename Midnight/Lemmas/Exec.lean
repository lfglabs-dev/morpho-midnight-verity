import Midnight.Lemmas.Math
import Midnight.Lemmas.Call

/-!
Stepping lemmas for `execStmtList` on the imported `updatePositionView` body.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight.Lemmas

theorem eval_param (oracle : DenoteOracle) (fs : List Field) (s : DenoteState) (n : String) :
    evalExpr oracle fs s (.param n) = some (lookupValue s.bindings n) := by
  simp [evalExpr]

theorem eval_local (oracle : DenoteOracle) (fs : List Field) (s : DenoteState) (n : String) :
    evalExpr oracle fs s (.localVar n) = some (lookupValue s.bindings n) := by
  simp [evalExpr]

theorem eval_literal (oracle : DenoteOracle) (fs : List Field) (s : DenoteState) (n : Nat) :
    evalExpr oracle fs s (.literal n) = some (wordNormalize n) := by
  simp [evalExpr]

theorem credit_read_eq
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) :
    readMember oracle midnight.model world "position" [id.val, user.val] "credit" =
      (midnight.position.credit oracle world id user).val :=
  (midnight.position.credit_val oracle world id user).symm

theorem lastLossFactor_read_eq
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) :
    readMember oracle midnight.model world "position" [id.val, user.val] "lastLossFactor" =
      (midnight.position.lastLossFactor oracle world id user).val :=
  (midnight.position.lastLossFactor_val oracle world id user).symm

theorem pendingFee_read_eq
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) :
    readMember oracle midnight.model world "position" [id.val, user.val] "pendingFee" =
      (midnight.position.pendingFee oracle world id user).val :=
  (midnight.position.pendingFee_val oracle world id user).symm

theorem lossFactor_read_eq
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) :
    readMember oracle midnight.model world "marketState" [id.val] "lossFactor" =
      (midnight.marketState.lossFactor oracle world id).val :=
  (midnight.marketState.lossFactor_val oracle world id).symm

/-- Lookup of call parameters in the initial state. -/
theorem lookup_init_id
    (world : Verity.ContractState)
    (obligationMaturity : Uint256) (id : BytesN 32) (user : Address) :
    lookupValue (callBindings obligationMaturity id user) "id" = id.val := by
  simp [callBindings, lookupValue, Word.toWord]

theorem lookup_init_user
    (world : Verity.ContractState)
    (obligationMaturity : Uint256) (id : BytesN 32) (user : Address) :
    lookupValue (callBindings obligationMaturity id user) "user" = user.val := by
  simp [callBindings, lookupValue, Word.toWord]

theorem lookup_init_maturity
    (world : Verity.ContractState)
    (obligationMaturity : Uint256) (id : BytesN 32) (user : Address) :
    lookupValue (callBindings obligationMaturity id user) "market_maturity" =
      obligationMaturity.val := by
  simp [callBindings, lookupValue, Word.toWord]

theorem wordNormalize_max128 : wordNormalize max128 = max128 := normalize_max

theorem wordNormalize_of_le {n : Nat} (h : n ≤ max128) : wordNormalize n = n :=
  word_of_small h

end Midnight.Lemmas
