import Midnight.Lemmas.Setup

/-!
Extract a successful `midnight.updatePositionView` call into a `.stop` execution
of the imported body with concrete return words.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas

namespace Midnight.Lemmas

def initState (world : Verity.ContractState)
    (obligationMaturity : Uint256) (id : BytesN 32) (user : Address) : DenoteState :=
  { world, bindings := callBindings obligationMaturity id user }

/-- Successful `updatePositionView` ran the body to `.stop` with the three return words. -/
theorem updatePositionView_exec_stop
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (obligationMaturity : Uint256) (id : BytesN 32) (user : Address)
    (newCredit newPendingFee fee : UIntN 128)
    (hcall : midnight.updatePositionView oracle world obligationMaturity id user =
      some (newCredit, newPendingFee, fee)) :
    ∃ (w0 w1 w2 : Nat) (final : DenoteState),
      execStmtList oracle midnight.model.fields
        (initState world obligationMaturity id user) body = .stop final ∧
      final.observedReturnWords = some [w0, w1, w2] ∧
      newCredit = Word.ofWord w0 ∧
      newPendingFee = Word.ofWord w1 ∧
      fee = Word.ofWord w2 := by
  set s0 := initState world obligationMaturity id user
  have hends :
      execStmtList oracle midnight.model.fields s0 body = .revert ∨
        ∃ t, execStmtList oracle midnight.model.fields s0 body = .stop t := by
    have := ends_return oracle midnight.model.fields s0
      (preCredit ++ midPending ++ midFee ++ postFeePre) retArgs full_pre_return_prefix
    simpa [body_eq_parts_return] using this
  -- Match `runFunction`'s nesting exactly so `rfl` goes through.
  have hwrap :
      midnight.updatePositionView oracle world obligationMaturity id user =
        match
          match execStmtList oracle midnight.model.fields s0 body with
          | .stop state | .continue state | .return _ state => state.observedReturnWords
          | .revert => none
        with
        | some [r0, r1, r2] => some (Word.ofWord r0, Word.ofWord r1, Word.ofWord r2)
        | _ => none := by
    unfold midnight.updatePositionView runFunction s0 initState
    rfl
  rw [hwrap] at hcall
  cases hends with
  | inl hrev =>
    rw [hrev] at hcall
    nomatch hcall
  | inr hex =>
    rcases hex with ⟨final, hstop⟩
    rw [hstop] at hcall
    cases hr : final.observedReturnWords with
    | none =>
      simp only [hr] at hcall
      nomatch hcall
    | some words =>
      simp only [hr] at hcall
      match words with
      | [w0, w1, w2] =>
        refine ⟨w0, w1, w2, final, hstop, hr, ?_⟩
        have := Option.some.inj hcall
        exact ⟨congrArg Prod.fst this.symm,
          congrArg Prod.fst (congrArg Prod.snd this.symm),
          congrArg Prod.snd (congrArg Prod.snd this.symm)⟩
      | [] => nomatch hcall
      | [_] => nomatch hcall
      | [_, _] => nomatch hcall
      | _ :: _ :: _ :: _ :: _ => nomatch hcall

end Midnight.Lemmas
