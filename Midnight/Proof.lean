import Midnight.Lemmas.Return
import Midnight.Lemmas.PostSlash
import Midnight.Lemmas.Call
import Midnight.Lemmas.Math

/-!
Proof of `Spec.updatePositionViewProperties`.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight

private theorem prefixList_id_user_preCredit :
    prefixList ["id", "user"] preCredit = true := by decide

private theorem prefixList_psc_midPending :
    prefixList ["postSlashCredit", "_credit", "_lastLossFactor", "id", "user"] midPending =
      true := by decide

theorem updatePositionViewProperties : Spec.updatePositionViewProperties := by
  intro oracle world obligationMaturity id user newCredit newPendingFee fee
  show Requires (Spec.old oracle world id user) →
    midnight.updatePositionView oracle world obligationMaturity id user =
      some (newCredit, newPendingFee, fee) →
    Asserts (Spec.old oracle world id user) newCredit newPendingFee fee
  intro hreq hcall
  obtain ⟨w0, w1, w2, final, hexec, hobs, hnc, hnp, hf⟩ :=
    updatePositionView_exec_stop oracle world obligationMaturity id user
      newCredit newPendingFee fee hcall
  set s0 := initState world obligationMaturity id user
  have hbody := body_eq_parts
  rw [hbody] at hexec
  obtain ⟨sCredit, hCredit, hexec1⟩ :=
    split_prefix oracle midnight.model.fields s0 final
      preCredit (midPending ++ midFee ++ postFee) preCredit_prefix (by
        simpa [List.append_assoc] using hexec)
  obtain ⟨sPending, hPending, hexec2⟩ :=
    split_prefix oracle midnight.model.fields sCredit final
      midPending (midFee ++ postFee) midPending_prefix (by
        simpa [List.append_assoc] using hexec1)
  obtain ⟨sFee, hFee, hPost⟩ :=
    split_prefix oracle midnight.model.fields sPending final
      midFee postFee midFee_prefix hexec2
  have hps : PostSlashState oracle world id user sCredit :=
    preCredit_continue_postSlash oracle world obligationMaturity id user sCredit hCredit
  -- Preserve id/user across preCredit.
  have hframe_cu := list_frame oracle midnight.model.fields s0 preCredit
    ["id", "user"] prefixList_id_user_preCredit
  simp only [Frame, hCredit] at hframe_cu
  have hid : lookupValue sCredit.bindings "id" = id.val := by
    have := hframe_cu.2 "id" (by simp)
    simpa [s0, initState, callBindings, lookupValue, Word.toWord] using this
  have huser : lookupValue sCredit.bindings "user" = user.val := by
    have := hframe_cu.2 "user" (by simp)
    simpa [s0, initState, callBindings, lookupValue, Word.toWord] using this
  have hpend := midPending_continue_le oracle world id user sCredit sPending
    hps hid huser hPending
  -- Preserve postSlashCredit across midPending.
  have hframe_pend := list_frame oracle midnight.model.fields sCredit midPending
    ["postSlashCredit", "_credit", "_lastLossFactor", "id", "user"]
    prefixList_psc_midPending
  simp only [Frame, hPending] at hframe_pend
  have hpsc_pending : lookupValue sPending.bindings "postSlashCredit" =
      lookupValue sCredit.bindings "postSlashCredit" :=
    hframe_pend.2 "postSlashCredit" (by simp)
  -- Frame across fee.
  have hframe_fee := midFee_preserves_postSlash oracle midnight.model.fields
    sPending sFee hFee
  set credit := (midnight.position.credit oracle world id user).val
  set pending := (midnight.position.pendingFee oracle world id user).val
  set lastLoss := (midnight.position.lastLossFactor oracle world id user).val
  set loss := (midnight.marketState.lossFactor oracle world id).val
  set psc := slashFormula credit lastLoss loss
  have hpsc_bind : lookupValue sFee.bindings "postSlashCredit" = psc := by
    rw [hframe_fee.1, hpsc_pending, hps.postSlash_eq]
  set psp := lookupValue sPending.bindings "postSlashPendingFee"
  have hpsp_bind : lookupValue sFee.bindings "postSlashPendingFee" = psp := hframe_fee.2
  have hpsp_le_pending : psp ≤ pending := hpend.1
  have hcredit_le := credit_val_le_max oracle world id user
  have hpending_le := pendingFee_val_le_max oracle world id user
  have hlast_le := lastLossFactor_val_le_max oracle world id user
  have hloss_le := lossFactor_val_le_max oracle world id
  have hreq' : lastLoss ≤ loss := hreq.lastLossFactorLeqMarketLossFactor
  have hpsc_le_credit : psc ≤ credit :=
    slash_formula_le_credit credit lastLoss loss hreq'
  have hpsc_le : psc ≤ max128 := le_trans hpsc_le_credit hcredit_le
  have hpsp_le : psp ≤ max128 := le_trans hpsp_le_pending hpending_le
  set feeVal := lookupValue sFee.bindings "fee"
  have hw := postFee_stop_return oracle midnight.model.fields sFee final
    psc psp feeVal hpsc_bind hpsp_bind rfl hpsc_le hpsp_le hPost
  rcases hw with ⟨w0', w1', w2', hobs', hw2, hfee_le_psc, hw0, hfee_le_psp, hw1⟩
  have hwords : w0 = w0' ∧ w1 = w1' ∧ w2 = w2' := by
    have := Option.some.inj (hobs.symm.trans hobs')
    simp only [List.cons.injEq, and_true] at this
    exact this
  have hw0eq := hwords.1
  have hw1eq := hwords.2.1
  have hw2eq := hwords.2.2
  have hw0_le : w0 ≤ max128 := by
    rw [hw0eq, hw0]; exact le_trans (Nat.sub_le _ _) hpsc_le
  have hw1_le : w1 ≤ max128 := by
    rw [hw1eq, hw1]; exact le_trans (Nat.sub_le _ _) hpsp_le
  have hw2_le : w2 ≤ max128 := by
    rw [hw2eq, hw2]; exact le_trans hfee_le_psc hpsc_le
  have hnc_val : newCredit.val = w0 := by rw [hnc, uintN_val_ofWord_of_le hw0_le]
  have hnp_val : newPendingFee.val = w1 := by rw [hnp, uintN_val_ofWord_of_le hw1_le]
  have hf_val : fee.val = w2 := by rw [hf, uintN_val_ofWord_of_le hw2_le]
  refine {
    feeLeOldPendingFee := ?_
    creditWithFeeLeCreditAfterSlashing := ?_
    newCreditLeOldCredit := ?_
    newPendingFeeLeOldPendingFee := ?_
    noCreditFeeOnTotalLossFactor := ?_
  }
  · -- fee ≤ oldPendingFee
    change fee.val ≤ pending
    rw [hf_val, hw2eq, hw2]
    exact le_trans hfee_le_psp hpsp_le_pending
  · -- (newCredit + fee) * mapFactor(last) ≤ credit * mapFactor(loss)
    have hadd : newCredit.val + fee.val = psc := by
      rw [hnc_val, hf_val, hw0eq, hw2eq, hw0, hw2]
      exact Nat.sub_add_cancel hfee_le_psc
    change ((newCredit.val : Int) + fee.val) * mapFactor
        (midnight.position.lastLossFactor oracle world id user) ≤
      (midnight.position.credit oracle world id user).val *
        mapFactor (midnight.marketState.lossFactor oracle world id)
    have haddI : (newCredit.val : Int) + fee.val = (psc : Int) := by exact_mod_cast hadd
    rw [haddI]
    -- Work with mapFactor in Nat form without unfolding storage accessors.
    have hL : mapFactor (midnight.position.lastLossFactor oracle world id user) =
        ((max128 - lastLoss : Nat) : Int) := mapFactor_as_nat _
    have hR : mapFactor (midnight.marketState.lossFactor oracle world id) =
        ((max128 - loss : Nat) : Int) := mapFactor_as_nat _
    rw [hL, hR]
    have hnat : psc * (max128 - lastLoss) ≤ credit * (max128 - loss) := by
      rw [show psc = slashFormula credit lastLoss loss from rfl]
      exact slash_formula_mul_le credit lastLoss loss
    -- ↑psc * ↑(max128 - lastLoss) = ↑(psc * (max128 - lastLoss)), similarly RHS.
    have hcast : (psc : Int) * ((max128 - lastLoss : Nat) : Int) =
        ↑(psc * (max128 - lastLoss)) := by rw [Int.natCast_mul]
    have hcast' : (credit : Int) * ((max128 - loss : Nat) : Int) =
        ↑(credit * (max128 - loss)) := by rw [Int.natCast_mul]
    rw [hcast, hcast']
    exact Int.ofNat_le.mpr hnat
  · -- newCredit ≤ oldCredit
    change newCredit.val ≤ credit
    rw [hnc_val, hw0eq, hw0]
    exact le_trans (Nat.sub_le _ _) hpsc_le_credit
  · -- newPendingFee ≤ oldPendingFee
    change newPendingFee.val ≤ pending
    rw [hnp_val, hw1eq, hw1]
    exact le_trans (Nat.sub_le _ _) hpsp_le_pending
  · -- mapFactor(loss) = 0 → newCredit = 0 ∧ fee = 0
    intro hz
    have hloss_max : loss = max128 :=
      (mapFactor_eq_zero_iff (midnight.marketState.lossFactor oracle world id)).mp hz
    have hpsc0 : psc = 0 := by
      simp only [psc, slashFormula, hloss_max, Nat.sub_self, Nat.mul_zero, Nat.zero_div]
      split <;> rfl
    have hfee0' : feeVal = 0 := Nat.eq_zero_of_le_zero (by simpa [hpsc0] using hfee_le_psc)
    have hw00 : w0 = 0 := by rw [hw0eq, hw0, hpsc0, hfee0']
    have hw20 : w2 = 0 := by rw [hw2eq, hw2, hfee0']
    refine ⟨UIntN.ext ?_, UIntN.ext ?_⟩
    · rw [hnc_val, hw00]; rfl
    · rw [hf_val, hw20]; rfl

end Midnight
