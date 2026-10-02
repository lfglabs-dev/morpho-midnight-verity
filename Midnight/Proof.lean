import Midnight.Lemmas.Walk

/-!
`updatePositionViewProperties` from the execution of the imported body.
-/

open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight

private theorem uint128_ofNat_val {n : Nat} (h : n ≤ U) :
    (UIntN.ofNat 128 n).val = n := by
  have hlt : n < 2 ^ 128 := by
    have : U + 1 = 2 ^ 128 := by decide
    omega
  simp [UIntN.ofNat, Nat.mod_eq_of_lt hlt]

private theorem uint128_zero_val : (0 : UIntN 128).val = 0 := rfl

theorem updatePositionViewProperties : Spec.updatePositionViewProperties := by
  intro oracle world maturity id user newCredit newPendingFee fee old hreq hcall
  have hord :
      (midnight.position.lastLossFactor oracle world id user).val ≤
        (midnight.marketState.lossFactor oracle world id).val :=
    hreq.lastLossFactorLeqMarketLossFactor
  unfold midnight.updatePositionView at hcall
  simp only [toWord_uint256, toWord_bytes32, toWord_address] at hcall
  rw [exec_view oracle world maturity id user hord] at hcall
  simp only [midnight.position.credit_val, midnight.position.pendingFee_val,
    midnight.position.lastLossFactor_val, midnight.position.lastAccrual_val,
    midnight.marketState.lossFactor_val] at hcall
  let credit := readMember oracle midnight.model world "position" [id.val, user.val] "credit"
  let pending := readMember oracle midnight.model world "position" [id.val, user.val] "pendingFee"
  let llf := readMember oracle midnight.model world "position" [id.val, user.val] "lastLossFactor"
  let lf := readMember oracle midnight.model world "marketState" [id.val] "lossFactor"
  let lastAccrual := readMember oracle midnight.model world "position" [id.val, user.val] "lastAccrual"
  have hcredU : credit ≤ U := by
    simpa [credit, midnight.position.credit_val] using
      uint128_le_U (midnight.position.credit oracle world id user)
  have hllU : llf ≤ U := by
    simpa [llf, midnight.position.lastLossFactor_val] using
      uint128_le_U (midnight.position.lastLossFactor oracle world id user)
  have hlfU : lf ≤ U := by
    simpa [lf, midnight.marketState.lossFactor_val] using
      uint128_le_U (midnight.marketState.lossFactor oracle world id)
  have hpendU : pending ≤ U := by
    simpa [pending, midnight.position.pendingFee_val] using
      uint128_le_U (midnight.position.pendingFee oracle world id user)
  have hordN : llf ≤ lf := by simpa [llf, lf, midnight.position.lastLossFactor_val,
    midnight.marketState.lossFactor_val] using hord
  cases hv : viewResult? credit llf lf pending lastAccrual world.blockTimestamp.val maturity.val with
  | none =>
    rw [hv] at hcall
    simp at hcall
  | some packed =>
    obtain ⟨ncN, npN, feeN⟩ := packed
    rw [hv] at hcall
    simp at hcall
    cases hcall with
    | intro hnc hrest =>
      cases hrest with
      | intro hnp hfeeEq =>
        have hassert := asserts_of_view hcredU hllU hlfU hpendU hordN hv
        have hncLe : ncN ≤ credit := hassert.2.2.1
        have hnpLe : npN ≤ pending := hassert.2.2.2.1
        have hfeeLeP : feeN ≤ pending := hassert.1
        have hncVal : newCredit.val = ncN := by
          rw [← hnc]; exact uint128_ofNat_val (Nat.le_trans hncLe hcredU)
        have hnpVal : newPendingFee.val = npN := by
          rw [← hnp]; exact uint128_ofNat_val (Nat.le_trans hnpLe hpendU)
        have hfeeVal : fee.val = feeN := by
          rw [← hfeeEq]; exact uint128_ofNat_val (Nat.le_trans hfeeLeP hpendU)
        have hpendVal : old.pendingFee.val = pending := by
          simp [old, Spec.old, pending, midnight.position.pendingFee_val]
        have hcredVal : old.credit.val = credit := by
          simp [old, Spec.old, credit, midnight.position.credit_val]
        have hllVal : old.lastLossFactor.val = llf := by
          simp [old, Spec.old, llf, midnight.position.lastLossFactor_val]
        have hlfVal : old.lossFactor.val = lf := by
          simp [old, Spec.old, lf, midnight.marketState.lossFactor_val]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show fee.val ≤ old.pendingFee.val
          rw [hfeeVal, hpendVal]
          exact hfeeLeP
        · rw [mapFactor_eq_nat, mapFactor_eq_nat, hncVal, hfeeVal, hllVal, hlfVal, hcredVal]
          simpa [Int.natCast_add, Int.natCast_mul] using Int.ofNat_le.mpr hassert.2.1
        · show newCredit.val ≤ old.credit.val
          rw [hncVal, hcredVal]
          exact hncLe
        · show newPendingFee.val ≤ old.pendingFee.val
          rw [hnpVal, hpendVal]
          exact hnpLe
        · intro hz
          have hloss : lf = U := by
            have hval := (mapFactor_eq_zero_iff old.lossFactor).1 hz
            simpa [hlfVal] using hval
          have hpair := hassert.2.2.2.2 (by simp [hloss])
          refine ⟨?_, ?_⟩
          · apply UIntN.ext
            rw [hncVal, hpair.1, uint128_zero_val]
          · apply UIntN.ext
            rw [hfeeVal, hpair.2, uint128_zero_val]

end Midnight
