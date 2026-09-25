import Midnight.Lemmas.Execution
import Midnight.Lemmas.Arithmetic

/-!
# Why the rule holds

`updatePositionView` ends with

    return (postSlashCredit - fee, postSlashPendingFee - fee, fee);

with checked subtractions, and `postSlashCredit = credit * G / L` rounded down,
where `L = max - lastLossFactor` and `G = max - lossFactor`.

1. **Execution** (`successful_call`, `Lemmas/Execution.lean`). A successful call
   did not underflow, so `newCredit + fee = postSlashCredit` and
   `newPendingFee + fee ≤ oldPendingFee`. What `fee` is does not matter.
2. **Arithmetic** (`Lemmas/Arithmetic.lean`). `lastLossFactor ≤ lossFactor` gives
   `G ≤ L`, so slashing multiplies the credit by at most 1, rounding down.
   Each assertion follows in one line, below.
-/

namespace Midnight
open Spec Lemmas

/-- The Certora rule `updatePositionViewProperties` holds (see `Spec.lean`). -/
theorem updatePositionViewProperties : Spec.updatePositionViewProperties := by
  intro oracle world maturity id user newCredit newPendingFee fee
  dsimp only
  intro requires success
  -- Step 1: `newCredit + fee = postSlashCredit` and `newPendingFee + fee ≤ oldPendingFee`.
  obtain ⟨hcredit, hpending⟩ :=
    successful_call oracle world maturity id user newCredit newPendingFee fee
      requires.lastLossFactorLeqMarketLossFactor success
  -- Step 2: `postSlashCredit ≤ oldCredit`, as `G / L ≤ 1`.
  have hslash := postSlashCredit_le (c := (Spec.old oracle world id user).credit.val)
    requires.lastLossFactorLeqMarketLossFactor
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. `fee ≤ newPendingFee + fee ≤ oldPendingFee`.
    show fee.val ≤ _; omega
  · -- 2. `(newCredit + fee) * L = postSlashCredit * L ≤ oldCredit * G`, rounding down.
    simp only [mapFactor_eq]
    exact_mod_cast hcredit ▸ postSlashCredit_mul_le ..
  · -- 3. `newCredit ≤ postSlashCredit ≤ oldCredit`.
    show newCredit.val ≤ _; omega
  · -- 4. `newPendingFee ≤ newPendingFee + fee ≤ oldPendingFee`.
    show newPendingFee.val ≤ _; omega
  · -- 5. `G = 0` gives `postSlashCredit = 0 = newCredit + fee`.
    intro htotal
    rw [mapFactor_eq_zero htotal, postSlashCredit_total_loss] at hcredit
    exact ⟨Verity.Core.UIntN.ext (by show newCredit.val = 0; omega),
      Verity.Core.UIntN.ext (by show fee.val = 0; omega)⟩

end Midnight
