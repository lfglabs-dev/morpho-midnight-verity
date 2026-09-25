import Midnight.Spec
import Compiler.SolidityImport.Proofs

/-!
Arithmetic of slashing, with no execution. Write `L = max - lastLossFactor` and
`G = max - lossFactor` (`max = type(uint128).max`). Slashing multiplies the
credit by `G / L`, rounding down; `lastLossFactor ≤ lossFactor` makes `G ≤ L`,
so the ratio is at most 1.
-/

open Compiler.CompilationModel.SolidityImport Midnight.Spec
namespace Midnight.Lemmas

/-- `postSlashCredit` in `updatePositionView`:
`_lastLossFactor < max ? _credit.mulDivDown(max - lossFactor, max - _lastLossFactor) : 0`. -/
def postSlashCredit (credit lastLossFactor lossFactor : Nat) : Nat :=
  if lastLossFactor < max128 then credit * (max128 - lossFactor) / (max128 - lastLossFactor) else 0

/-- The ratio `G / L` is at most 1: slashing never increases credit. -/
theorem postSlashCredit_le {c l g : Nat} (hlg : l ≤ g) : postSlashCredit c l g ≤ c := by
  unfold postSlashCredit
  split
  · calc c * (max128 - g) / (max128 - l)
        ≤ c * (max128 - l) / (max128 - l) := Nat.div_le_div_right (by gcongr)
      _ = c := Nat.mul_div_cancel c (by omega)
  · exact Nat.zero_le _

/-- The division rounds down: `postSlashCredit * L ≤ credit * G`. -/
theorem postSlashCredit_mul_le (c l g : Nat) :
    postSlashCredit c l g * (max128 - l) ≤ c * (max128 - g) := by
  unfold postSlashCredit
  split
  · exact Nat.div_mul_le_self _ _
  · simp

/-- A total loss (`G = 0`) leaves no credit. -/
theorem postSlashCredit_total_loss (c l : Nat) : postSlashCredit c l max128 = 0 := by
  simp [postSlashCredit]

/-- `mapFactor` of a `uint128` is `max - factor`, which is `L` or `G`. -/
theorem mapFactor_eq (factor : Verity.Core.UIntN 128) :
    mapFactor factor = ((max128 - factor.val : Nat) : Int) := by
  have := factor.isLt
  unfold mapFactor max128
  omega

theorem mapFactor_eq_zero {factor : Verity.Core.UIntN 128} (h : mapFactor factor = 0) :
    factor.val = max128 := by
  have := factor.isLt
  rw [mapFactor_eq] at h
  unfold max128 at *
  omega

end Midnight.Lemmas
