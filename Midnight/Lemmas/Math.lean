import Midnight.Lemmas.Setup

/-!
Natural-number facts used to discharge the five asserts once the body's
post-slash / fee bindings are known.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight.Lemmas

theorem mapFactor_nonneg (f : UIntN 128) : 0 ≤ mapFactor f := by
  have : f.val ≤ max128 := Nat.le_pred_of_lt f.isLt
  simp only [mapFactor, max128] at this ⊢
  omega

theorem mapFactor_eq_zero_iff (f : UIntN 128) :
    mapFactor f = 0 ↔ f.val = max128 := by
  simp only [mapFactor, max128]
  constructor <;> intro h <;> omega

theorem mapFactor_as_nat (f : UIntN 128) :
    mapFactor f = ((max128 - f.val : Nat) : Int) := by
  have : f.val ≤ max128 := Nat.le_pred_of_lt f.isLt
  simp only [mapFactor, max128]
  exact (Int.natCast_sub this).symm

theorem slash_mul_le (credit lastLoss loss : Nat) :
    (credit * (max128 - loss) / (max128 - lastLoss)) * (max128 - lastLoss) ≤
      credit * (max128 - loss) :=
  Nat.div_mul_le_self _ _

theorem slash_le_credit (credit lastLoss loss : Nat)
    (hl : lastLoss ≤ loss) (hlast : lastLoss < max128) :
    credit * (max128 - loss) / (max128 - lastLoss) ≤ credit := by
  have hdenpos : 0 < max128 - lastLoss := Nat.sub_pos_of_lt hlast
  have hnum : max128 - loss ≤ max128 - lastLoss := Nat.sub_le_sub_left hl _
  calc
    credit * (max128 - loss) / (max128 - lastLoss)
        ≤ credit * (max128 - lastLoss) / (max128 - lastLoss) :=
          Nat.div_le_div_right (Nat.mul_le_mul_left credit hnum)
    _ = credit := Nat.mul_div_left credit hdenpos

theorem slash_formula_mul_le (credit lastLoss loss : Nat) :
    (if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0) *
        (max128 - lastLoss) ≤
      credit * (max128 - loss) := by
  split
  · exact slash_mul_le credit lastLoss loss
  · simp

theorem slash_formula_le_credit (credit lastLoss loss : Nat)
    (hl : lastLoss ≤ loss) :
    (if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0) ≤
      credit := by
  split
  · exact slash_le_credit credit lastLoss loss hl ‹_›
  · exact Nat.zero_le _

theorem slash_zero_of_loss_max (credit lastLoss : Nat) :
    (if lastLoss < max128 then credit * (max128 - max128) / (max128 - lastLoss) else 0) = 0 := by
  split <;> simp

theorem add_of_sub_eq {a b c : Nat} (h : a - b = c) (hle : b ≤ a) : c + b = a := by
  omega

theorem uintN_val_ofWord (w : Nat) :
    (Word.ofWord w : UIntN 128).val = w % 2 ^ 128 := by
  simp only [Word.ofWord, UIntN.ofNat]

theorem uintN_val_ofWord_of_le {w : Nat} (hw : w ≤ max128) :
    (Word.ofWord w : UIntN 128).val = w := by
  rw [uintN_val_ofWord, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt hw (by decide : max128 < 2 ^ 128)

theorem credit_val_le_max (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) :
    (midnight.position.credit oracle world id user).val ≤ max128 :=
  Nat.le_pred_of_lt (midnight.position.credit oracle world id user).isLt

theorem pendingFee_val_le_max (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) :
    (midnight.position.pendingFee oracle world id user).val ≤ max128 :=
  Nat.le_pred_of_lt (midnight.position.pendingFee oracle world id user).isLt

theorem lastLossFactor_val_le_max (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) :
    (midnight.position.lastLossFactor oracle world id user).val ≤ max128 :=
  Nat.le_pred_of_lt (midnight.position.lastLossFactor oracle world id user).isLt

theorem lossFactor_val_le_max (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) :
    (midnight.marketState.lossFactor oracle world id).val ≤ max128 :=
  Nat.le_pred_of_lt (midnight.marketState.lossFactor oracle world id).isLt

/-- Int form of the slash inequality used by assert 2. -/
theorem slash_int_le (credit lastLoss loss : Nat)
    (hlastBound : lastLoss ≤ max128) (hlossBound : loss ≤ max128) (psc : Nat)
    (hpsc : psc = if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0) :
    (psc : Int) * ((max128 : Int) - lastLoss) ≤ (credit : Int) * ((max128 : Int) - loss) := by
  have hnat : psc * (max128 - lastLoss) ≤ credit * (max128 - loss) := by
    rw [hpsc]
    exact slash_formula_mul_le credit lastLoss loss
  calc
    (psc : Int) * ((max128 : Int) - lastLoss)
        = (psc * (max128 - lastLoss) : Nat) := by
          rw [← Int.natCast_sub hlastBound, ← Int.natCast_mul]
    _ ≤ (credit * (max128 - loss) : Nat) := Int.ofNat_le.mpr hnat
    _ = (credit : Int) * ((max128 : Int) - loss) := by
          rw [← Int.natCast_sub hlossBound, ← Int.natCast_mul]

end Midnight.Lemmas
