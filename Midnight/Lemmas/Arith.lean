import Mathlib.Tactic
import Compiler.SolidityImport.Proofs

/-!
Arithmetic used by `updatePositionView`: 256-bit checked operations stay exact on
`uint128` inputs, and the branchless `min` matches the mathematical minimum.
-/

open Verity.Core
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport

namespace Midnight.Lemmas

theorem uint128_le_max (x : UIntN 128) : x.val ≤ max128 := by
  have h := x.isLt
  unfold max128 at *
  omega

theorem wordNormalize_of_lt {n : Nat} (h : n < Uint256.modulus) : wordNormalize n = n := by
  simp [wordNormalize, Uint256.ofNat, Nat.mod_eq_of_lt h]

theorem wordNormalize_le_max {n : Nat} (h : n ≤ max128) : wordNormalize n = n :=
  wordNormalize_of_lt (lt_of_le_of_lt h max128_lt)

@[simp] theorem boolWord_true : boolWord true = 1 := rfl
@[simp] theorem boolWord_false : boolWord false = 0 := rfl

theorem decide_false_of_not {p : Prop} [Decidable p] (h : ¬p) : decide p = false :=
  decide_eq_false h

theorem decide_true_of {p : Prop} [Decidable p] (h : p) : decide p = true :=
  decide_eq_true h

theorem mul128_lt {a b : Nat} (ha : a ≤ max128) (hb : b ≤ max128) :
    a * b < Uint256.modulus := by
  have hmax : max128 * max128 < Uint256.modulus := by decide
  exact lt_of_le_of_lt (Nat.mul_le_mul ha hb) hmax

theorem add128_lt {a b : Nat} (ha : a ≤ max128) (hb : b ≤ max128) :
    a + b < Uint256.modulus := by
  have hmax : max128 + max128 < Uint256.modulus := by decide
  exact lt_of_le_of_lt (Nat.add_le_add ha hb) hmax

/-- `p * k + (c - 1)` fits in a word when every factor is a `uint128`. -/
theorem mulDivUp_sum_lt {p k c : Nat} (hp : p ≤ max128) (hk : k ≤ max128) (hc : c ≤ max128) :
    p * k + (c - 1) < Uint256.modulus := by
  have hpk : p * k ≤ max128 * max128 := Nat.mul_le_mul hp hk
  have hcm : c - 1 ≤ max128 := by omega
  have hsum : p * k + (c - 1) ≤ max128 * max128 + max128 := by omega
  have hmod : max128 * max128 + max128 < Uint256.modulus := by decide
  exact lt_of_le_of_lt hsum hmod

theorem mul_div_le_self {a b c : Nat} (hb : 0 < b) (hc : c ≤ b) : a * c / b ≤ a := by
  have hmul : a * c ≤ a * b := Nat.mul_le_mul_left a hc
  have hdiv : a * c / b ≤ a * b / b := Nat.div_le_div_right hmul
  rwa [Nat.mul_div_cancel _ hb] at hdiv

theorem div_mul_le_self (a b : Nat) : a / b * b ≤ a :=
  Nat.div_mul_le_self a b

/-- Ceiling division `(p * k + (c - 1)) / c` does not exceed `p` when `k ≤ c`. -/
theorem mulDivUp_le {p k c : Nat} (hc : 0 < c) (hk : k ≤ c) :
    (p * k + (c - 1)) / c ≤ p := by
  have hmul : p * k ≤ p * c := Nat.mul_le_mul_left p hk
  have hsum : p * k + (c - 1) ≤ p * c + (c - 1) := Nat.add_le_add_right hmul _
  have hlt : p * c + (c - 1) < (p + 1) * c := by
    have hc1 : c - 1 < c := Nat.sub_lt hc (by decide)
    have : p * c + (c - 1) < p * c + c := Nat.add_lt_add_left hc1 _
    simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hall : p * k + (c - 1) < (p + 1) * c := lt_of_le_of_lt hsum hlt
  exact Nat.le_of_lt_succ (Nat.div_lt_iff_lt_mul hc |>.mpr (by simpa [Nat.succ_eq_add_one] using hall))

theorem xor_val {a b : Nat} (ha : a < Uint256.modulus) (hb : b < Uint256.modulus) :
    (Uint256.xor (Uint256.ofNat a) (Uint256.ofNat b)).val = a ^^^ b := by
  simp [Uint256.xor, Uint256.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)

theorem xor_cancel_left (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- `UtilsLib.min` via `xor(x, mul(xor(x, y), lt(y, x)))`. -/
theorem yul_min {x y : Nat} (hx : x < Uint256.modulus) (hy : y < Uint256.modulus) :
    (Uint256.xor (Uint256.ofNat x)
      ((Uint256.xor (Uint256.ofNat x) (Uint256.ofNat y)) *
        Uint256.ofNat (boolWord (decide (y < x))))).val =
      if y < x then y else x := by
  set xy : Uint256 := Uint256.xor (Uint256.ofNat x) (Uint256.ofNat y)
  have hxy : xy.val = x ^^^ y := xor_val hx hy
  by_cases hyx : y < x
  · have hd : decide (y < x) = true := decide_true_of hyx
    simp only [hd, boolWord_true]
    have hone : Uint256.ofNat 1 = (1 : Uint256) := rfl
    simp only [hone, Uint256.mul_one]
    rw [← ofNat_val xy]
    rw [xor_val hx (by
      simpa [Uint256.modulus, UINT256_MODULUS, hxy] using Nat.xor_lt_two_pow hx hy)]
    simp [hxy, xor_cancel_left, hyx]
  · have hd : decide (y < x) = false := decide_false_of_not hyx
    simp only [hd, boolWord_false]
    have hzero : Uint256.ofNat 0 = (0 : Uint256) := rfl
    simp only [hzero, Uint256.mul_zero]
    have hz : (Uint256.xor (Uint256.ofNat x) (0 : Uint256)).val = x := by
      rw [show (0 : Uint256) = Uint256.ofNat 0 by rfl, xor_val hx Uint256.modulus_pos, Nat.xor_zero]
    simp [hz, hyx]

theorem mask_of_le {a : Nat} (ha : a ≤ max128) :
    (Uint256.and (Uint256.ofNat a) (Uint256.ofNat max128)).val = a :=
  mask_eq ha

theorem postSlashCredit_le {credit lastLoss loss : Nat}
    (hm : loss ≤ max128) (hle : lastLoss ≤ loss) :
    (if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0) ≤ credit := by
  split
  · next hlt =>
      have hden : 0 < max128 - lastLoss := by omega
      have hnum : max128 - loss ≤ max128 - lastLoss := by omega
      exact mul_div_le_self hden hnum
  · exact Nat.zero_le _

theorem postSlashCredit_mul_le {credit lastLoss loss : Nat}
    (hl : lastLoss ≤ max128) (hm : loss ≤ max128) (hle : lastLoss ≤ loss) :
    (if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0) *
        (max128 - lastLoss) ≤
      credit * (max128 - loss) := by
  split
  · next hlt =>
      exact div_mul_le_self _ _
  · next hge =>
      have hloss : lastLoss = max128 := by omega
      have hmk : loss = max128 := by omega
      simp [hloss, hmk]

theorem postSlashPending_le (pending credit psc : Nat) :
    pending - (pending * (credit - psc) + (credit - 1)) / credit ≤ pending :=
  Nat.sub_le _ _

theorem postSlashPending_quot_le {credit pending : Nat} (hc : 0 < credit) (psc : Nat) :
    (pending * (credit - psc) + (credit - 1)) / credit ≤ pending :=
  mulDivUp_le hc (Nat.sub_le credit psc)

theorem accrued_le_pending {psp d1 d2 : Nat} (hd : 0 < d2) (hle : d1 ≤ d2) :
    psp * d1 / d2 ≤ psp :=
  mul_div_le_self hd hle

/-- The importer's overflow check `(a * b) / a = b` forces the product to fit in a word. -/
theorem mul_check_lt {a b : Nat} (_ha : a ≠ 0)
    (h : (a * b) % Uint256.modulus / a = b) :
    a * b < Uint256.modulus := by
  let w := (a * b) % Uint256.modulus
  have hwlt : w < Uint256.modulus := Nat.mod_lt _ Uint256.modulus_pos
  have hdecomp : a * (w / a) + w % a = w := Nat.div_add_mod w a
  have hdiv : w / a = b := by
    simpa [w] using h
  have hsum : a * b + w % a = w := by
    simpa [hdiv] using hdecomp
  have hwge : a * b ≤ w := by omega
  exact lt_of_le_of_lt hwge hwlt

end Midnight.Lemmas
