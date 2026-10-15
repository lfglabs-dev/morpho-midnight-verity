import Verity.Proofs.Stdlib.Int256
import Mathlib.Tactic

/-!
# Signed words (helpers for steps A and B)

The imported code computes on 256-bit words (`Nat`s below `2^256`). An `int256`
value `z` is stored as the word `enc z = z mod 2^256`. This file turns each
word operation the imported `wExp` uses into the integer operation it computes,
as long as the operands and the result are representable:

| word operation | integer operation      | lemma      |
| -------------- | ---------------------- | ---------- |
| `addW`         | `+`                    | `addW_enc` |
| `subW`         | `-`                    | `subW_enc` |
| `mulW`         | `*`                    | `mulW_enc` |
| `sdivW`        | `Int.tdiv`             | `sdivW_enc`|
| `sltW`         | `<`                    | `sltW_enc` |
| `shlW`         | `* 2^q`, then mod 2^256| `shlW_enc` |

`addW`, `subW`, `mulW` wrap, so they need no range condition.
-/

open Verity.Core

namespace TickLib.Proof.Signed

/-! ## The word operations of the imported model's `evalExpr` -/

def addW (a b : Nat) : Nat := (Uint256.ofNat a + Uint256.ofNat b).val
def subW (a b : Nat) : Nat := (Uint256.ofNat a - Uint256.ofNat b).val
def mulW (a b : Nat) : Nat := (Uint256.ofNat a * Uint256.ofNat b).val
def divW (a b : Nat) : Nat := (Uint256.ofNat a / Uint256.ofNat b).val
def sdivW (a b : Nat) : Nat :=
  (Int256.div (Int256.ofUint256 (Uint256.ofNat a)) (Int256.ofUint256 (Uint256.ofNat b))).toUint256.val
def sltW (a b : Nat) : Bool :=
  decide ((Int256.ofUint256 (Uint256.ofNat a) : Int) < (Int256.ofUint256 (Uint256.ofNat b) : Int))
def shlW (s v : Nat) : Nat := (Uint256.shl (Uint256.ofNat s) (Uint256.ofNat v)).val

/-! ## Two's-complement encoding -/

/-- `2^256` as an integer. -/
def M : Int := 2 ^ 256

/-- The word storing the `int256` value `z`. -/
def enc (z : Int) : Nat := (z % M).toNat

/-- `z` is a representable `int256`. -/
def InR (z : Int) : Prop := -2 ^ 255 ≤ z ∧ z < 2 ^ 255

theorem M_pos : (0 : Int) < M := by unfold M; positivity

theorem hM : (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) = M := by
  unfold M; norm_num

theorem hMn : Uint256.modulus = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  unfold Uint256.modulus UINT256_MODULUS; norm_num

theorem enc_cast (z : Int) : ((enc z : Nat) : Int) = z % M := by
  unfold enc; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt M_pos))

theorem enc_lt (z : Int) : enc z < 2 ^ 256 := by
  have h := enc_cast z
  have : z % M < M := Int.emod_lt_of_pos _ M_pos
  have : ((enc z : Nat) : Int) < ((2 ^ 256 : Nat) : Int) := by rw [h]; unfold M at *; push_cast; omega
  exact_mod_cast this

theorem ofNat_enc (z : Int) : (Uint256.ofNat (enc z)).val = enc z := Nat.mod_eq_of_lt (enc_lt z)

theorem enc_eq_of_cast {n : Nat} {z : Int} (h : (n : Int) = z % M) : n = enc z := by
  have : (n : Int) = (enc z : Int) := by rw [h, enc_cast]
  exact_mod_cast this

/-- A non-negative value below `2^256` is its own word. -/
theorem enc_of_nonneg {z : Int} (h0 : 0 ≤ z) (h1 : z < M) : enc z = z.toNat := by
  unfold enc; rw [Int.emod_eq_of_lt h0 h1]

theorem enc_natCast {n : Nat} (h : n < 2 ^ 256) : enc (n : Int) = n := by
  rw [enc_of_nonneg (by positivity) (by unfold M; exact_mod_cast h)]; simp

/-! ## Arithmetic -/

theorem addW_enc (a b : Int) : addW (enc a) (enc b) = enc (a + b) := by
  show (Uint256.add _ _).val = _
  simp only [Uint256.add, ofNat_enc]
  simp only [Uint256.ofNat, hMn]
  apply enc_eq_of_cast
  push_cast [enc_cast, hM]
  rw [← Int.add_emod]

theorem mulW_enc (a b : Int) : mulW (enc a) (enc b) = enc (a * b) := by
  show (Uint256.mul _ _).val = _
  simp only [Uint256.mul, ofNat_enc]
  simp only [Uint256.ofNat, hMn]
  apply enc_eq_of_cast
  push_cast [enc_cast, hM]
  rw [← Int.mul_emod]

theorem subW_enc (a b : Int) : subW (enc a) (enc b) = enc (a - b) := by
  show (Uint256.sub _ _).val = _
  simp only [Uint256.sub, ofNat_enc]
  apply enc_eq_of_cast
  have ha := enc_cast a
  have hb := enc_cast b
  have hal := enc_lt a
  have hbl := enc_lt b
  split
  · rename_i h
    show (((enc a - enc b) % Uint256.modulus : Nat) : Int) = _
    rw [hMn]; push_cast [Nat.cast_sub h, ha, hb, hM]
    rw [← Int.sub_emod]
  · rename_i h
    show ((((Uint256.modulus - (enc b - enc a)) % Uint256.modulus : Nat)) : Int) = _
    rw [hMn]
    have h' : enc b - enc a ≤
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by omega
    push_cast [Nat.cast_sub h', Nat.cast_sub (le_of_lt (not_le.mp h)), ha, hb, hM]
    rw [show M - (b % M - a % M) = (a % M - b % M) + M by ring, Int.add_emod_right, ← Int.sub_emod]

/-! ## Signed views -/

theorem toInt_enc {a : Int} (h : InR a) : (Int256.ofUint256 (Uint256.ofNat (enc a)) : Int) = a := by
  have hc := enc_cast a
  show Int256.toInt _ = a
  simp only [Int256.toInt, Int256.ofUint256, Int256.signBit, Int256.modulus, Uint256.modulus,
    UINT256_MODULUS, ofNat_enc]
  unfold InR M at *
  split
  · rename_i hlt
    have : ((enc a : Nat) : Int) < 2 ^ 255 := by exact_mod_cast hlt
    simp only [Int.ofNat_eq_natCast]; omega
  · rename_i hlt
    have : (2 ^ 255 : Int) ≤ ((enc a : Nat) : Int) := by exact_mod_cast (not_lt.mp hlt)
    simp only [Int.ofNat_eq_natCast]; push_cast; omega

/-- The word of an `int256` is the encoding of its value. -/
theorem word_eq_enc (v : Int256) : v.toUint256.val = enc (v : Int) := by
  apply enc_eq_of_cast
  have := Verity.Proofs.Stdlib.Int256.toInt_emod v
  rw [show ((Int256.modulus : Nat) : Int) = M by
    unfold Int256.modulus; rw [hMn]; exact hM] at this
  rw [this]; rfl

theorem inR_toInt (v : Int256) : InR (v : Int) := by
  have := Int256.toInt_in_range v
  unfold InR
  simp only [Int256.minValue, Int256.maxValue, Int256.signBit] at this
  push_cast at this
  omega

theorem ofInt_word (z : Int) : (Int256.ofInt z).toUint256.val = enc z := by
  apply enc_eq_of_cast
  unfold Int256.ofInt
  split
  · rename_i hz
    simp only [Int256.toUint256_ofUint256, Uint256.ofNat, Int256.modulus, hMn]
    have hlt : z.natAbs % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
      Nat.mod_lt _ (by norm_num)
    push_cast [Nat.cast_sub (le_of_lt hlt)]
    rw [hM]
    rw [abs_of_neg hz]
    have : M - -z % M = z + M * (1 + (-z) / M) := by rw [Int.emod_def]; ring
    rw [this, Int.add_mul_emod_self_left]
  · rename_i hz
    simp only [Int256.toUint256_ofUint256, Uint256.ofNat, hMn]
    push_cast [Int.toNat_of_nonneg (not_lt.mp hz)]
    rw [hM]

theorem sltW_enc {a b : Int} (ha : InR a) (hb : InR b) : sltW (enc a) (enc b) = decide (a < b) := by
  unfold sltW; rw [toInt_enc ha, toInt_enc hb]

theorem sdivW_enc {a b : Int} (ha : InR a) (hb : InR b) (hb0 : 0 < b) :
    sdivW (enc a) (enc b) = enc (Int.tdiv a b) := by
  unfold sdivW
  rw [Verity.Proofs.Stdlib.Int256.div_eq_ofInt_tdiv _ _ (by rw [toInt_enc hb]; omega),
    toInt_enc ha, toInt_enc hb, ofInt_word]

theorem shlW_enc {q v : Int} (hq0 : 0 ≤ q) (hq : q < M) (hv0 : 0 ≤ v) (hv : v < M) :
    shlW (enc q) (enc v) = (v.toNat * 2 ^ q.toNat) % 2 ^ 256 := by
  unfold shlW Uint256.shl
  rw [ofNat_enc, ofNat_enc, enc_of_nonneg hq0 hq, enc_of_nonneg hv0 hv, Nat.shiftLeft_eq]
  simp only [Uint256.ofNat, hMn]
  norm_num

/-! ## Unsigned words without wrapping -/

theorem addW_nat {a b : Nat} (h : a + b < 2 ^ 256) : addW a b = a + b := by
  have := addW_enc (a : Int) (b : Int)
  rw [enc_natCast (by omega), enc_natCast (by omega), ← Nat.cast_add, enc_natCast h] at this
  exact this

theorem subW_nat {a b : Nat} (ha : a < 2 ^ 256) (h : b ≤ a) : subW a b = a - b := by
  have := subW_enc (a : Int) (b : Int)
  rw [enc_natCast ha, enc_natCast (by omega), ← Nat.cast_sub h, enc_natCast (by omega)] at this
  exact this

theorem mulW_nat {a b : Nat} (h : a * b < 2 ^ 256) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    mulW a b = a * b := by
  have := mulW_enc (a : Int) (b : Int)
  rw [enc_natCast ha, enc_natCast hb, ← Nat.cast_mul, enc_natCast h] at this
  exact this

theorem divW_nat {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) : divW a b = a / b := by
  show (Uint256.div _ _).val = _
  have hva : (Uint256.ofNat a).val = a := Nat.mod_eq_of_lt (by rw [hMn]; norm_num at ha ⊢; exact ha)
  have hvb : (Uint256.ofNat b).val = b := Nat.mod_eq_of_lt (by rw [hMn]; norm_num at hb ⊢; exact hb)
  unfold Uint256.div
  rw [hva, hvb]
  split
  · rename_i h; subst h; simp [Uint256.ofNat]
  · show (a / b) % Uint256.modulus = a / b
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hMn]; norm_num at ha ⊢; exact ha))

theorem divW_lt (a b : Nat) : divW a b < 2 ^ 256 := (Uint256.ofNat a / Uint256.ofNat b).isLt

theorem mulW_lt (a b : Nat) : mulW a b < 2 ^ 256 := (Uint256.ofNat a * Uint256.ofNat b).isLt

end TickLib.Proof.Signed
