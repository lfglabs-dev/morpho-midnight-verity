import TickLib.Spec
import TickLib.Proof.Execution
import TickLib.Proof.Math

/-!
# Step B: the word functions compute the integer functions

`Execution.lean` shows that the imported calls return `wExpW x` and `tickW tick`,
functions on 256-bit words. `Math.lean` proves monotonicity for `wExpVal` and
`priceOf`, the same formulas on unbounded integers. This file connects the two on
the inputs the rules talk about:

1. `wCore_enc`: on `0 ≤ x ≤ 2^200`, the positive branch computes `expPos x mod 2^256`.
   Each signed operation of `Signed.lean` applies because every intermediate
   value is far from `±2^255`.
2. `wExpW_val`: on `[-X*, X*]`, `wExpW x = wExpVal x`. The sign-flip guard of the
   inlined `wExp(-x)` never fires, and `expPos (-x) ≥ 1e18` so `1e36 / ..` does
   not divide by zero.
3. `tickW_val`: for `tick ≤ 6744`, `tickW tick = priceOf (wExpVal (LN * (3372 - tick)))`.
   `|LN * (3372 - tick)| ≤ maxInput < X*`, and no word overflows.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote Compiler.CompilationModel.SolidityImport
open Verity.Core TickLib.Proof.Signed TickLib.Proof.Execution TickLib.Proof.Math
namespace TickLib.Proof.Bridge

/-! ## 1. The positive branch -/

theorem eO : (322611214989459870 : Nat) = enc 322611214989459870 := by decide
theorem eL : (693147180559945309 : Nat) = enc 693147180559945309 := by decide
theorem e2 : (2000000000000000000 : Nat) = enc 2000000000000000000 := by decide
theorem e3 : (3000000000000000000 : Nat) = enc 3000000000000000000 := by decide
theorem e1 : (1000000000000000000 : Nat) = enc 1000000000000000000 := by decide

theorem inR_of {z : Int} (a b : Int) (ha : a ≤ z) (hb : z ≤ b) (h1 : -2^255 ≤ a := by norm_num)
    (h2 : b < 2^255 := by norm_num) : InR z := ⟨le_trans h1 ha, lt_of_le_of_lt hb h2⟩

theorem wCore_enc {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 2 ^ 200) :
    wCore (enc x) = expPos x % 2 ^ 256 := by
  have hq0 := q_nonneg h0
  have hqle : q x ≤ x + 322611214989459870 := by
    unfold q; rw [Int.tdiv_eq_ediv_of_nonneg (by linarith)]
    exact Int.ediv_le_self _ (by linarith)
  have hlo := rem_lo h0
  have hhi := rem_hi h0
  have hrr0 : 0 ≤ rem x * rem x := mul_self_nonneg _
  have hrr1 : rem x * rem x ≤ 10 ^ 36 := by nlinarith
  have hs0 : 0 ≤ secondTerm (rem x) := by
    unfold secondTerm; rw [Int.tdiv_eq_ediv_of_nonneg hrr0]; exact Int.ediv_nonneg hrr0 (by norm_num)
  have hs1 : secondTerm (rem x) ≤ 10 ^ 36 := by
    unfold secondTerm; rw [Int.tdiv_eq_ediv_of_nonneg hrr0]
    exact le_trans (Int.ediv_le_self _ hrr0) hrr1
  have hsr0 : -10 ^ 54 ≤ secondTerm (rem x) * rem x := by nlinarith
  have hsr1 : secondTerm (rem x) * rem x ≤ 10 ^ 54 := by nlinarith
  have he0 := expR_rem_ge h0
  have he1 : expR (rem x) ≤ 2 * 723831661569835069 := by
    have := expR_mono (le_trans (by norm_num) hlo) hhi
    rw [segment_jump, expR_bottom] at this; exact this
  unfold wCore
  simp only
  rw [eO, eL, e2, e3, e1, addW_enc,
    sdivW_enc (inR_of 0 (2 ^ 201) (by linarith) (by linarith)) (inR_of 1 (2^60) (by norm_num) (by norm_num))
      (by norm_num),
    mulW_enc, subW_enc]
  rw [show (x + 322611214989459870).tdiv 693147180559945309 = q x from rfl,
    show x - q x * 693147180559945309 = rem x from rfl, mulW_enc,
    sdivW_enc (inR_of 0 (10^36) hrr0 hrr1) (inR_of 1 (2^62) (by norm_num) (by norm_num)) (by norm_num),
    show (rem x * rem x).tdiv 2000000000000000000 = secondTerm (rem x) from rfl, mulW_enc,
    sdivW_enc (inR_of (-10^54) (10^54) hsr0 hsr1) (inR_of 1 (2^62) (by norm_num) (by norm_num)) (by norm_num),
    show (secondTerm (rem x) * rem x).tdiv 3000000000000000000 = thirdTerm (rem x) from rfl,
    addW_enc, addW_enc, addW_enc,
    show 1000000000000000000 + rem x + secondTerm (rem x) + thirdTerm (rem x) = expR (rem x) from rfl,
    shlW_enc hq0 (by unfold M; linarith) (by linarith) (by unfold M; linarith)]
  rfl


/-! ## 2. `wExp` -/

theorem expPos_bound {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ XSTAR) : expPos x % 2 ^ 256 = expPos x :=
  Nat.mod_eq_of_lt (expPos_lt h0 h1)

theorem wExpW_val {x : Int} (h0 : -XSTAR ≤ x) (h1 : x ≤ XSTAR) : wExpW (enc x) = some (wExpVal x) := by
  have hX : XSTAR ≤ 2 ^ 200 := by unfold XSTAR; norm_num
  have hXR : InR x := inR_of (-XSTAR) XSTAR h0 h1 (by unfold XSTAR; norm_num) (by unfold XSTAR; norm_num)
  have h00 : (0 : Nat) = enc 0 := by decide
  unfold wExpW wExpVal
  rw [h00, sltW_enc hXR (inR_of 0 0 le_rfl le_rfl)]
  by_cases hneg : x < 0
  · have hnR : InR (0 - x) := inR_of 0 XSTAR (by linarith) (by linarith) (by norm_num) (by unfold XSTAR; norm_num)
    rw [decide_eq_true hneg, if_pos rfl, subW_enc, sltW_enc hnR (inR_of 0 0 le_rfl le_rfl),
      decide_eq_false (by linarith), if_neg (by simp), wCore_enc (by linarith) (by linarith),
      if_pos hneg, show (0 : Int) - x = -x by ring, expPos_bound (by linarith) (by linarith)]
    have hpos := expPos_ge (x := -x) (by linarith)
    rw [if_neg (by omega), divW_nat (by norm_num) (expPos_lt (by linarith) (by linarith))]
  · rw [decide_eq_false hneg, if_neg (by simp), wCore_enc (by linarith) (by linarith), if_neg hneg,
      expPos_bound (by linarith) h1]

theorem ofNat_mod (v : Nat) : (Word.ofWord (v % 2 ^ 256) : Uint256) = Uint256.ofNat v := by
  apply Uint256.ext
  show (v % 2 ^ 256) % Uint256.modulus = v % Uint256.modulus
  rw [hMn]; norm_num

/-- The imported `wExp` on `x : Int256`. -/
theorem wExp_call (o : DenoteOracle) (w : Verity.ContractState) (x : Int256) :
    tickLib.wExp o w x = (wExpW (enc (x : Int))).map Uint256.ofNat := by
  unfold tickLib.wExp
  rw [toWord_int256, word_eq_enc, run_wExp]
  cases wExpW (enc (x : Int)) with
  | none => rfl
  | some v => exact congrArg some (ofNat_mod v)

/-! ## 3. `tickToPrice` -/

/-- `x = LN_ONE_PLUS_DELTA * (MAX_TICK / 2 - tick)` as an integer. -/
def tickInput (tick : Nat) : Int := 4987541511039073 * (3372 - (tick : Int))

theorem tickInput_enc {tick : Nat} (h : tick ≤ 6744) :
    mulW 4987541511039073 (subW (divW 6744 2) tick) = enc (tickInput tick) := by
  have ht : tick = enc (tick : Int) := (enc_natCast (by omega)).symm
  have hs : subW (enc 3372) tick = enc (3372 - (tick : Int)) := by
    conv_lhs => rw [ht]
    exact subW_enc _ _
  rw [divW_nat (by norm_num) (by norm_num), show (6744 / 2 : Nat) = enc 3372 by decide, hs,
    show (4987541511039073 : Nat) = enc 4987541511039073 by decide, mulW_enc]
  rfl

theorem tickInput_range {tick : Nat} (h : tick ≤ 6744) :
    -XSTAR ≤ tickInput tick ∧ tickInput tick ≤ XSTAR := by
  unfold tickInput XSTAR; constructor <;> omega

theorem tailW_val (W : Nat) (hW : W ≤ 2 ^ 200) : tailW W = some (priceOf W) := by
  set d := 1000000000000000000 + W with hd_def
  have hd : d < 2 ^ 256 := by omega
  have h1 : addW 1000000000000000000 W = d := addW_nat hd
  have h2 : divW (subW d 1) 2 = (d - 1) / 2 := by
    rw [subW_nat hd (by omega), divW_nat (by omega) (by norm_num)]
  have h3 : addW 1000000000000000000000000000000000000 ((d - 1) / 2) =
      1000000000000000000000000000000000000 + (d - 1) / 2 := addW_nat (by omega)
  set A := (1000000000000000000000000000000000000 + (d - 1) / 2) / d with hA_def
  have hA : A ≤ 1000000000000000000 :=
    Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
  have h4 : divW (1000000000000000000000000000000000000 + (d - 1) / 2) d = A :=
    divW_nat (by omega) hd
  have h5 : divW (subW 100000000000 1) 2 = (100000000000 - 1) / 2 := by
    rw [subW_nat (by norm_num) (by norm_num), divW_nat (by norm_num) (by norm_num)]
  have h6 : addW A ((100000000000 - 1) / 2) = A + (100000000000 - 1) / 2 := addW_nat (by omega)
  have h7 : divW (A + (100000000000 - 1) / 2) 100000000000 = (A + (100000000000 - 1) / 2) / 100000000000 :=
    divW_nat (by omega) (by norm_num)
  have hB : (A + (100000000000 - 1) / 2) / 100000000000 ≤ A + 1 := by omega
  have h8 : mulW ((A + (100000000000 - 1) / 2) / 100000000000) 100000000000 =
      (A + (100000000000 - 1) / 2) / 100000000000 * 100000000000 :=
    mulW_nat (by omega) (by omega) (by norm_num)
  unfold tailW
  simp only
  rw [h1, if_neg (by omega), h2, h3, h4, h5, h6, h7, h8]
  rfl

/-- `maxOutputIsWExpOfMaxInput`, on the integer function. -/
theorem wExpVal_maxInput : wExpVal 16817989975223754156 = 20134595243400876315901952 := by
  unfold wExpVal; rw [if_neg (by norm_num)]; decide

theorem wExpVal_tick_le {tick : Nat} (h : tick ≤ 6744) :
    wExpVal (tickInput tick) ≤ 20134595243400876315901952 := by
  rw [← wExpVal_maxInput]
  exact wExpVal_mono (by unfold tickInput; omega)

theorem tickW_val {tick : Nat} (h : tick ≤ 6744) :
    tickW tick = some (priceOf (wExpVal (tickInput tick))) := by
  obtain ⟨h0, h1⟩ := tickInput_range h
  rw [tickW_eq tick h, tickInput_enc h, wExpW_val h0 h1, Option.bind_some, tailW_val _ (le_trans (wExpVal_tick_le h) (by norm_num))]

/-- The imported `tickToPrice` on `tick : Uint256`. -/
theorem tickToPrice_call (o : DenoteOracle) (w : Verity.ContractState) (tick : Uint256) :
    tickLib.tickToPrice o w tick = (tickW tick.val).map Uint256.ofNat := by
  unfold tickLib.tickToPrice
  rw [toWord_uint256, run_tickToPrice]
  cases tickW tick.val with
  | none => rfl
  | some v => exact congrArg some (ofNat_mod v)

/-! ## 4. The rules -/

theorem ofNat_val_of_lt {v : Nat} (h : v < 2 ^ 256) : (Uint256.ofNat v).val = v := by
  show v % Uint256.modulus = v
  rw [hMn]; exact Nat.mod_eq_of_lt (by norm_num at h ⊢; exact h)

theorem wExpVal_lt {x : Int} (_h0 : -XSTAR ≤ x) (h1 : x ≤ XSTAR) : wExpVal x < 2 ^ 256 := by
  by_cases hx : x < 0
  · exact lt_of_le_of_lt (wExpVal_nonneg_le hx) (by norm_num)
  · unfold wExpVal; rw [if_neg hx]; exact expPos_lt (by linarith) h1

theorem toInt_ofInt' {z : Int} (h0 : -XSTAR - 1 ≤ z) (h1 : z ≤ XSTAR + 1) : (Int256.ofInt z : Int) = z := by
  apply Verity.Proofs.Stdlib.Int256.toInt_ofInt
  unfold Int256.inRange Int256.minValue Int256.maxValue Int256.signBit
  unfold XSTAR at h0 h1
  constructor <;> push_cast <;> omega

theorem wExp_val (o : DenoteOracle) (w : Verity.ContractState) (x : Int256)
    (h0 : -XSTAR ≤ (x : Int)) (h1 : (x : Int) ≤ XSTAR) :
    tickLib.wExp o w x = some (Uint256.ofNat (wExpVal x)) := by
  rw [wExp_call, wExpW_val h0 h1]; rfl

/-! ## Helpers for the final theorems -/

theorem xstar_eq : Spec.XSTAR = XSTAR := rfl

theorem price_val (tick : Nat) : (Uint256.ofNat (priceOf (wExpVal (tickInput tick)))).val =
    priceOf (wExpVal (tickInput tick)) :=
  ofNat_val_of_lt (lt_of_le_of_lt (priceOf_le_wad _) (by norm_num))

/-- A successful `tickToPrice` returns `priceOf (wExpVal (tickInput tick))`. -/
theorem tickToPrice_some {o : DenoteOracle} {w : Verity.ContractState} {tick price : Uint256}
    (h : tickLib.tickToPrice o w tick = some price) :
    tick.val ≤ 6744 ∧ price.val = priceOf (wExpVal (tickInput tick.val)) := by
  rw [tickToPrice_call] at h
  by_cases ht : tick.val ≤ 6744
  · rw [tickW_val ht] at h
    cases h
    exact ⟨ht, price_val _⟩
  · unfold tickW at h; rw [if_neg ht] at h; cases h

end TickLib.Proof.Bridge
