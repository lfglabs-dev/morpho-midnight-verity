import Mathlib.Tactic

/-!
# Step C: why `wExp` and `tickToPrice` are monotone

Integer versions of what `TickLib.sol` computes, and why they are monotone.
`Execution.lean` and `Bridge.lean` show that the imported code computes exactly
these values on the ranges the rules use.

For `x ≥ 0`, `wExp(x) = expR(r) << q` with

    q = (x + offset) / ln2,   r = x - q * ln2 ∈ [-offset, ln2 - offset),
    expR(r) = 1e18 + r + secondTerm(r) + thirdTerm(r),
    secondTerm(r) = r * r / 2e18,   thirdTerm(r) = secondTerm(r) * r / 3e18

(`/` truncates toward zero, as Solidity's `sdiv`). For `x < 0`,
`wExp(x) = 1e36 / wExp(-x)`.

1. **Within a segment** (`expR_mono`): `expR` is non-decreasing on `[-1e18, ∞)`.
   For `r ≥ 0` every term grows. For `r < 0`, one step `r → r+1` adds `1`,
   lowers `secondTerm` by at most `1`, and moves `thirdTerm` toward `0`.
2. **Across segments** (`segment_jump`): `expR(ln2 - offset - 1) = 2 * expR(-offset)`,
   so the largest value of segment `q` is the smallest value of segment `q+1`.
3. **Positive inputs** (`expPos_mono`): `expR(r) * 2^q` is non-decreasing for
   `x ≥ 0`. It stays below `2^256` exactly up to `X* = 135999161806159974428`
   (`expPos_lt`, `expPos_overflow`), so the shift does not truncate.
4. **Negative inputs** (`wExpVal_mono`): `1e36 / expPos(-x)` is non-decreasing in
   `x` since `expPos` is, and `wExp(0) = 1e18` bridges the sign change.
5. **Prices** (`roundHalfDown_anti`, `roundStep_mono`): rounding `1e36 / d` to the
   nearest integer (ties down) is non-increasing in `d`; rounding to a multiple
   of `1e11` is non-decreasing.
-/

namespace TickLib.Proof.Math

/-! ## Definitions -/

def secondTerm (r : Int) : Int := Int.tdiv (r * r) 2000000000000000000
def thirdTerm (r : Int) : Int := Int.tdiv (secondTerm r * r) 3000000000000000000
def expR (r : Int) : Int := 1000000000000000000 + r + secondTerm r + thirdTerm r

/-- `int256 q = (x + offset) / ln2;` -/
def q (x : Int) : Int := Int.tdiv (x + 322611214989459870) 693147180559945309
/-- `int256 r = x - q * ln2;` -/
def rem (x : Int) : Int := x - q x * 693147180559945309

/-- `uint256(expR) << uint256(q)` before truncation to 256 bits, for `x ≥ 0`. -/
def expPos (x : Int) : Nat := (expR (rem x)).toNat * 2 ^ (q x).toNat

/-- `wExp(x)` on `[-X*, X*]`, where no truncation happens. -/
def wExpVal (x : Int) : Nat := if x < 0 then 1000000000000000000000000000000000000 / expPos (-x) else expPos x

/-- The largest input on which `wExp` does not overflow: `X* = 135999161806159974428`. -/
def XSTAR : Int := 135999161806159974428

/-- `divHalfDownUnchecked(a, d) = (a + (d - 1) / 2) / d`. -/
def roundHalfDown (a d : Nat) : Nat := (a + (d - 1) / 2) / d

/-- `x.divHalfDownUnchecked(1e11) * 1e11`. -/
def roundStep (v : Nat) : Nat := roundHalfDown v 100000000000 * 100000000000

/-- `tickToPrice` from `W = wExp(LN_ONE_PLUS_DELTA * (3372 - tick))`. -/
def priceOf (W : Nat) : Nat :=
  roundStep (roundHalfDown 1000000000000000000000000000000000000 (1000000000000000000 + W))

/-! ## 1. Within a segment -/

theorem expR_step (r : Int) (hr : -1000000000000000000 ≤ r) : expR r ≤ expR (r + 1) := by
  unfold expR thirdTerm secondTerm
  rcases le_or_gt 0 r with h | h
  · have h1 : 0 ≤ r * r := by positivity
    have h2 : 0 ≤ (r + 1) * (r + 1) := by positivity
    rw [Int.tdiv_eq_ediv_of_nonneg h1, Int.tdiv_eq_ediv_of_nonneg h2]
    have hs : r * r / 2000000000000000000 ≤ (r + 1) * (r + 1) / 2000000000000000000 :=
      Int.ediv_le_ediv (by norm_num) (by nlinarith)
    have hs0 : 0 ≤ r * r / 2000000000000000000 := Int.ediv_nonneg h1 (by norm_num)
    have hp1 : 0 ≤ r * r / 2000000000000000000 * r := mul_nonneg hs0 h
    have hp2 : 0 ≤ (r + 1) * (r + 1) / 2000000000000000000 * (r + 1) :=
      mul_nonneg (le_trans hs0 hs) (by linarith)
    rw [Int.tdiv_eq_ediv_of_nonneg hp1, Int.tdiv_eq_ediv_of_nonneg hp2]
    have : r * r / 2000000000000000000 * r / 3000000000000000000 ≤
        (r + 1) * (r + 1) / 2000000000000000000 * (r + 1) / 3000000000000000000 :=
      Int.ediv_le_ediv (by norm_num) (mul_le_mul hs (by linarith) h (le_trans hs0 hs))
    linarith
  · have h1 : 0 ≤ r * r := by nlinarith
    have h2 : 0 ≤ (r + 1) * (r + 1) := by nlinarith
    rw [Int.tdiv_eq_ediv_of_nonneg h1, Int.tdiv_eq_ediv_of_nonneg h2]
    set s := r * r / 2000000000000000000 with hs_def
    set s' := (r + 1) * (r + 1) / 2000000000000000000 with hs'_def
    have hs0 : 0 ≤ s' := Int.ediv_nonneg h2 (by norm_num)
    have hss' : s' ≤ s := Int.ediv_le_ediv (by norm_num) (by nlinarith)
    have hs'1 : s ≤ s' + 1 := by
      have : r * r ≤ (r + 1) * (r + 1) + 1 * 2000000000000000000 := by nlinarith
      have := Int.ediv_le_ediv (c := 2000000000000000000) (by norm_num) this
      rwa [Int.add_mul_ediv_right _ _ (by norm_num)] at this
    have e1 : s * r = -(s * -r) := by ring
    have e2 : s' * (r + 1) = -(s' * -(r + 1)) := by ring
    rw [e1, e2, Int.neg_tdiv, Int.neg_tdiv,
      Int.tdiv_eq_ediv_of_nonneg (mul_nonneg (le_trans hs0 hss') (by linarith)),
      Int.tdiv_eq_ediv_of_nonneg (mul_nonneg hs0 (by linarith))]
    have : s' * -(r + 1) / 3000000000000000000 ≤ s * -r / 3000000000000000000 :=
      Int.ediv_le_ediv (by norm_num) (mul_le_mul hss' (by linarith) (by linarith) (le_trans hs0 hss'))
    linarith

/-- `expR` is non-decreasing on `[-1e18, ∞)`, which contains every remainder `r`. -/
theorem expR_mono {r r' : Int} (hr : -1000000000000000000 ≤ r) (h : r ≤ r') : expR r ≤ expR r' := by
  induction r', h using Int.leInduction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans ih (expR_step n (le_trans hr hn))

/-! ## 2. Across segments -/

theorem q_nonneg {x : Int} (hx : 0 ≤ x) : 0 ≤ q x := by
  unfold q; rw [Int.tdiv_eq_ediv_of_nonneg (by linarith)]; exact Int.ediv_nonneg (by linarith) (by norm_num)

theorem rem_eq {x : Int} (hx : 0 ≤ x) :
    rem x = (x + 322611214989459870) % 693147180559945309 - 322611214989459870 := by
  unfold rem q; rw [Int.tdiv_eq_ediv_of_nonneg (by linarith), Int.emod_def]; ring

theorem rem_lo {x : Int} (hx : 0 ≤ x) : -322611214989459870 ≤ rem x := by
  rw [rem_eq hx]; have := Int.emod_nonneg (x + 322611214989459870) (b := 693147180559945309) (by norm_num)
  linarith

theorem rem_hi {x : Int} (hx : 0 ≤ x) : rem x ≤ 693147180559945309 - 322611214989459870 - 1 := by
  rw [rem_eq hx]; have := Int.emod_lt_of_pos (x + 322611214989459870) (b := 693147180559945309) (by norm_num)
  linarith

theorem q_mono {x y : Int} (hx : 0 ≤ x) (h : x ≤ y) : q x ≤ q y := by
  unfold q
  rw [Int.tdiv_eq_ediv_of_nonneg (by linarith), Int.tdiv_eq_ediv_of_nonneg (by linarith)]
  exact Int.ediv_le_ediv (by norm_num) (by linarith)

/-- `offset` makes the top of a segment exactly twice its bottom. -/
theorem segment_jump : expR (693147180559945309 - 322611214989459870 - 1) =
    2 * expR (-322611214989459870) := by decide

theorem expR_bottom : expR (-322611214989459870) = 723831661569835069 := by decide

theorem expR_rem_ge {x : Int} (hx : 0 ≤ x) : 723831661569835069 ≤ expR (rem x) := by
  rw [← expR_bottom]; exact expR_mono (by norm_num) (rem_lo hx)

/-! ## 3. Positive inputs -/

/-- `expR(r) * 2^q` is non-decreasing on `x ≥ 0`. -/
theorem expPos_mono {x y : Int} (hx : 0 ≤ x) (h : x ≤ y) : expPos x ≤ expPos y := by
  have hy : 0 ≤ y := le_trans hx h
  unfold expPos
  rcases (q_mono hx h).lt_or_eq with hq | hq
  · -- `q` jumps: max of segment `q x` ≤ min of segment `q x + 1` ≤ min of segment `q y`.
    have ha : (expR (rem x)).toNat ≤ 2 * 723831661569835069 := by
      have h2 := expR_mono (le_trans (by norm_num) (rem_lo hx)) (rem_hi hx)
      rw [segment_jump, expR_bottom] at h2
      omega
    have hb : 723831661569835069 ≤ (expR (rem y)).toNat := by have := expR_rem_ge hy; omega
    have hp : 2 ^ ((q x).toNat + 1) ≤ 2 ^ (q y).toNat :=
      Nat.pow_le_pow_right (by norm_num) (by have := q_nonneg hx; omega)
    calc (expR (rem x)).toNat * 2 ^ (q x).toNat
        ≤ 2 * 723831661569835069 * 2 ^ (q x).toNat := Nat.mul_le_mul_right _ ha
      _ = 723831661569835069 * 2 ^ ((q x).toNat + 1) := by rw [pow_succ]; ring
      _ ≤ 723831661569835069 * 2 ^ (q y).toNat := Nat.mul_le_mul_left _ hp
      _ ≤ (expR (rem y)).toNat * 2 ^ (q y).toNat := Nat.mul_le_mul_right _ hb
  · -- same segment: `r` grows by `y - x`.
    have hr : rem x ≤ rem y := by unfold rem; rw [hq]; linarith
    rw [hq]
    apply Nat.mul_le_mul_right
    exact Int.toNat_le_toNat (expR_mono (by have := rem_lo hx; linarith) hr)

theorem expPos_zero : expPos 0 = 1000000000000000000 := by decide

theorem expPos_ge {x : Int} (hx : 0 ≤ x) : 1000000000000000000 ≤ expPos x := by
  rw [← expPos_zero]; exact expPos_mono (le_refl _) hx

/-- No truncation up to `X*`. -/
theorem expPos_lt {x : Int} (hx : 0 ≤ x) (h : x ≤ XSTAR) : expPos x < 2 ^ 256 :=
  lt_of_le_of_lt (expPos_mono hx h) (by decide)

/-- At `X* + 1` the shift drops every bit: the truncated result is `0`. -/
theorem expPos_overflow : expPos (XSTAR + 1) % 2 ^ 256 = 0 := by decide

/-! ## 4. Negative inputs -/

theorem wExpVal_nonneg_le {x : Int} (h0 : x < 0) : wExpVal x ≤ 1000000000000000000 := by
  unfold wExpVal; rw [if_pos h0]
  apply Nat.div_le_of_le_mul
  have := expPos_ge (x := -x) (by linarith)
  nlinarith

/-- `wExp` is non-decreasing on `[-X*, X*]`. -/
theorem wExpVal_mono {x y : Int} (h : x ≤ y) : wExpVal x ≤ wExpVal y := by
  rcases lt_or_ge y 0 with hy | hy
  · have hx : x < 0 := lt_of_le_of_lt h hy
    unfold wExpVal; rw [if_pos hx, if_pos hy]
    exact Nat.div_le_div_left (expPos_mono (by linarith) (by linarith))
      (lt_of_lt_of_le (by norm_num) (expPos_ge (by linarith)))
  · rcases lt_or_ge x 0 with hx | hx
    · have := wExpVal_nonneg_le hx
      have h2 := expPos_ge hy
      unfold wExpVal at *; rw [if_neg (not_lt.mpr hy)]; omega
    · unfold wExpVal; rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr hy)]
      exact expPos_mono hx h

/-! ## 5. Prices -/

/-- Rounding `a / d` to the nearest integer, ties down, is non-increasing in `d`. -/
theorem roundHalfDown_anti (a : Nat) {d d' : Nat} (hd : 0 < d) (h : d ≤ d') :
    roundHalfDown a d' ≤ roundHalfDown a d := by
  unfold roundHalfDown
  set k := (a + (d' - 1) / 2) / d'
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]; exact Nat.zero_le _
  · have hkd' : k * d' ≤ a + (d' - 1) / 2 := Nat.div_mul_le_self _ _
    have hkk : k * d' = k * d + k * (d' - d) := by
      rw [← Nat.mul_add]; congr 1; omega
    have hkm : d' - d ≤ k * (d' - d) := Nat.le_mul_of_pos_left _ hk
    apply (Nat.le_div_iff_mul_le hd).mpr
    omega

theorem roundStep_mono {v v' : Nat} (h : v ≤ v') : roundStep v ≤ roundStep v' := by
  unfold roundStep roundHalfDown
  exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

/-- A smaller `wExp` gives a larger price. -/
theorem priceOf_anti {W W' : Nat} (h : W ≤ W') : priceOf W' ≤ priceOf W := by
  unfold priceOf
  exact roundStep_mono (roundHalfDown_anti _ (by omega) (by omega))

theorem priceOf_le_wad (W : Nat) : priceOf W ≤ 1000000000000000000 :=
  le_trans (priceOf_anti (Nat.zero_le W)) (by decide)

end TickLib.Proof.Math
