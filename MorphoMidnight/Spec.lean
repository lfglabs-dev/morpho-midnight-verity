import Mathlib.Tactic

/-!
Mathematical form of the successful `updatePositionView` slash-and-accrue step.

`M = 2^128 - 1`, `A = M - g`, `B = M - ell`. On a successful call with
`ell ≤ g` and `lastAccrual ≤ timestamp`:

* `q = floor(c*A/B)` when `B > 0`, else `0`
* `r = p - ceil(p*(c-q)/c)` when `c > 0`, else `0`
* `fee` is the accrued amount, and success means `fee ≤ q` and `fee ≤ r`

These theorems are about that arithmetic. They do not by themselves say that
`midnight.model` computes it. That correspondence is not a kernel theorem yet;
see `TRUST.md`.
-/

namespace MorphoMidnight.Spec

def M : Nat := 2 ^ 128 - 1

def q (c A B : Nat) : Nat :=
  if B = 0 then 0 else c * A / B

def ceilDiv (n d : Nat) : Nat :=
  if d = 0 then 0 else (n + d - 1) / d

def pendingAfterSlash (c p qv : Nat) : Nat :=
  if c = 0 then 0 else p - ceilDiv (p * (c - qv)) c

def A (g : Nat) : Nat := M - g
def B (ell : Nat) : Nat := M - ell

theorem q_le_c {c A B : Nat} (hA : A ≤ B) (hB : 0 < B) : q c A B ≤ c := by
  have hne : B ≠ 0 := Nat.ne_of_gt hB
  unfold q
  rw [if_neg hne]
  have hmul : c * A ≤ c * B := Nat.mul_le_mul_left c hA
  have hdiv : c * A / B ≤ c * B / B := Nat.div_le_div_right hmul
  rw [Nat.mul_div_cancel c hB] at hdiv
  exact hdiv

theorem q_mul_le {c A B : Nat} (hB : 0 < B) : q c A B * B ≤ c * A := by
  have hne : B ≠ 0 := Nat.ne_of_gt hB
  unfold q
  rw [if_neg hne]
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (c * A) B

theorem pending_le {c p qv : Nat} : pendingAfterSlash c p qv ≤ p := by
  unfold pendingAfterSlash
  split
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

theorem pending_zero_when_q_zero {c p : Nat} : pendingAfterSlash c p 0 = 0 := by
  unfold pendingAfterSlash
  split
  · rfl
  · rename_i hc
    have hc0 : 0 < c := Nat.pos_of_ne_zero hc
    have hceil : ceilDiv (p * c) c = p := by
      unfold ceilDiv
      rw [if_neg hc]
      have h1 : 1 ≤ c := Nat.succ_le_of_lt hc0
      have hsum : p * c + c - 1 = c * p + (c - 1) := by
        rw [Nat.mul_comm p c]
        exact Nat.add_sub_assoc h1 (c * p)
      rw [hsum, Nat.mul_add_div hc0 p (c - 1)]
      have hsmall : (c - 1) / c = 0 := Nat.div_eq_of_lt (Nat.sub_lt hc0 Nat.one_pos)
      simp [hsmall]
    simp [hceil]

theorem slash_zero_of_A {c g ell : Nat}
    (hell : ell ≤ M) (hg : g ≤ M) (horder : ell ≤ g) (hB : B ell = 0) :
    A g = 0 ∧ q c (A g) (B ell) = 0 := by
  have hellM : ell = M := by
    unfold B at hB
    exact Nat.le_antisymm hell ((Nat.sub_eq_zero_iff_le).mp hB)
  have hgM : g = M := by
    have hMg : M ≤ g := by simpa [hellM] using horder
    exact Nat.le_antisymm hg hMg
  unfold A q
  simp [hellM, hgM]

/-- Property 2 for a successful call: `newCredit + fee = q` when `B > 0`. -/
theorem property2 {newCredit fee c A B : Nat}
    (hB : 0 < B) (hsum : newCredit + fee = q c A B) :
    (newCredit + fee) * B ≤ c * A := by
  rw [hsum]
  exact q_mul_le hB

/-- Property 3, from `newCredit + fee = q` and `q ≤ c`. -/
theorem property3 {newCredit fee c A B : Nat}
    (hA : A ≤ B) (hB : 0 < B) (hsum : newCredit + fee = q c A B) :
    newCredit ≤ c := by
  have hq : q c A B ≤ c := q_le_c hA hB
  have hle : newCredit ≤ newCredit + fee := Nat.le_add_right newCredit fee
  rw [hsum] at hle
  exact Nat.le_trans hle hq

/-- Property 1 and 4: a fee that fits in the slashed pending fee is ≤ p. -/
theorem property1_and_4 {fee newPending p : Nat}
    (hfee : fee ≤ newPending + fee) (hpend : newPending + fee ≤ p) :
    fee ≤ p ∧ newPending ≤ p :=
  ⟨Nat.le_trans hfee hpend, Nat.le_trans (Nat.le_add_right newPending fee) hpend⟩

/-- Property 5. `A = 0` forces `q = 0`. Success with `newCredit + fee = q`
and `fee ≤ pendingAfterSlash` then forces both results to be zero when the
slashed pending fee is zero. -/
theorem property5 {newCredit fee c p g ell : Nat}
    (hell : ell ≤ M) (hg : g ≤ M) (horder : ell ≤ g) (hB0 : B ell = 0)
    (hsum : newCredit + fee = q c (A g) (B ell))
    (hfee : fee ≤ pendingAfterSlash c p (q c (A g) (B ell))) :
    newCredit = 0 ∧ fee = 0 := by
  obtain ⟨_, hq0⟩ := slash_zero_of_A (c := c) hell hg horder hB0
  have hq : q c (A g) (B ell) = 0 := hq0
  have hsum0 : newCredit + fee = 0 := by simpa [hq] using hsum
  have hfee0 : fee ≤ pendingAfterSlash c p 0 := by simpa [hq] using hfee
  have hpend0 : pendingAfterSlash c p 0 = 0 := pending_zero_when_q_zero
  have hfeeZ : fee = 0 := Nat.eq_zero_of_le_zero (by simpa [hpend0] using hfee0)
  have hnew : newCredit = 0 := by simpa [hfeeZ] using hsum0
  exact ⟨hnew, hfeeZ⟩

/-- `B = 0` and `ell ≤ g ≤ M` imply `A = 0`, so both sides of the CVL
inequality are zero when `preciseCreditDivFactor = 0`. -/
theorem cvl_bridge_zero {newCredit fee precise A PRECISION : Nat}
    (hA : A = 0) (hprecise : precise = 0) (hsum : newCredit + fee = 0) :
    (newCredit + fee) * PRECISION ≤ precise * A := by
  simp [hsum, hprecise, hA]

/-- For `B > 0`, with `precise * B = PRECISION * c` and
`(newCredit + fee) * B ≤ c * A`. -/
theorem cvl_bridge {newCredit fee c A B precise PRECISION : Nat}
    (hB : 0 < B) (_hP : 0 < PRECISION)
    (hfactor : precise * B = PRECISION * c)
    (hineq : (newCredit + fee) * B ≤ c * A) :
    (newCredit + fee) * PRECISION ≤ precise * A := by
  have hcomm : (newCredit + fee) * PRECISION * B = (newCredit + fee) * B * PRECISION := by ring
  have hmul1 : (newCredit + fee) * B * PRECISION ≤ c * A * PRECISION :=
    Nat.mul_le_mul_right PRECISION hineq
  have hmul : (newCredit + fee) * PRECISION * B ≤ c * A * PRECISION := by
    simpa [hcomm] using hmul1
  have hrewrite : c * A * PRECISION = precise * A * B := by
    calc
      c * A * PRECISION = A * (PRECISION * c) := by ring
      _ = A * (precise * B) := by rw [← hfactor]
      _ = precise * A * B := by ring
  have hle : (newCredit + fee) * PRECISION * B ≤ precise * A * B := by
    simpa [hrewrite] using hmul
  exact Nat.le_of_mul_le_mul_right hle hB

end MorphoMidnight.Spec
