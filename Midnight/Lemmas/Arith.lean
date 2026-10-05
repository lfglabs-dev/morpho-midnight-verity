import Verity.Core.Uint256

/-!
Arithmetic behind `updatePositionView`: slashing by loss factors and the
continuous-fee accrual, stated on natural numbers.
-/

namespace Midnight.Lemmas

def max128 : Nat := 2 ^ 128 - 1

theorem max128_lt_mod : max128 < 2 ^ 256 := by decide

theorem max128_sq_lt_mod : max128 * max128 < 2 ^ 256 := by decide

theorem max128_sq_add_lt_mod : max128 * max128 + max128 < 2 ^ 256 := by decide

theorem modulus_pow : Verity.Core.Uint256.modulus = 2 ^ 256 := by
  simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

theorem ofNat_val_lt {n : Nat} (h : n < 2 ^ 256) :
    (Verity.Core.Uint256.ofNat n).val = n := by
  rw [Verity.Core.Uint256.val_ofNat, modulus_pow, Nat.mod_eq_of_lt h]

theorem xor_val {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (Verity.Core.Uint256.xor (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b)).val =
      a ^^^ b := by
  unfold Verity.Core.Uint256.xor
  rw [show (Verity.Core.Uint256.ofNat a).val = a from ofNat_val_lt ha,
    show (Verity.Core.Uint256.ofNat b).val = b from ofNat_val_lt hb]
  exact ofNat_val_lt (Nat.xor_lt_two_pow ha hb)

theorem mul_val {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a * b < 2 ^ 256) :
    (Verity.Core.Uint256.mul (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b)).val =
      a * b := by
  unfold Verity.Core.Uint256.mul
  rw [show (Verity.Core.Uint256.ofNat a).val = a from ofNat_val_lt ha,
    show (Verity.Core.Uint256.ofNat b).val = b from ofNat_val_lt hb]
  exact ofNat_val_lt h

theorem mul_zero_val (a : Verity.Core.Uint256) :
    (Verity.Core.Uint256.mul a (Verity.Core.Uint256.ofNat 0)).val = 0 := by
  unfold Verity.Core.Uint256.mul
  simp

theorem xor_cancel (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  apply Nat.eq_of_testBit_eq
  simp

/-- `c * a / b ≤ c` when `a ≤ b` and `b` is positive. -/
theorem mul_div_le_self {c a b : Nat} (hb : 0 < b) (ha : a ≤ b) : c * a / b ≤ c := by
  have hmul : c * a ≤ c * b := Nat.mul_le_mul_left _ ha
  have hdiv : c * a / b ≤ c * b / b := Nat.div_le_div_right hmul
  rwa [Nat.mul_div_cancel _ hb] at hdiv

/-- `(n + d - 1) / d ≤ q` when `n ≤ q * d` and `d > 0`. -/
theorem roundUp_div_le {n d q : Nat} (hd : 0 < d) (hn : n ≤ q * d) :
    (n + d - 1) / d ≤ q := by
  have hdist : (q + 1) * d = q * d + d := by rw [Nat.add_mul, Nat.one_mul]
  have hlt : n + d - 1 < d * (q + 1) := by
    rw [Nat.mul_comm, hdist]
    omega
  have : (n + d - 1) / d < q + 1 := Nat.div_lt_of_lt_mul hlt
  omega

theorem div_mul_le (a b : Nat) : a / b * b ≤ a :=
  Nat.div_mul_le_self a b

/-- Branchless `min`, as lowered from `UtilsLib.min`. -/
theorem branchless_min {x y : Nat} (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    (Verity.Core.Uint256.xor (Verity.Core.Uint256.ofNat x)
      (Verity.Core.Uint256.mul
        (Verity.Core.Uint256.xor (Verity.Core.Uint256.ofNat x) (Verity.Core.Uint256.ofNat y))
        (Verity.Core.Uint256.ofNat (if y < x then 1 else 0)))).val =
      min x y := by
  by_cases hlt : y < x
  · simp only [Verity.Core.Uint256.xor, Verity.Core.Uint256.mul, hlt, if_true]
    rw [ofNat_val_lt hx, ofNat_val_lt hy]
    rw [show (Verity.Core.Uint256.ofNat (x.xor y)).val = x.xor y from
      ofNat_val_lt (Nat.xor_lt_two_pow hx hy)]
    rw [ofNat_val_lt (by decide : (1 : Nat) < 2 ^ 256), Nat.mul_one]
    rw [show (Verity.Core.Uint256.ofNat (x.xor y)).val = x.xor y from
      ofNat_val_lt (Nat.xor_lt_two_pow hx hy)]
    rw [show (Verity.Core.Uint256.ofNat (x.xor (x.xor y))).val = x.xor (x.xor y) from
      ofNat_val_lt (Nat.xor_lt_two_pow hx (Nat.xor_lt_two_pow hx hy))]
    rw [show x.xor (x.xor y) = y by simpa [Nat.xor_eq] using xor_cancel x y]
    exact (Nat.min_eq_right (Nat.le_of_lt hlt)).symm
  · simp only [Verity.Core.Uint256.xor, Verity.Core.Uint256.mul, hlt, if_false]
    rw [ofNat_val_lt hx, ofNat_val_lt hy]
    rw [show (Verity.Core.Uint256.ofNat (x.xor y)).val = x.xor y from
      ofNat_val_lt (Nat.xor_lt_two_pow hx hy)]
    rw [ofNat_val_lt (by decide : (0 : Nat) < 2 ^ 256)]
    rw [show (x.xor y) * 0 = 0 from Nat.mul_zero _]
    rw [ofNat_val_lt (by decide : (0 : Nat) < 2 ^ 256)]
    rw [show x.xor 0 = x by simp [Nat.xor_eq, Nat.xor_zero]]
    rw [ofNat_val_lt hx]
    exact (Nat.min_eq_left ((Nat.not_lt).mp hlt)).symm

theorem mask128_eq {a : Nat} (ha : a ≤ max128) :
    (Verity.Core.Uint256.and (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat max128)).val = a := by
  have hlt : a < 2 ^ 128 := by
    have := ha
    unfold max128 at this
    omega
  unfold Verity.Core.Uint256.and
  rw [ofNat_val_lt (Nat.lt_of_le_of_lt ha max128_lt_mod), ofNat_val_lt max128_lt_mod,
    show max128 = 2 ^ 128 - 1 from rfl]
  have hland : a.land (2 ^ 128 - 1) = a := by
    rw [Nat.land_eq]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hlt
  rw [hland]
  exact ofNat_val_lt (Nat.lt_trans hlt (by decide : 2 ^ 128 < 2 ^ 256))

/-- Inputs of one view, already narrowed to their Solidity ranges. -/
structure Inp where
  credit : Nat
  pending : Nat
  lastLoss : Nat
  loss : Nat
  lastAccrual : Nat
  maturity : Nat
  timestamp : Nat
  credit_le : credit ≤ max128
  pending_le : pending ≤ max128
  lastLoss_le : lastLoss ≤ max128
  loss_le : loss ≤ max128
  lastAccrual_le : lastAccrual ≤ max128
  maturity_lt : maturity < 2 ^ 256
  timestamp_lt : timestamp < 2 ^ 256
  lastLoss_le_loss : lastLoss ≤ loss

def mapN (factor : Nat) : Nat := max128 - factor

def postSlashCredit (i : Inp) : Nat :=
  if i.lastLoss < max128 then i.credit * mapN i.loss / mapN i.lastLoss else 0

theorem postSlashCredit_le (i : Inp) : postSlashCredit i ≤ i.credit := by
  unfold postSlashCredit mapN
  have hll : i.lastLoss ≤ i.loss := i.lastLoss_le_loss
  split
  · have hpos : 0 < max128 - i.lastLoss := by omega
    have hle : max128 - i.loss ≤ max128 - i.lastLoss := by omega
    exact mul_div_le_self hpos hle
  · exact Nat.zero_le _

def postSlashPending (i : Inp) : Nat :=
  if i.credit = 0 then 0
  else
    let delta := i.credit - postSlashCredit i
    i.pending - (i.pending * delta + (i.credit - 1)) / i.credit

theorem postSlashPending_le (i : Inp) : postSlashPending i ≤ i.pending := by
  unfold postSlashPending
  split
  · exact Nat.zero_le _
  · rename_i hpos
    have hc : 0 < i.credit := Nat.pos_of_ne_zero hpos
    have hq : (i.pending * (i.credit - postSlashCredit i) + (i.credit - 1)) / i.credit ≤ i.pending := by
      have heq : i.pending * (i.credit - postSlashCredit i) + (i.credit - 1) =
          i.pending * (i.credit - postSlashCredit i) + i.credit - 1 := by omega
      rw [heq]
      have hn : i.pending * (i.credit - postSlashCredit i) ≤ i.pending * i.credit :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact roundUp_div_le hc hn
    exact Nat.sub_le _ _

def accrualEnd (i : Inp) : Nat := min i.timestamp i.maturity

def feeOf (i : Inp) : Option Nat :=
  let psp := postSlashPending i
  if i.lastAccrual < i.maturity then
    let endt := accrualEnd i
    if endt < i.lastAccrual then none
    else
      let elapsed := endt - i.lastAccrual
      let span := i.maturity - i.lastAccrual
      if psp * elapsed < 2 ^ 256 then some (psp * elapsed / span) else none
  else some 0

theorem feeOf_le_pending {i : Inp} {fee : Nat} (h : feeOf i = some fee) :
    fee ≤ postSlashPending i := by
  unfold feeOf at h
  by_cases hA : i.lastAccrual < i.maturity
  · simp only [hA, if_true] at h
    by_cases hE : accrualEnd i < i.lastAccrual
    · simp [hE] at h
    · simp only [hE, if_false] at h
      by_cases hov : postSlashPending i * (accrualEnd i - i.lastAccrual) < 2 ^ 256
      · simp only [hov, if_true, Option.some.injEq] at h
        subst fee
        have hspan : 0 < i.maturity - i.lastAccrual := by omega
        have hel : accrualEnd i - i.lastAccrual ≤ i.maturity - i.lastAccrual := by
          unfold accrualEnd
          have : min i.timestamp i.maturity ≤ i.maturity := Nat.min_le_right _ _
          omega
        exact mul_div_le_self hspan hel
      · simp [hov] at h
  · simp only [hA, if_false, Option.some.injEq] at h
    subst fee
    exact Nat.zero_le _

def predict (i : Inp) : Option (Nat × Nat × Nat) :=
  match feeOf i with
  | none => none
  | some fee =>
    if fee ≤ postSlashCredit i then
      some (postSlashCredit i - fee, postSlashPending i - fee, fee)
    else none

theorem predict_bounds {i : Inp} {nc np fee : Nat} (h : predict i = some (nc, np, fee)) :
    fee ≤ i.pending ∧ nc ≤ i.credit ∧ np ≤ i.pending ∧
      nc + fee = postSlashCredit i ∧ np + fee = postSlashPending i ∧
      fee ≤ postSlashPending i := by
  unfold predict at h
  cases hf : feeOf i with
  | none => simp [hf] at h
  | some f =>
    rw [hf] at h
    by_cases hle : f ≤ postSlashCredit i
    · simp only [hle, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hfee : f ≤ postSlashPending i := feeOf_le_pending hf
      refine ⟨Nat.le_trans hfee (postSlashPending_le i), ?_, ?_, ?_, ?_, hfee⟩
      · exact Nat.le_trans (Nat.sub_le _ _) (postSlashCredit_le i)
      · exact Nat.le_trans (Nat.sub_le _ _) (postSlashPending_le i)
      · omega
      · omega
    · simp [hle] at h

theorem predict_slash {i : Inp} {nc np fee : Nat} (h : predict i = some (nc, np, fee)) :
    (nc + fee) * mapN i.lastLoss ≤ i.credit * mapN i.loss := by
  have hb := predict_bounds h
  rw [hb.2.2.2.1]
  unfold postSlashCredit mapN
  split
  · exact div_mul_le _ _
  · simp

theorem predict_total_loss {i : Inp} {nc np fee : Nat} (h : predict i = some (nc, np, fee))
    (hz : mapN i.loss = 0) : nc = 0 ∧ fee = 0 := by
  have hb := predict_bounds h
  have hloss : i.loss = max128 := by
    have hle : i.loss ≤ max128 := i.loss_le
    unfold mapN at hz
    omega
  have hpsc : postSlashCredit i = 0 := by
    unfold postSlashCredit
    rw [hloss]
    split <;> simp [mapN]
  have : nc + fee = 0 := by simpa [hpsc] using hb.2.2.2.1
  omega

end Midnight.Lemmas
