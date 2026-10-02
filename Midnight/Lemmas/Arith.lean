import Midnight.Spec

/-!
Arithmetic behind a successful `updatePositionView`: checked word operations,
the imported Yul `min`, and the five Certora assertions.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open Verity.Core
open Midnight.Spec

namespace Midnight.Lemmas

/-- `type(uint128).max`. -/
def U : Nat := 2 ^ 128 - 1

/-- EVM word modulus. -/
def MOD : Nat := 2 ^ 256

theorem U_lt_MOD : U < MOD := by decide

theorem U_sq_lt_MOD : U * U < MOD := by decide

theorem U_sq_add_U_lt_MOD : U * U + U < MOD := by decide

theorem uint128_le_U (x : UIntN 128) : x.val ≤ U := by
  have hlt : x.val < 2 ^ 128 := x.isLt
  have hsucc : U + 1 = 2 ^ 128 := by decide
  omega

theorem mapFactor_eq_nat (factor : UIntN 128) :
    mapFactor factor = Int.ofNat (U - factor.val) := by
  unfold mapFactor U
  have hle : factor.val ≤ 2 ^ 128 - 1 := uint128_le_U factor
  have hone : (1 : Nat) ≤ 2 ^ 128 := by decide
  have h2 : ((2 : Nat) : Int) = 2 := rfl
  have hcast :
      (2 ^ 128 - 1 - (factor.val : Int)) =
        ((2 ^ 128 - 1 : Nat) : Int) - (factor.val : Int) := by
    rw [Int.ofNat_sub hone]
    simp only [← h2, Int.natCast_pow, Int.natCast_one]
  rw [hcast, ← Int.ofNat_sub hle]
  rfl

theorem mapFactor_eq_zero_iff (factor : UIntN 128) :
    mapFactor factor = 0 ↔ factor.val = U := by
  rw [mapFactor_eq_nat]
  constructor
  · intro h
    have hnat : U - factor.val = 0 := Int.ofNat_inj.mp h
    have hle := uint128_le_U factor
    omega
  · intro h
    simp [h]

def csub? (a b : Nat) : Option Nat :=
  if b ≤ a then some (a - b) else none

def cmul? (a b : Nat) : Option Nat :=
  if a * b < MOD then some (a * b) else none

def cadd? (a b : Nat) : Option Nat :=
  if a + b < MOD then some (a + b) else none

def cdiv? (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

/-- `uint128(x)` as imported: a mask with `type(uint128).max`. -/
def narrow (n : Nat) : Nat := n &&& U

theorem narrow_le_left (n : Nat) : narrow n ≤ n := by
  simpa [narrow] using Nat.and_le_left (n := n) (m := U)

theorem narrow_eq_mod (n : Nat) : narrow n = n % 2 ^ 128 := by
  unfold narrow U
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 128
  · simp [hi]
  · simp [hi]

theorem narrow_eq_of_le_U {n : Nat} (h : n ≤ U) : narrow n = n := by
  rw [narrow_eq_mod]
  have hlt : n < 2 ^ 128 := by
    have hsucc : U + 1 = 2 ^ 128 := by decide
    omega
  exact Nat.mod_eq_of_lt hlt

private theorem xor_xor_cancel_left (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases hx : x.testBit i <;> cases hy : y.testBit i <;>
    simp [Nat.testBit_xor, hx, hy]

/-- Imported `UtilsLib.min`: `xor(x, mul(xor(x, y), lt(y, x)))`. -/
def yulMin (x y : Nat) : Nat :=
  x ^^^ ((x ^^^ y) * (if y < x then 1 else 0))

theorem yulMin_eq (x y : Nat) : yulMin x y = if y < x then y else x := by
  unfold yulMin
  by_cases h : y < x
  · simp [h, xor_xor_cancel_left]
  · simp [h, Nat.xor_zero]

theorem yulMin_le_right (x y : Nat) : yulMin x y ≤ y := by
  rw [yulMin_eq]
  split <;> omega

theorem yulMin_le_left (x y : Nat) : yulMin x y ≤ x := by
  rw [yulMin_eq]
  split <;> omega

def postSlashCredit? (credit lastLossFactor lossFactor : Nat) : Option Nat :=
  if lastLossFactor < U then do
    let mfM ← csub? U lossFactor
    let mfL ← csub? U lastLossFactor
    let prod ← cmul? credit mfM
    cdiv? prod mfL
  else
    some 0

def postSlashPendingFee? (credit pending postSlashCredit : Nat) : Option Nat :=
  if credit > 0 then do
    let delta ← csub? credit postSlashCredit
    let prod ← cmul? pending delta
    let cm1 ← csub? credit 1
    let sum ← cadd? prod cm1
    let quot ← cdiv? sum credit
    csub? pending quot
  else
    some 0

def feeWord? (postSlashPendingFee accrualEnd lastAccrual maturity : Nat) : Option Nat :=
  if lastAccrual < maturity then do
    let dt ← csub? accrualEnd lastAccrual
    let span ← csub? maturity lastAccrual
    let prod ← cmul? postSlashPendingFee dt
    let q ← cdiv? prod span
    some (narrow q)
  else
    some 0

def returnWords? (postSlashCredit postSlashPendingFee fee : Nat) : Option (Nat × Nat × Nat) := do
  let newCredit ← csub? (narrow postSlashCredit) fee
  let newPending ← csub? (narrow postSlashPendingFee) fee
  some (newCredit, newPending, fee)

def viewResult? (credit lastLossFactor lossFactor pending lastAccrual timestamp maturity : Nat) :
    Option (Nat × Nat × Nat) := do
  let postSlashCredit ← postSlashCredit? credit lastLossFactor lossFactor
  let postSlashPendingFee ← postSlashPendingFee? credit pending postSlashCredit
  let fee ← feeWord? postSlashPendingFee (yulMin timestamp maturity) lastAccrual maturity
  returnWords? postSlashCredit postSlashPendingFee fee

theorem csub_some_iff {a b v : Nat} : csub? a b = some v ↔ b ≤ a ∧ v = a - b := by
  unfold csub?
  split <;> rename_i h <;> simp [h, eq_comm]

theorem cmul_some_iff {a b v : Nat} : cmul? a b = some v ↔ a * b < MOD ∧ v = a * b := by
  unfold cmul?
  split <;> rename_i h <;> simp [h, eq_comm]

theorem cadd_some_iff {a b v : Nat} : cadd? a b = some v ↔ a + b < MOD ∧ v = a + b := by
  unfold cadd?
  split <;> rename_i h <;> simp [h, eq_comm]

theorem cdiv_some_iff {a b v : Nat} : cdiv? a b = some v ↔ b ≠ 0 ∧ v = a / b := by
  unfold cdiv?
  split <;> rename_i h <;> simp [h, eq_comm]

theorem mul_bound {a b : Nat} (ha : a ≤ U) (hb : b ≤ U) : a * b < MOD :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul ha hb) U_sq_lt_MOD

theorem add_bound {prod credit : Nat} (hprod : prod ≤ U * U) (hc : credit ≤ U) :
    prod + (credit - 1) < MOD := by
  have : prod + (credit - 1) ≤ U * U + U := by omega
  exact Nat.lt_of_le_of_lt this U_sq_add_U_lt_MOD

/-- Under the uint128 bounds the slash quotient always fits, and equals the model. -/
theorem postSlashCredit_eq {credit lastLossFactor lossFactor : Nat}
    (hc : credit ≤ U) (hll : lastLossFactor ≤ U) (hlf : lossFactor ≤ U) :
    postSlashCredit? credit lastLossFactor lossFactor =
      some (if lastLossFactor < U then
        (credit * (U - lossFactor)) / (U - lastLossFactor) else 0) := by
  unfold postSlashCredit?
  by_cases hlt : lastLossFactor < U
  · have hmfL : U - lastLossFactor ≠ 0 := by omega
    have hmul : credit * (U - lossFactor) < MOD :=
      mul_bound hc (by omega)
    simp [hlt, csub?, hll, hlf, cmul?, hmul, cdiv?, hmfL]
  · simp [hlt]

theorem postSlashCredit_le {credit lastLossFactor lossFactor psc : Nat}
    (hc : credit ≤ U) (hll : lastLossFactor ≤ U) (hlf : lossFactor ≤ U)
    (hord : lastLossFactor ≤ lossFactor)
    (h : postSlashCredit? credit lastLossFactor lossFactor = some psc) :
    psc ≤ credit := by
  rw [postSlashCredit_eq hc hll hlf] at h
  cases h
  by_cases hlt : lastLossFactor < U
  · simp only [hlt]
    have hmf : U - lossFactor ≤ U - lastLossFactor := by omega
    have hmul : credit * (U - lossFactor) ≤ credit * (U - lastLossFactor) :=
      Nat.mul_le_mul_left _ hmf
    have hpos : 0 < U - lastLossFactor := by omega
    exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)
  · simp [hlt]

theorem ceilDiv_cancel {p c : Nat} (hc : 0 < c) :
    (p * c + (c - 1)) / c = p := by
  have hge : p ≤ (p * c + (c - 1)) / c :=
    (Nat.le_div_iff_mul_le hc).2 (Nat.le_add_right _ _)
  have hhi : p * c + (c - 1) < (p + 1) * c := by
    have : (p + 1) * c = p * c + c := by simp [Nat.add_mul]
    omega
  have hlt : (p * c + (c - 1)) / c < p + 1 :=
    (Nat.div_lt_iff_lt_mul hc).2 hhi
  omega

theorem postSlashPendingFee_eq {credit pending psc : Nat}
    (hc : credit ≤ U) (hp : pending ≤ U) (hpsc : psc ≤ credit) :
    postSlashPendingFee? credit pending psc =
      some (if credit = 0 then 0 else
        pending - (pending * (credit - psc) + (credit - 1)) / credit) := by
  unfold postSlashPendingFee?
  by_cases hpos : credit > 0
  · have hdelta : psc ≤ credit := hpsc
    have hdlt : credit - psc ≤ U := by omega
    have hmul : pending * (credit - psc) < MOD := mul_bound hp hdlt
    have hprodLe : pending * (credit - psc) ≤ U * U := Nat.mul_le_mul hp hdlt
    have hadd : pending * (credit - psc) + (credit - 1) < MOD := add_bound hprodLe hc
    have hquot : (pending * (credit - psc) + (credit - 1)) / credit ≤ pending := by
      have hle : pending * (credit - psc) + (credit - 1) ≤ pending * credit + (credit - 1) := by
        have : credit - psc ≤ credit := by omega
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _
      have hdiv : (pending * credit + (credit - 1)) / credit = pending := ceilDiv_cancel hpos
      have : (pending * (credit - psc) + (credit - 1)) / credit ≤
          (pending * credit + (credit - 1)) / credit :=
        Nat.div_le_div_right hle
      omega
    have hone : 1 ≤ credit := hpos
    have hne : credit ≠ 0 := by omega
    rw [if_pos hpos]
    simp only [csub?, if_pos hdelta, if_pos hone, bind, pure_bind, Option.bind]
    simp only [cmul?, if_pos hmul, cadd?, if_pos hadd, cdiv?, if_neg hne, if_pos hquot, bind,
      pure_bind, Option.bind]
  · have : credit = 0 := by omega
    rw [if_neg hpos]
    simp [this]

theorem postSlashPendingFee_le {credit pending psc pspf : Nat}
    (h : postSlashPendingFee? credit pending psc = some pspf) :
    pspf ≤ pending := by
  unfold postSlashPendingFee? at h
  by_cases hpos : credit > 0
  · rw [if_pos hpos] at h
    cases h1 : csub? credit psc with
    | none => simp [h1] at h
    | some delta =>
      simp only [h1, bind, pure_bind, Option.bind] at h
      cases h2 : cmul? pending delta with
      | none => simp [h2] at h
      | some prod =>
        simp only [h2, bind, pure_bind, Option.bind] at h
        cases h3 : csub? credit 1 with
        | none => simp [h3] at h
        | some cm1 =>
          simp only [h3, bind, pure_bind, Option.bind] at h
          cases h4 : cadd? prod cm1 with
          | none => simp [h4] at h
          | some sum =>
            simp only [h4, bind, pure_bind, Option.bind] at h
            cases h5 : cdiv? sum credit with
            | none => simp [h5] at h
            | some quot =>
              simp only [h5, bind, pure_bind, Option.bind] at h
              rw [csub_some_iff] at h
              omega
  · simp only [hpos] at h
    cases h
    exact Nat.zero_le _

theorem feeWord_le {pspf endTs lastAccrual maturity fee : Nat}
    (hend : endTs ≤ maturity)
    (h : feeWord? pspf endTs lastAccrual maturity = some fee) :
    fee ≤ pspf := by
  unfold feeWord? at h
  by_cases hlt : lastAccrual < maturity
  · simp only [hlt] at h
    cases h1 : csub? endTs lastAccrual with
    | none => simp [h1] at h
    | some dt =>
      simp only [h1, bind, pure_bind, Option.bind] at h
      cases h2 : csub? maturity lastAccrual with
      | none => simp [h2] at h
      | some span =>
        simp only [h2, bind, pure_bind, Option.bind] at h
        cases h3 : cmul? pspf dt with
        | none => simp [h3] at h
        | some prod =>
          simp only [h3, bind, pure_bind, Option.bind] at h
          cases h4 : cdiv? prod span with
          | none => simp [h4] at h
          | some q =>
            simp only [h4, bind, pure_bind, Option.bind] at h
            cases h
            rw [csub_some_iff] at h1 h2
            rw [cmul_some_iff] at h3
            rw [cdiv_some_iff] at h4
            have hdt : dt ≤ span := by omega
            have hmul : pspf * dt ≤ pspf * span := Nat.mul_le_mul_left _ hdt
            have hpos : 0 < span := by omega
            have hq : q ≤ pspf := by
              have : prod / span ≤ pspf := by
                refine Nat.div_le_of_le_mul ?_
                simpa [h3.2, Nat.mul_comm] using hmul
              simpa [h4.2] using this
            exact Nat.le_trans (narrow_le_left _) hq
  · simp only [hlt] at h
    cases h
    exact Nat.zero_le _

theorem asserts_of_view {credit lastLossFactor lossFactor pending lastAccrual timestamp maturity
    nc np fee : Nat}
    (hc : credit ≤ U) (hll : lastLossFactor ≤ U) (hlf : lossFactor ≤ U) (hp : pending ≤ U)
    (hord : lastLossFactor ≤ lossFactor)
    (h : viewResult? credit lastLossFactor lossFactor pending lastAccrual timestamp maturity =
      some (nc, np, fee)) :
    fee ≤ pending ∧
      (nc + fee) * (U - lastLossFactor) ≤ credit * (U - lossFactor) ∧
      nc ≤ credit ∧
      np ≤ pending ∧
      (U - lossFactor = 0 → nc = 0 ∧ fee = 0) := by
  simp only [viewResult?] at h
  cases hpsc : postSlashCredit? credit lastLossFactor lossFactor with
  | none => simp [hpsc] at h
  | some psc =>
    simp only [hpsc, bind, pure_bind, Option.bind] at h
    cases hpspf : postSlashPendingFee? credit pending psc with
    | none => simp [hpspf] at h
    | some pspf =>
      simp only [hpspf, bind, pure_bind, Option.bind] at h
      cases hfee : feeWord? pspf (yulMin timestamp maturity) lastAccrual maturity with
      | none => simp [hfee] at h
      | some fee' =>
        simp only [hfee, returnWords?, bind, pure_bind, Option.bind] at h
        cases hnc : csub? (narrow psc) fee' with
        | none => simp [hnc] at h
        | some nc' =>
          simp only [hnc, bind, pure_bind, Option.bind] at h
          cases hnp : csub? (narrow pspf) fee' with
          | none => simp [hnp] at h
          | some np' =>
            simp only [hnp, bind, pure_bind, Option.bind] at h
            cases h
            rw [csub_some_iff] at hnc hnp
            have hpscLe : psc ≤ credit := postSlashCredit_le hc hll hlf hord hpsc
            have hpspfLe : pspf ≤ pending := postSlashPendingFee_le hpspf
            have hnarP : narrow psc = psc := narrow_eq_of_le_U (Nat.le_trans hpscLe hc)
            have hnarF : narrow pspf = pspf := narrow_eq_of_le_U (Nat.le_trans hpspfLe hp)
            have hfeeLe : fee ≤ pspf :=
              feeWord_le (yulMin_le_right timestamp maturity) hfee
            have hfeePend : fee ≤ pending := Nat.le_trans hfeeLe hpspfLe
            have hsum : nc + fee = psc := by
              have hsub : nc = psc - fee := by simpa [hnarP] using hnc.2
              omega
            have hprod : psc * (U - lastLossFactor) ≤ credit * (U - lossFactor) := by
              rw [postSlashCredit_eq hc hll hlf] at hpsc
              cases hpsc
              by_cases hlt : lastLossFactor < U
              · simp only [hlt]
                exact Nat.div_mul_le_self _ _
              · simp [show lastLossFactor = U by omega]
            refine ⟨hfeePend, ?_, ?_, ?_, ?_⟩
            · simpa [hsum] using hprod
            · have : nc = psc - fee := by simpa [hnarP] using hnc.2
              omega
            · have : np = pspf - fee := by simpa [hnarF] using hnp.2
              omega
            · intro hzero
              have hloss : lossFactor = U := by omega
              have hpsc0 : psc = 0 := by
                rw [postSlashCredit_eq hc hll hlf] at hpsc
                cases hpsc
                by_cases hlt : lastLossFactor < U
                · simp [hlt, hloss]
                · simp [hlt]
              have hpspf0 : pspf = 0 := by
                rw [postSlashPendingFee_eq hc hp hpscLe, hpsc0] at hpspf
                cases hpspf
                by_cases hz : credit = 0
                · simp [hz]
                · have hpos : 0 < credit := by omega
                  simp only [hz, ite_false]
                  have hcancel := ceilDiv_cancel (p := pending) (c := credit) hpos
                  have : pending - (pending * credit + (credit - 1)) / credit = 0 := by
                    rw [hcancel]
                    exact Nat.sub_self _
                  simpa using this
              have hfee0 : fee = 0 := by
                unfold feeWord? at hfee
                by_cases hlt : lastAccrual < maturity
                · simp only [hlt, hpspf0] at hfee
                  cases h1 : csub? (yulMin timestamp maturity) lastAccrual with
                  | none => simp [h1] at hfee
                  | some dt =>
                    simp only [h1, bind, pure_bind, Option.bind] at hfee
                    cases h2 : csub? maturity lastAccrual with
                    | none => simp [h2] at hfee
                    | some span =>
                      simp only [h2, bind, pure_bind, Option.bind] at hfee
                      cases h3 : cmul? 0 dt with
                      | none => simp [h3] at hfee
                      | some prod =>
                        simp only [h3, bind, pure_bind, Option.bind] at hfee
                        cases h4 : cdiv? prod span with
                        | none => simp [h4] at hfee
                        | some q =>
                          simp only [h4, bind, pure_bind, Option.bind] at hfee
                          cases hfee
                          rw [cmul_some_iff] at h3
                          rw [cdiv_some_iff] at h4
                          have : q = 0 := by simpa [h3.2] using h4.2
                          simp [this, narrow]
                · simp [hlt] at hfee
                  exact hfee.symm
              have hnc0 : nc = 0 := by
                have : nc = psc - fee := by simpa [hnarP] using hnc.2
                omega
              exact ⟨hnc0, hfee0⟩

end Midnight.Lemmas
