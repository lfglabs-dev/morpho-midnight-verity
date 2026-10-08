import Midnight.Spec
import Midnight.Lemmas.Exec

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight

local macro "lk" : tactic =>
  `(tactic| simp (discharger := decide) [lookup_bind_same, lookup_bind_other, lookupValue])

abbrev fields : List Field := midnight.model.fields

def body : List Stmt := functionBody midnight.model "updatePositionView"

def skip : List Stmt → Nat → List Stmt
  | s, 0 => s
  | [], _ => []
  | _ :: r, n + 1 => skip r n

def at_ (n : Nat) : List Stmt := skip body n

def brYes (n : Nat) : List Stmt :=
  match at_ n with
  | .ite _ t _ :: _ => t
  | _ => []

def brNo (n : Nat) : List Stmt :=
  match at_ n with
  | .ite _ _ e :: _ => e
  | _ => []

def brYesAt (n k : Nat) : List Stmt := skip (brYes n) k

def brNoAt (n k : Nat) : List Stmt := skip (brNo n) k

theorem pos_ok (member : String)
    (h : member = "credit" ∨ member = "pendingFee" ∨ member = "lastLossFactor" ∨
      member = "lastAccrual") :
    (findFieldWithResolvedSlot fields "position").isSome ∧
      (findMember midnight.model "position" member).isSome := by
  rcases h with h | h | h | h <;> subst h <;> decide

theorem mkt_ok :
    (findFieldWithResolvedSlot fields "marketState").isSome ∧
      (findMember midnight.model "marketState" "lossFactor").isSome := by
  decide

theorem shape0 : at_ 0 =
    .letVar "_credit" (.structMember2 "position" (.param "id") (.param "user") "credit") :: at_ 1 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape1 : at_ 1 =
    .letVar "_lastLossFactor"
      (.structMember2 "position" (.param "id") (.param "user") "lastLossFactor") :: at_ 2 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape2 : at_ 2 =
    .letVar "_verity_slice_tmp_0"
      (.lt (.localVar "_lastLossFactor") (.literal max128)) :: at_ 3 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape4 : at_ 4 =
    .ite (.localVar "_verity_slice_tmp_0") (brYes 4) (brNo 4) :: at_ 5 := by
  unfold at_ brYes brNo skip body functionBody functionBody.go; rfl

/-- Post-slash credit on the taken branch, as a natural number. -/
def postSlashCreditN (credit lastLoss loss : Nat) : Nat :=
  if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0

theorem step_reads
    (o : DenoteOracle) (w : Verity.ContractState) (maturity : Uint256) (id : BytesN 32) (user : Address) :
    let s0 : DenoteState :=
      { world := w, bindings := [("market_maturity", maturity.val), ("id", id.val), ("user", user.val)] }
    let C := (midnight.position.credit o w id user).val
    let L := (midnight.position.lastLossFactor o w id user).val
    let sL :=
      { s0 with bindings := bindValue (bindValue s0.bindings "_credit" C) "_lastLossFactor" L }
    execStmtList o fields s0 (at_ 0) = execStmtList o fields sL (at_ 2) := by
  intro s0 C L sL
  have hC : readMember o midnight.model w "position" [id.val, user.val] "credit" = C := by
    simp [C, midnight.position.credit_val]
  have hL : readMember o midnight.model w "position" [id.val, user.val] "lastLossFactor" = L := by
    simp [L, midnight.position.lastLossFactor_val]
  rw [shape0, exec_let_cons]
  rw [evalExpr_structMember2_param (oracle := o) (model := midnight.model) (state := s0)
    "position" "id" "user" "credit" (pos_ok "credit" (by simp))]
  simp [s0, lookupValue, hC]
  rw [shape1, exec_let_cons]
  rw [evalExpr_structMember2_param (h := pos_ok "lastLossFactor" (by simp))]
  simp [lookupValue, bindValue, List.filter, s0, sL, hL]

theorem shape3 : at_ 3 = .letVar "_verity_slice_tmp_9" (.literal 0) :: at_ 4 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape5 : at_ 5 =
    .letVar "postSlashCredit" (.localVar "_verity_slice_tmp_9") :: at_ 6 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem br4y0 : brYes 4 =
    .letVar "_verity_slice_tmp_1"
      (.structMember "marketState" (.param "id") "lossFactor") :: brYesAt 4 1 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4y12 : brYesAt 4 12 =
    [.assignVar "_verity_slice_tmp_9" (.localVar "_verity_slice_tmp_8")] := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4n : brNo 4 = [.assignVar "_verity_slice_tmp_9" (.literal 0)] := by
  unfold brNo at_ skip body functionBody functionBody.go; rfl

theorem br4subNum : brYesAt 4 1 =
    .letVar "_verity_slice_tmp_2" (.literal 0) ::
    .ite (.lt (.literal max128) (.localVar "_verity_slice_tmp_1"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_2" (.sub (.literal max128) (.localVar "_verity_slice_tmp_1"))] ::
    brYesAt 4 3 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4copyNum : brYesAt 4 3 =
    .letVar "_verity_slice_tmp_4" (.localVar "_verity_slice_tmp_2") :: brYesAt 4 4 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4subDen : brYesAt 4 4 =
    .letVar "_verity_slice_tmp_3" (.literal 0) ::
    .ite (.lt (.literal max128) (.localVar "_lastLossFactor"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_3" (.sub (.literal max128) (.localVar "_lastLossFactor"))] ::
    brYesAt 4 6 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4copyDen : brYesAt 4 6 =
    .letVar "_verity_slice_tmp_5" (.localVar "_verity_slice_tmp_3") :: brYesAt 4 7 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4mul : brYesAt 4 7 =
    .letVar "_verity_slice_tmp_6" (.literal 0) ::
    .ite (.eq (.localVar "_credit") (.literal 0))
      [.assignVar "_verity_slice_tmp_6" (.mul (.localVar "_credit") (.localVar "_verity_slice_tmp_4"))]
      [.ite (.eq (.div (.mul (.localVar "_credit") (.localVar "_verity_slice_tmp_4")) (.localVar "_credit"))
          (.localVar "_verity_slice_tmp_4"))
        [.assignVar "_verity_slice_tmp_6" (.mul (.localVar "_credit") (.localVar "_verity_slice_tmp_4"))]
        [.panic .arithmeticOverflow]] ::
    brYesAt 4 9 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4copyProd : brYesAt 4 9 =
    .letVar "_verity_slice_tmp_7" (.localVar "_verity_slice_tmp_6") :: brYesAt 4 10 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br4div : brYesAt 4 10 =
    .letVar "_verity_slice_tmp_8" (.literal 0) ::
    .ite (.eq (.localVar "_verity_slice_tmp_5") (.literal 0))
      [.panic .divisionByZero]
      [.assignVar "_verity_slice_tmp_8"
        (.div (.localVar "_verity_slice_tmp_7") (.localVar "_verity_slice_tmp_5"))] ::
    brYesAt 4 12 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

/-- Local lookup after binding a different name. -/
theorem lookup_skip {env : Env} {name key : String} {v x : Nat}
    (h : name ≠ key) (hk : lookupValue env key = x) :
    lookupValue (bindValue env name v) key = x := by
  rw [lookup_bind_other env name key v h, hk]

theorem lookup_here {env : Env} {name : String} {v : Nat} :
    lookupValue (bindValue env name v) name = v :=
  lookup_bind_same env name v

/-- `postSlashCredit` when `lastLoss < 2^128 - 1`, starting after the loss factor is loaded. -/
theorem run_psc_yes
    (o : DenoteOracle) (s : DenoteState) (credit lastLoss loss : Nat)
    (hC : lookupValue s.bindings "_credit" = credit)
    (hL : lookupValue s.bindings "_lastLossFactor" = lastLoss)
    (hM : lookupValue s.bindings "_verity_slice_tmp_1" = loss)
    (hc : credit ≤ max128) (hl : lastLoss ≤ max128) (hm : loss ≤ max128)
    (hlt : lastLoss < max128) (hle : lastLoss ≤ loss) :
    ∃ t, execStmtList o fields s (brYesAt 4 1) = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_9" =
        credit * (max128 - loss) / (max128 - lastLoss) ∧
      lookupValue t.bindings "_credit" = credit ∧
      lookupValue t.bindings "_lastLossFactor" = lastLoss ∧
      t.world = s.world := by
  let num := max128 - loss
  let den := max128 - lastLoss
  let prod := credit * num
  let quot := prod / den
  have hnum_le : num ≤ max128 := by simp [num]
  have hden_pos : den ≠ 0 := by unfold den; omega
  have hden_le : den ≤ max128 := by simp [den]
  have hprod : prod < Uint256.modulus := by
    simpa [prod, num] using mul128_lt hc hnum_le
  have hcredM : credit < Uint256.modulus := lt_of_le_of_lt hc max128_lt
  have hlossM : loss < Uint256.modulus := lt_of_le_of_lt hm max128_lt
  have hlastM : lastLoss < Uint256.modulus := lt_of_le_of_lt hl max128_lt
  let sNum := {s with bindings := bindValue s.bindings "_verity_slice_tmp_2" num}
  have hstep1 : execStmtList o fields s (brYesAt 4 1) =
      execStmtList o fields sNum (brYesAt 4 3) := by
    rw [br4subNum]
    apply go_checked_sub
    · exact eval_lit normalize_max
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hM]
    · exact max128_lt
    · exact hlossM
    · exact hm
    · simp [sNum, num]
  -- keep the main goal intact until the steps are chained
  let sNum' := {sNum with bindings := bindValue sNum.bindings "_verity_slice_tmp_4" num}
  let sNum' := {sNum with bindings := bindValue sNum.bindings "_verity_slice_tmp_4" num}
  have hstep2 : execStmtList o fields sNum (brYesAt 4 3) =
      execStmtList o fields sNum' (brYesAt 4 4) := by
    rw [br4copyNum, let_local (lookup_here)]
    simp [sNum']
  let sDen := {sNum' with bindings := bindValue sNum'.bindings "_verity_slice_tmp_3" den}
  have hL2 : lookupValue sNum'.bindings "_lastLossFactor" = lastLoss := by
    simp only [sNum', sNum]
    exact lookup_skip (by decide) (lookup_skip (by decide) hL)
  have hstep3 : execStmtList o fields sNum' (brYesAt 4 4) =
      execStmtList o fields sDen (brYesAt 4 6) := by
    rw [br4subDen]
    apply go_checked_sub
    · exact eval_lit normalize_max
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hL2]
    · exact max128_lt
    · exact hlastM
    · exact hl
    · simp [sDen, den]
  let sDen' := {sDen with bindings := bindValue sDen.bindings "_verity_slice_tmp_5" den}
  let sDen' := {sDen with bindings := bindValue sDen.bindings "_verity_slice_tmp_5" den}
  have hstep4 : execStmtList o fields sDen (brYesAt 4 6) =
      execStmtList o fields sDen' (brYesAt 4 7) := by
    rw [br4copyDen, let_local (lookup_here)]
    simp [sDen']
  let sProd := {sDen' with bindings := bindValue sDen'.bindings "_verity_slice_tmp_6" prod}
  have hC3 : lookupValue sDen'.bindings "_credit" = credit := by
    simp only [sDen', sDen, sNum', sNum]
    exact lookup_skip (by decide) (lookup_skip (by decide)
      (lookup_skip (by decide) (lookup_skip (by decide) hC)))
  have hNum3 : lookupValue sDen'.bindings "_verity_slice_tmp_4" = num := by
    simp only [sDen', sDen, sNum', sNum]
    exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_here))
  have hstep5 : execStmtList o fields sDen' (brYesAt 4 7) =
      execStmtList o fields sProd (brYesAt 4 9) := by
    rw [br4mul]
    apply go_checked_mul
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hC3]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hNum3]
    · exact hcredM
    · exact lt_of_le_of_lt hnum_le max128_lt
    · exact hprod
    · simp [sProd, prod]
  let sProd' := {sProd with bindings := bindValue sProd.bindings "_verity_slice_tmp_7" prod}
  let sProd' := {sProd with bindings := bindValue sProd.bindings "_verity_slice_tmp_7" prod}
  have hstep6 : execStmtList o fields sProd (brYesAt 4 9) =
      execStmtList o fields sProd' (brYesAt 4 10) := by
    rw [br4copyProd, let_local (lookup_here)]
    simp only [sProd']
  let sQuot := {sProd' with bindings := bindValue sProd'.bindings "_verity_slice_tmp_8" quot}
  have hProd4 : lookupValue sProd'.bindings "_verity_slice_tmp_7" = prod := by
    simp only [sProd']; exact lookup_here
  have hDen4 : lookupValue sProd'.bindings "_verity_slice_tmp_5" = den := by
    simp only [sProd', sProd, sDen', sDen]
    exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_here))
  have hstep7 : execStmtList o fields sProd' (brYesAt 4 10) =
      execStmtList o fields sQuot (brYesAt 4 12) := by
    rw [br4div]
    apply go_checked_div
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hProd4]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hDen4]
    · exact hprod
    · exact lt_of_le_of_lt hden_le max128_lt
    · exact hden_pos
    · simp [sQuot, quot]
  let sDone := {sQuot with bindings := bindValue sQuot.bindings "_verity_slice_tmp_9" quot}
  let sDone := {sQuot with bindings := bindValue sQuot.bindings "_verity_slice_tmp_9" quot}
  have hstep8 : execStmtList o fields sQuot (brYesAt 4 12) = .continue sDone := by
    rw [br4y12]
    apply assign_local (lookup_here)
    rw [execStmtList.eq_1]
  refine ⟨sDone, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans
      (hstep5.trans (hstep6.trans (hstep7.trans hstep8)))))))
  · simp only [sDone, quot, prod, num, den]; exact lookup_here
  · simp only [sDone, sQuot, sProd', sProd, sDen', sDen, sNum', sNum]
    exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
      (lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
        (lookup_skip (by decide) (lookup_skip (by decide) hC)))))))
  · simp only [sDone, sQuot, sProd', sProd, sDen', sDen, sNum', sNum]
    exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
      (lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
        (lookup_skip (by decide) (lookup_skip (by decide) hL)))))))
  · rfl

theorem shape6 : at_ 6 =
    .letVar "_pendingFee" (.structMember2 "position" (.param "id") (.param "user") "pendingFee") :: at_ 7 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape7 : at_ 7 =
    .letVar "_verity_slice_tmp_10" (.gt (.localVar "_credit") (.literal 0)) :: at_ 8 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape8 : at_ 8 = .letVar "_verity_slice_tmp_22" (.literal 0) :: at_ 9 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape9 : at_ 9 =
    .ite (.localVar "_verity_slice_tmp_10") (brYes 9) (brNo 9) :: at_ 10 := by
  unfold at_ brYes brNo skip body functionBody functionBody.go; rfl

theorem shape10 : at_ 10 =
    .letVar "postSlashPendingFee" (.localVar "_verity_slice_tmp_22") :: at_ 11 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape11 : at_ 11 =
    .letVar "accrualEnd"
      (.bitXor .blockTimestamp
        (.mul (.bitXor .blockTimestamp (.param "market_maturity"))
          (.lt (.param "market_maturity") .blockTimestamp))) :: at_ 12 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape12 : at_ 12 =
    .letVar "_lastAccrual"
      (.structMember2 "position" (.param "id") (.param "user") "lastAccrual") :: at_ 13 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem br9head : brYes 9 = .letVar "_verity_slice_tmp_11" (.literal 0) :: brYesAt 9 1 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem br9no : brNo 9 = [.assignVar "_verity_slice_tmp_22" (.literal 0)] := by
  unfold brNo at_ skip body functionBody functionBody.go; rfl

theorem pspDiff : brYes 9 =
    .letVar "_verity_slice_tmp_11" (.literal 0) ::
    .ite (.lt (.localVar "_credit") (.localVar "postSlashCredit"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_11"
        (.sub (.localVar "_credit") (.localVar "postSlashCredit"))] ::
    brYesAt 9 2 := by
  unfold brYes brYesAt at_ skip body functionBody functionBody.go; rfl

theorem pspCopyDiff : brYesAt 9 2 =
    .letVar "_verity_slice_tmp_12" (.localVar "_verity_slice_tmp_11") :: brYesAt 9 3 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspMul : brYesAt 9 3 =
    .letVar "_verity_slice_tmp_13" (.literal 0) ::
    .ite (.eq (.localVar "_pendingFee") (.literal 0))
      [.assignVar "_verity_slice_tmp_13"
        (.mul (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_12"))]
      [.ite (.eq
          (.div (.mul (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_12")) (.localVar "_pendingFee"))
          (.localVar "_verity_slice_tmp_12"))
        [.assignVar "_verity_slice_tmp_13"
          (.mul (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_12"))]
        [.panic .arithmeticOverflow]] ::
    brYesAt 9 5 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspCopyMul : brYesAt 9 5 =
    .letVar "_verity_slice_tmp_15" (.localVar "_verity_slice_tmp_13") :: brYesAt 9 6 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspSub1 : brYesAt 9 6 =
    .letVar "_verity_slice_tmp_14" (.literal 0) ::
    .ite (.lt (.localVar "_credit") (.literal 1))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_14" (.sub (.localVar "_credit") (.literal 1))] ::
    brYesAt 9 8 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspCopy1 : brYesAt 9 8 =
    .letVar "_verity_slice_tmp_16" (.localVar "_verity_slice_tmp_14") :: brYesAt 9 9 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspAdd : brYesAt 9 9 =
    .letVar "_verity_slice_tmp_17" (.literal 0) ::
    .ite (.lt (.add (.localVar "_verity_slice_tmp_15") (.localVar "_verity_slice_tmp_16"))
        (.localVar "_verity_slice_tmp_15"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_17"
        (.add (.localVar "_verity_slice_tmp_15") (.localVar "_verity_slice_tmp_16"))] ::
    brYesAt 9 11 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspCopyAdd : brYesAt 9 11 =
    .letVar "_verity_slice_tmp_18" (.localVar "_verity_slice_tmp_17") :: brYesAt 9 12 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspDiv : brYesAt 9 12 =
    .letVar "_verity_slice_tmp_19" (.literal 0) ::
    .ite (.eq (.localVar "_credit") (.literal 0))
      [.panic .divisionByZero]
      [.assignVar "_verity_slice_tmp_19"
        (.div (.localVar "_verity_slice_tmp_18") (.localVar "_credit"))] ::
    brYesAt 9 14 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspCopyDiv : brYesAt 9 14 =
    .letVar "_verity_slice_tmp_20" (.localVar "_verity_slice_tmp_19") :: brYesAt 9 15 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspSubP : brYesAt 9 15 =
    .letVar "_verity_slice_tmp_21" (.literal 0) ::
    .ite (.lt (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_21"
        (.sub (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20"))] ::
    brYesAt 9 17 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem pspAssign : brYesAt 9 17 =
    [.assignVar "_verity_slice_tmp_22" (.localVar "_verity_slice_tmp_21")] := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem word_one : wordNormalize 1 = 1 :=
  wordNormalize_of_lt (by decide)

/-- Pending fee after slashing, when credit is positive. -/
theorem run_psp_yes
    (o : DenoteOracle) (s : DenoteState) (credit pending psc : Nat)
    (hC : lookupValue s.bindings "_credit" = credit)
    (hP : lookupValue s.bindings "_pendingFee" = pending)
    (hS : lookupValue s.bindings "postSlashCredit" = psc)
    (hc : credit ≤ max128) (hp : pending ≤ max128) (hpsc : psc ≤ credit)
    (hpos : 0 < credit) :
    ∃ t, execStmtList o fields s (brYes 9) = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_22" =
        pending - (pending * (credit - psc) + (credit - 1)) / credit ∧
      lookupValue t.bindings "_credit" = credit ∧
      lookupValue t.bindings "_pendingFee" = pending ∧
      lookupValue t.bindings "postSlashCredit" = psc ∧
      t.world = s.world := by
  let diff := credit - psc
  let prod := pending * diff
  let cm1 := credit - 1
  let sum := prod + cm1
  let quot := sum / credit
  let psp := pending - quot
  have hdiff_le : diff ≤ max128 := by simp [diff]; omega
  have hcredM : credit < Uint256.modulus := lt_of_le_of_lt hc max128_lt
  have hpendM : pending < Uint256.modulus := lt_of_le_of_lt hp max128_lt
  have hprod : prod < Uint256.modulus := by simpa [prod] using mul128_lt hp hdiff_le
  have hcm1 : cm1 ≤ max128 := by simp [cm1]; omega
  have hsum : sum < Uint256.modulus := by
    simpa [sum, prod, diff, cm1] using mulDivUp_sum_lt hp hdiff_le hc
  have hquot : quot ≤ pending := by
    simpa [quot, sum, prod, diff, cm1] using postSlashPending_quot_le hpos psc
  let sDiff := {s with bindings := bindValue s.bindings "_verity_slice_tmp_11" diff}
  have h1 : execStmtList o fields s (brYes 9) = execStmtList o fields sDiff (brYesAt 9 2) := by
    rw [pspDiff]
    apply go_checked_sub
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hC]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hS]
    · exact hcredM
    · exact lt_of_le_of_lt (le_trans hpsc hc) max128_lt
    · exact hpsc
    · simp [sDiff, diff]
  let sDiff' := {sDiff with bindings := bindValue sDiff.bindings "_verity_slice_tmp_12" diff}
  have hC1 : lookupValue sDiff'.bindings "_credit" = credit := by
    simp only [sDiff', sDiff]; exact lookup_skip (by decide) (lookup_skip (by decide) hC)
  have hP1 : lookupValue sDiff'.bindings "_pendingFee" = pending := by
    simp only [sDiff', sDiff]; exact lookup_skip (by decide) (lookup_skip (by decide) hP)
  have hS1 : lookupValue sDiff'.bindings "postSlashCredit" = psc := by
    simp only [sDiff', sDiff]; exact lookup_skip (by decide) (lookup_skip (by decide) hS)
  have hD1 : lookupValue sDiff'.bindings "_verity_slice_tmp_12" = diff := by
    simp only [sDiff']; exact lookup_here
  have h2 : execStmtList o fields sDiff (brYesAt 9 2) =
      execStmtList o fields sDiff' (brYesAt 9 3) := by
    rw [pspCopyDiff, let_local (lookup_here)]; simp only [sDiff']
  let sProd := {sDiff' with bindings := bindValue sDiff'.bindings "_verity_slice_tmp_13" prod}
  have h3 : execStmtList o fields sDiff' (brYesAt 9 3) =
      execStmtList o fields sProd (brYesAt 9 5) := by
    rw [pspMul]
    apply go_checked_mul
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hP1]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hD1]
    · exact hpendM
    · exact lt_of_le_of_lt hdiff_le max128_lt
    · exact hprod
    · simp [sProd, prod]
  let sProd' := {sProd with bindings := bindValue sProd.bindings "_verity_slice_tmp_15" prod}
  have hC2 : lookupValue sProd'.bindings "_credit" = credit := by
    simp only [sProd', sProd]; exact lookup_skip (by decide) (lookup_skip (by decide) hC1)
  have hP2 : lookupValue sProd'.bindings "_pendingFee" = pending := by
    simp only [sProd', sProd]; exact lookup_skip (by decide) (lookup_skip (by decide) hP1)
  have hS2 : lookupValue sProd'.bindings "postSlashCredit" = psc := by
    simp only [sProd', sProd]; exact lookup_skip (by decide) (lookup_skip (by decide) hS1)
  have h4 : execStmtList o fields sProd (brYesAt 9 5) =
      execStmtList o fields sProd' (brYesAt 9 6) := by
    rw [pspCopyMul, let_local (lookup_here)]; simp only [sProd']
  let sOne := {sProd' with bindings := bindValue sProd'.bindings "_verity_slice_tmp_14" cm1}
  have h5 : execStmtList o fields sProd' (brYesAt 9 6) =
      execStmtList o fields sOne (brYesAt 9 8) := by
    rw [pspSub1]
    apply go_checked_sub
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hC2]
    · exact eval_lit word_one
    · exact hcredM
    · decide
    · omega
    · simp [sOne, cm1]
  let sOne' := {sOne with bindings := bindValue sOne.bindings "_verity_slice_tmp_16" cm1}
  have hMul2 : lookupValue sOne'.bindings "_verity_slice_tmp_15" = prod := by
    simp only [sOne', sOne]
    exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_here))
  have hOne2 : lookupValue sOne'.bindings "_verity_slice_tmp_16" = cm1 := by
    simp only [sOne']; exact lookup_here
  have hC3 : lookupValue sOne'.bindings "_credit" = credit := by
    simp only [sOne', sOne]; exact lookup_skip (by decide) (lookup_skip (by decide) hC2)
  have hP3 : lookupValue sOne'.bindings "_pendingFee" = pending := by
    simp only [sOne', sOne]; exact lookup_skip (by decide) (lookup_skip (by decide) hP2)
  have hS3 : lookupValue sOne'.bindings "postSlashCredit" = psc := by
    simp only [sOne', sOne]; exact lookup_skip (by decide) (lookup_skip (by decide) hS2)
  have h6 : execStmtList o fields sOne (brYesAt 9 8) =
      execStmtList o fields sOne' (brYesAt 9 9) := by
    rw [pspCopy1, let_local (lookup_here)]; simp only [sOne']
  let sSum := {sOne' with bindings := bindValue sOne'.bindings "_verity_slice_tmp_17" sum}
  have h7 : execStmtList o fields sOne' (brYesAt 9 9) =
      execStmtList o fields sSum (brYesAt 9 11) := by
    rw [pspAdd]
    apply go_checked_add
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hMul2]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hOne2]
    · exact hprod
    · exact lt_of_le_of_lt hcm1 max128_lt
    · exact hsum
    · simp [sSum, sum]
  let sSum' := {sSum with bindings := bindValue sSum.bindings "_verity_slice_tmp_18" sum}
  have hC4 : lookupValue sSum'.bindings "_credit" = credit := by
    simp only [sSum', sSum]; exact lookup_skip (by decide) (lookup_skip (by decide) hC3)
  have hP4 : lookupValue sSum'.bindings "_pendingFee" = pending := by
    simp only [sSum', sSum]; exact lookup_skip (by decide) (lookup_skip (by decide) hP3)
  have hS4 : lookupValue sSum'.bindings "postSlashCredit" = psc := by
    simp only [sSum', sSum]; exact lookup_skip (by decide) (lookup_skip (by decide) hS3)
  have h8 : execStmtList o fields sSum (brYesAt 9 11) =
      execStmtList o fields sSum' (brYesAt 9 12) := by
    rw [pspCopyAdd, let_local (lookup_here)]; simp only [sSum']
  let sQuot := {sSum' with bindings := bindValue sSum'.bindings "_verity_slice_tmp_19" quot}
  have hSum4 : lookupValue sSum'.bindings "_verity_slice_tmp_18" = sum := by
    simp only [sSum']; exact lookup_here
  have h9 : execStmtList o fields sSum' (brYesAt 9 12) =
      execStmtList o fields sQuot (brYesAt 9 14) := by
    rw [pspDiv]
    apply go_checked_div
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hSum4]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hC4]
    · exact hsum
    · exact hcredM
    · omega
    · simp [sQuot, quot]
  let sQuot' := {sQuot with bindings := bindValue sQuot.bindings "_verity_slice_tmp_20" quot}
  have hP5 : lookupValue sQuot'.bindings "_pendingFee" = pending := by
    simp only [sQuot', sQuot]; exact lookup_skip (by decide) (lookup_skip (by decide) hP4)
  have hQ5 : lookupValue sQuot'.bindings "_verity_slice_tmp_20" = quot := by
    simp only [sQuot']; exact lookup_here
  have hC5 : lookupValue sQuot'.bindings "_credit" = credit := by
    simp only [sQuot', sQuot]; exact lookup_skip (by decide) (lookup_skip (by decide) hC4)
  have hS5 : lookupValue sQuot'.bindings "postSlashCredit" = psc := by
    simp only [sQuot', sQuot]; exact lookup_skip (by decide) (lookup_skip (by decide) hS4)
  have h10 : execStmtList o fields sQuot (brYesAt 9 14) =
      execStmtList o fields sQuot' (brYesAt 9 15) := by
    rw [pspCopyDiv, let_local (lookup_here)]; simp only [sQuot']
  let sPsp := {sQuot' with bindings := bindValue sQuot'.bindings "_verity_slice_tmp_21" psp}
  have h11 : execStmtList o fields sQuot' (brYesAt 9 15) =
      execStmtList o fields sPsp (brYesAt 9 17) := by
    rw [pspSubP]
    apply go_checked_sub
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hP5]
    · rw [evalExpr_localVar_arm, lookup_skip (by decide) hQ5]
    · exact hpendM
    · exact lt_of_le_of_lt hquot hpendM
    · exact hquot
    · simp [sPsp, psp]
  let sDone := {sPsp with bindings := bindValue sPsp.bindings "_verity_slice_tmp_22" psp}
  have h12 : execStmtList o fields sPsp (brYesAt 9 17) = .continue sDone := by
    rw [pspAssign]
    apply assign_local (lookup_here)
    rw [execStmtList.eq_1]
  refine ⟨sDone, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans
      (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans h12)))))))))))
  · simp [sDone, psp, quot, sum, prod, diff, cm1, lookup_bind_same]
  · simp only [sDone, sPsp]; exact lookup_skip (by decide) (lookup_skip (by decide) hC5)
  · simp only [sDone, sPsp]; exact lookup_skip (by decide) (lookup_skip (by decide) hP5)
  · simp only [sDone, sPsp]; exact lookup_skip (by decide) (lookup_skip (by decide) hS5)
  · rfl

def pspN (credit pending psc : Nat) : Nat :=
  if credit = 0 then 0
  else pending - (pending * (credit - psc) + (credit - 1)) / credit

theorem at0 : at_ 0 = body := by
  unfold at_ skip; rfl

/-- Execute through `postSlashCredit`. -/
theorem run_to_psc
    (o : DenoteOracle) (w : Verity.ContractState) (maturity : Uint256)
    (id : BytesN 32) (user : Address) :
    let s0 : DenoteState :=
      { world := w, bindings := [("market_maturity", maturity.val), ("id", id.val), ("user", user.val)] }
    let C := (midnight.position.credit o w id user).val
    let L := (midnight.position.lastLossFactor o w id user).val
    let M := (midnight.marketState.lossFactor o w id).val
    ∀ (_hLM : L ≤ M),
    ∃ t, execStmtList o fields s0 (at_ 0) = execStmtList o fields t (at_ 6) ∧
      lookupValue t.bindings "postSlashCredit" = postSlashCreditN C L M ∧
      lookupValue t.bindings "_credit" = C ∧
      lookupValue t.bindings "_lastLossFactor" = L ∧
      lookupValue t.bindings "market_maturity" = maturity.val ∧
      lookupValue t.bindings "id" = id.val ∧
      lookupValue t.bindings "user" = user.val ∧
      t.world = w := by
  intro s0 C L M hLM
  have hc : C ≤ max128 := uint128_le_max _
  have hl : L ≤ max128 := uint128_le_max _
  have hm : M ≤ max128 := uint128_le_max _
  have hMread : readMember o midnight.model w "marketState" [id.val] "lossFactor" = M := by
    simp [M, midnight.marketState.lossFactor_val]
  let sL :=
    { s0 with bindings := bindValue (bindValue s0.bindings "_credit" C) "_lastLossFactor" L }
  have hreads : execStmtList o fields s0 (at_ 0) = execStmtList o fields sL (at_ 2) := by
    simpa [s0, C, L, sL] using step_reads o w maturity id user
  let bit := boolWord (decide (L < max128))
  let sBit := {sL with bindings := bindValue sL.bindings "_verity_slice_tmp_0" bit}
  have hbit : execStmtList o fields sL (at_ 2) = execStmtList o fields sBit (at_ 3) := by
    rw [shape2, exec_let_cons, evalExpr_lt_arm, evalExpr_localVar_arm, eval_lit normalize_max]
    simp only [sL, lookup_bind_same, bind, pure]
    simp [sBit, sL, bit]
  let sZero := {sBit with bindings := bindValue sBit.bindings "_verity_slice_tmp_9" 0}
  have hzero : execStmtList o fields sBit (at_ 3) = execStmtList o fields sZero (at_ 4) := by
    rw [shape3, let_literal wordNormalize_zero]; simp [sZero]
  by_cases hlt : L < max128
  · have hflag : lookupValue sZero.bindings "_verity_slice_tmp_0" = 1 := by
      dsimp [sZero, sBit]
      rw [lookup_bind_other (bindValue sL.bindings "_verity_slice_tmp_0" bit)
        "_verity_slice_tmp_9" "_verity_slice_tmp_0" 0 (by decide), lookup_bind_same]
      simp [bit, decide_true_of hlt, boolWord_true]
    let sLoss := {sZero with bindings := bindValue sZero.bindings "_verity_slice_tmp_1" M}
    have hloss : execStmtList o fields sZero (brYes 4) =
        execStmtList o fields sLoss (brYesAt 4 1) := by
      rw [br4y0, exec_let_cons, evalExpr_structMember_param (h := mkt_ok)]
      simp [sZero, sBit, sL, s0, lookupValue, bindValue, List.filter, hMread, sLoss]
    have hC0 : lookupValue sLoss.bindings "_credit" = C := by
      simp only [sLoss, sZero, sBit, sL]
      exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
        (lookup_skip (by decide) (lookup_bind_same _ _ _))))
    have hL0 : lookupValue sLoss.bindings "_lastLossFactor" = L := by
      simp only [sLoss, sZero, sBit, sL]
      exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide) (lookup_here)))
    have hM0 : lookupValue sLoss.bindings "_verity_slice_tmp_1" = M := by
      simp only [sLoss]; exact lookup_here
    obtain ⟨t1, ht1, hpsc, hC1, hL1, hw1⟩ :=
      run_psc_yes o sLoss C L M hC0 hL0 hM0 hc hl hm hlt hLM
    have hbranch : execStmtList o fields sZero (brYes 4) = .continue t1 := ht1 ▸ hloss
    have hite : execStmtList o fields sZero (at_ 4) = execStmtList o fields t1 (at_ 5) := by
      rw [shape4]; exact go_ite_one hflag hbranch rfl
    let sPsc := {t1 with bindings := bindValue t1.bindings "postSlashCredit" (C * (max128 - M) / (max128 - L))}
    have hlet : execStmtList o fields t1 (at_ 5) = execStmtList o fields sPsc (at_ 6) := by
      rw [shape5, let_local hpsc]; simp [sPsc, hlt]
    refine ⟨sPsc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hreads.trans (hbit.trans (hzero.trans (hite.trans hlet))))
    · simp [sPsc, postSlashCreditN, hlt, lookup_bind_same]
    · simp only [sPsc]; exact lookup_skip (by decide) hC1
    · simp only [sPsc]; exact lookup_skip (by decide) hL1
    · have hp : prefixList ["market_maturity"] (brYes 4) = true := by
        unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
      have hkeep := list_frame o fields sZero (brYes 4) ["market_maturity"] hp
      have hmat1 : lookupValue t1.bindings "market_maturity" =
          lookupValue sZero.bindings "market_maturity" := by
        have hf := hkeep
        simp [Frame, hbranch] at hf
        exact hf.2
      have hmat0 : lookupValue sZero.bindings "market_maturity" = maturity.val := by
        dsimp [sZero, sBit, sL, s0]
        rw [lookup_bind_other _ "_verity_slice_tmp_9" "market_maturity" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_0" "market_maturity" _ (by decide),
          lookup_bind_other _ "_lastLossFactor" "market_maturity" _ (by decide),
          lookup_bind_other _ "_credit" "market_maturity" _ (by decide)]
        simp [lookupValue]
      rw [lookup_bind_other _ "postSlashCredit" "market_maturity" _ (by decide), hmat1, hmat0]
    · have hp : prefixList ["id"] (brYes 4) = true := by
        unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
      have hkeep := list_frame o fields sZero (brYes 4) ["id"] hp
      have hid1 : lookupValue t1.bindings "id" = lookupValue sZero.bindings "id" := by
        have hf := hkeep
        simp [Frame, hbranch] at hf
        exact hf.2
      have hid0 : lookupValue sZero.bindings "id" = id.val := by
        dsimp [sZero, sBit, sL, s0]
        rw [lookup_bind_other _ "_verity_slice_tmp_9" "id" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_0" "id" _ (by decide),
          lookup_bind_other _ "_lastLossFactor" "id" _ (by decide),
          lookup_bind_other _ "_credit" "id" _ (by decide)]
        simp [lookupValue]
      rw [lookup_bind_other _ "postSlashCredit" "id" _ (by decide), hid1, hid0]
    · have hp : prefixList ["user"] (brYes 4) = true := by
        unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
      have hkeep := list_frame o fields sZero (brYes 4) ["user"] hp
      have hu1 : lookupValue t1.bindings "user" = lookupValue sZero.bindings "user" := by
        have hf := hkeep
        simp [Frame, hbranch] at hf
        exact hf.2
      have hu0 : lookupValue sZero.bindings "user" = user.val := by
        dsimp [sZero, sBit, sL, s0]
        rw [lookup_bind_other _ "_verity_slice_tmp_9" "user" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_0" "user" _ (by decide),
          lookup_bind_other _ "_lastLossFactor" "user" _ (by decide),
          lookup_bind_other _ "_credit" "user" _ (by decide)]
        simp [lookupValue]
      rw [lookup_bind_other _ "postSlashCredit" "user" _ (by decide), hu1, hu0]
    · exact hw1 ▸ rfl
  · have hflag : lookupValue sZero.bindings "_verity_slice_tmp_0" = 0 := by
      dsimp [sZero, sBit]
      rw [lookup_bind_other (bindValue sL.bindings "_verity_slice_tmp_0" bit)
        "_verity_slice_tmp_9" "_verity_slice_tmp_0" 0 (by decide), lookup_bind_same]
      simp [bit, decide_false_of_not hlt, boolWord_false]
    have hLmax : L = max128 := by omega
    have hMmax : M = max128 := by omega
    let sNo := {sZero with bindings := bindValue sZero.bindings "_verity_slice_tmp_9" 0}
    have hbranch : execStmtList o fields sZero (brNo 4) = .continue sNo := by
      rw [br4n]; apply assign_literal wordNormalize_zero; rw [execStmtList.eq_1]
    have hite : execStmtList o fields sZero (at_ 4) = execStmtList o fields sNo (at_ 5) := by
      rw [shape4]; exact go_ite_zero hflag hbranch rfl
    let sPsc := {sNo with bindings := bindValue sNo.bindings "postSlashCredit" 0}
    have hlet : execStmtList o fields sNo (at_ 5) = execStmtList o fields sPsc (at_ 6) := by
      rw [shape5, let_local (lookup_here)]; simp [sPsc]
    refine ⟨sPsc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hreads.trans (hbit.trans (hzero.trans (hite.trans hlet))))
    · simp [sPsc, postSlashCreditN, hlt, hLmax, lookup_bind_same]
    · simp only [sPsc, sNo, sZero, sBit, sL]
      exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
        (lookup_skip (by decide) (lookup_skip (by decide) (lookup_bind_same _ _ _)))))
    · simp only [sPsc, sNo, sZero, sBit, sL]
      exact lookup_skip (by decide) (lookup_skip (by decide) (lookup_skip (by decide)
        (lookup_skip (by decide) (lookup_here))))
    · dsimp [sPsc, sNo, sZero, sBit, sL, s0]
      rw [lookup_bind_other _ "postSlashCredit" "market_maturity" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_9" "market_maturity" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_9" "market_maturity" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_0" "market_maturity" _ (by decide),
        lookup_bind_other _ "_lastLossFactor" "market_maturity" _ (by decide),
        lookup_bind_other _ "_credit" "market_maturity" _ (by decide)]
      simp [lookupValue]
    · dsimp [sPsc, sNo, sZero, sBit, sL, s0]
      rw [lookup_bind_other _ "postSlashCredit" "id" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_9" "id" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_9" "id" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_0" "id" _ (by decide),
        lookup_bind_other _ "_lastLossFactor" "id" _ (by decide),
        lookup_bind_other _ "_credit" "id" _ (by decide)]
      simp [lookupValue]
    · dsimp [sPsc, sNo, sZero, sBit, sL, s0]
      rw [lookup_bind_other _ "postSlashCredit" "user" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_9" "user" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_9" "user" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_0" "user" _ (by decide),
        lookup_bind_other _ "_lastLossFactor" "user" _ (by decide),
        lookup_bind_other _ "_credit" "user" _ (by decide)]
      simp [lookupValue]
    · rfl

/-- From `postSlashCredit` through `lastAccrual`. -/
theorem run_to_time
    (o : DenoteOracle) (w : Verity.ContractState) (maturity : Uint256)
    (id : BytesN 32) (user : Address)
    (hLM : (midnight.position.lastLossFactor o w id user).val ≤
      (midnight.marketState.lossFactor o w id).val) :
    let C := (midnight.position.credit o w id user).val
    let L := (midnight.position.lastLossFactor o w id user).val
    let Mv := (midnight.marketState.lossFactor o w id).val
    let P := (midnight.position.pendingFee o w id user).val
    let A := (midnight.position.lastAccrual o w id user).val
    let psc := postSlashCreditN C L Mv
    let psp := pspN C P psc
    let ts := w.blockTimestamp.val
    let ae := if maturity.val < ts then maturity.val else ts
    ∃ t, execStmtList o fields
        { world := w, bindings := [("market_maturity", maturity.val), ("id", id.val), ("user", user.val)] } body =
        execStmtList o fields t (at_ 13) ∧
      lookupValue t.bindings "postSlashCredit" = psc ∧
      lookupValue t.bindings "postSlashPendingFee" = psp ∧
      lookupValue t.bindings "accrualEnd" = ae ∧
      lookupValue t.bindings "_lastAccrual" = A ∧
      lookupValue t.bindings "market_maturity" = maturity.val ∧
      lookupValue t.bindings "_credit" = C ∧
      lookupValue t.bindings "_pendingFee" = P ∧
      t.world = w := by
  intro C L Mv P A psc psp ts ae
  have hc : C ≤ max128 := uint128_le_max _
  have hm : Mv ≤ max128 := uint128_le_max _
  have hp : P ≤ max128 := uint128_le_max _
  obtain ⟨t0, hex0, hpsc0, hC0, _hL0, hmat0, hid0, huser0, hw0⟩ :=
    run_to_psc o w maturity id user hLM
  have hPread : readMember o midnight.model w "position" [id.val, user.val] "pendingFee" = P := by
    simp [P, midnight.position.pendingFee_val]
  have hAread : readMember o midnight.model w "position" [id.val, user.val] "lastAccrual" = A := by
    simp [A, midnight.position.lastAccrual_val]
  let sP := {t0 with bindings := bindValue t0.bindings "_pendingFee" P}
  have hpend : execStmtList o fields t0 (at_ 6) = execStmtList o fields sP (at_ 7) := by
    rw [shape6, exec_let_cons, evalExpr_structMember2_param (h := pos_ok "pendingFee" (by simp))]
    rw [hid0, huser0]
    simp [hw0, hPread, sP]
  -- The simp above is optimistic; the lookup of id/user is repaired below if needed.
  let bit := boolWord (decide (0 < C))
  let sBit := {sP with bindings := bindValue sP.bindings "_verity_slice_tmp_10" bit}
  have hbit : execStmtList o fields sP (at_ 7) = execStmtList o fields sBit (at_ 8) := by
    rw [shape7, exec_let_cons, evalExpr_gt_arm, evalExpr_localVar_arm, eval_lit wordNormalize_zero]
    have hcl : lookupValue sP.bindings "_credit" = C := by
      dsimp [sP]
      rw [lookup_bind_other _ "_pendingFee" "_credit" _ (by decide)]
      exact hC0
    simp [hcl, bind, pure, sBit, bit]
  let sZ := {sBit with bindings := bindValue sBit.bindings "_verity_slice_tmp_22" 0}
  have hz : execStmtList o fields sBit (at_ 8) = execStmtList o fields sZ (at_ 9) := by
    rw [shape8, let_literal wordNormalize_zero]; simp [sZ]
  have hC : lookupValue sZ.bindings "_credit" = C := by
    dsimp [sZ, sBit, sP]
    rw [lookup_bind_other _ "_verity_slice_tmp_22" "_credit" _ (by decide),
      lookup_bind_other _ "_verity_slice_tmp_10" "_credit" _ (by decide),
      lookup_bind_other _ "_pendingFee" "_credit" _ (by decide)]
    exact hC0
  have hS : lookupValue sZ.bindings "postSlashCredit" = psc := by
    dsimp [sZ, sBit, sP, psc]
    rw [lookup_bind_other _ "_verity_slice_tmp_22" "postSlashCredit" _ (by decide),
      lookup_bind_other _ "_verity_slice_tmp_10" "postSlashCredit" _ (by decide),
      lookup_bind_other _ "_pendingFee" "postSlashCredit" _ (by decide)]
    exact hpsc0
  have hPend : lookupValue sZ.bindings "_pendingFee" = P := by
    dsimp [sZ, sBit, sP]
    rw [lookup_bind_other _ "_verity_slice_tmp_22" "_pendingFee" _ (by decide),
      lookup_bind_other _ "_verity_slice_tmp_10" "_pendingFee" _ (by decide), lookup_bind_same]
  have hMat : lookupValue sZ.bindings "market_maturity" = maturity.val := by
    dsimp [sZ, sBit, sP]
    rw [lookup_bind_other _ "_verity_slice_tmp_22" "market_maturity" _ (by decide),
      lookup_bind_other _ "_verity_slice_tmp_10" "market_maturity" _ (by decide),
      lookup_bind_other _ "_pendingFee" "market_maturity" _ (by decide)]
    exact hmat0
  by_cases hzeroC : C = 0
  · have hflag : lookupValue sZ.bindings "_verity_slice_tmp_10" = 0 := by
      dsimp [sZ, sBit, bit]
      rw [lookup_bind_other _ "_verity_slice_tmp_22" "_verity_slice_tmp_10" _ (by decide), lookup_bind_same]
      simp [bit, hzeroC, boolWord_false]
    let sNo := {sZ with bindings := bindValue sZ.bindings "_verity_slice_tmp_22" 0}
    have hbr : execStmtList o fields sZ (brNo 9) = .continue sNo := by
      rw [br9no]; apply assign_literal wordNormalize_zero; rw [execStmtList.eq_1]
    have hite : execStmtList o fields sZ (at_ 9) = execStmtList o fields sNo (at_ 10) := by
      rw [shape9]; exact go_ite_zero hflag hbr rfl
    let sPsp := {sNo with bindings := bindValue sNo.bindings "postSlashPendingFee" 0}
    have hlet : execStmtList o fields sNo (at_ 10) = execStmtList o fields sPsp (at_ 11) := by
      rw [shape10, let_local (lookup_here)]; simp [sPsp]
    -- continue with min and last accrual on sPsp; psp = 0
    have hpsp0 : psp = 0 := by simp [psp, pspN, hzeroC]
    let sAe := {sPsp with bindings := bindValue sPsp.bindings "accrualEnd" ae}
    have hae : execStmtList o fields sPsp (at_ 11) = execStmtList o fields sAe (at_ 12) := by
      rw [shape11, exec_let_cons]
      have hts : sPsp.world.blockTimestamp.val = ts := by
        dsimp [sPsp, sNo, sZ, sBit, sP]
        simp [hw0, ts]
      have hmv : lookupValue sPsp.bindings "market_maturity" = maturity.val := by
        dsimp [sPsp, sNo]
        rw [lookup_bind_other _ "postSlashPendingFee" "market_maturity" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_22" "market_maturity" _ (by decide)]
        exact hMat
      rw [eval_yul_min hts hmv w.blockTimestamp.isLt maturity.isLt]
    let sA := {sAe with bindings := bindValue sAe.bindings "_lastAccrual" A}
    have hlast : execStmtList o fields sAe (at_ 12) = execStmtList o fields sA (at_ 13) := by
      rw [shape12, exec_let_cons, evalExpr_structMember2_param (h := pos_ok "lastAccrual" (by simp))]
      have hid : lookupValue sAe.bindings "id" = id.val := by
        dsimp [sAe, sPsp, sNo, sZ, sBit, sP]
        rw [lookup_bind_other _ "accrualEnd" "id" _ (by decide),
          lookup_bind_other _ "postSlashPendingFee" "id" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_22" "id" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_22" "id" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_10" "id" _ (by decide),
          lookup_bind_other _ "_pendingFee" "id" _ (by decide)]
        exact hid0
      have hu : lookupValue sAe.bindings "user" = user.val := by
        dsimp [sAe, sPsp, sNo, sZ, sBit, sP]
        rw [lookup_bind_other _ "accrualEnd" "user" _ (by decide),
          lookup_bind_other _ "postSlashPendingFee" "user" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_22" "user" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_22" "user" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_10" "user" _ (by decide),
          lookup_bind_other _ "_pendingFee" "user" _ (by decide)]
        exact huser0
      have hwA : sAe.world = w := by
        dsimp [sAe, sPsp, sNo, sZ, sBit, sP]
        simp [hw0]
      rw [hid, hu, hwA, hAread]
      simp [sA, hwA]
    refine ⟨sA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← at0]; exact (hex0.trans (hpend.trans (hbit.trans (hz.trans (hite.trans (hlet.trans (hae.trans hlast)))))))
    · dsimp [sA, sAe, sPsp, sNo]
      rw [lookup_bind_other _ "_lastAccrual" "postSlashCredit" _ (by decide),
        lookup_bind_other _ "accrualEnd" "postSlashCredit" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "postSlashCredit" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_22" "postSlashCredit" _ (by decide)]
      exact hS
    · rw [lookup_bind_other _ "_lastAccrual" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "accrualEnd" "postSlashPendingFee" _ (by decide), lookup_bind_same]
      simp [hpsp0]
    · rw [lookup_bind_other _ "_lastAccrual" "accrualEnd" _ (by decide), lookup_bind_same]
    · rw [lookup_bind_same]
    · dsimp [sA, sAe, sPsp, sNo]
      rw [lookup_bind_other _ "_lastAccrual" "market_maturity" _ (by decide),
        lookup_bind_other _ "accrualEnd" "market_maturity" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "market_maturity" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_22" "market_maturity" _ (by decide)]
      exact hMat
    · dsimp [sA, sAe, sPsp, sNo, sZ, sBit, sP]
      rw [lookup_bind_other _ "_lastAccrual" "_credit" _ (by decide),
        lookup_bind_other _ "accrualEnd" "_credit" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "_credit" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_22" "_credit" _ (by decide)]
      exact hC
    · dsimp [sA, sAe, sPsp, sNo, sZ, sBit]
      rw [lookup_bind_other _ "_lastAccrual" "_pendingFee" _ (by decide),
        lookup_bind_other _ "accrualEnd" "_pendingFee" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "_pendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_22" "_pendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_22" "_pendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_10" "_pendingFee" _ (by decide),
        lookup_bind_same]
    · simp [sA, sAe, sPsp, sNo, sZ, sBit, sP, hw0]
  · have hpos : 0 < C := by omega
    have hflag : lookupValue sZ.bindings "_verity_slice_tmp_10" = 1 := by
      dsimp [sZ, sBit, bit]
      rw [lookup_bind_other _ "_verity_slice_tmp_22" "_verity_slice_tmp_10" _ (by decide), lookup_bind_same]
      simp [bit, hpos, boolWord_true, decide_true_of hpos]
    have hpsc_le : psc ≤ C := by
      dsimp [psc, postSlashCreditN]
      split
      · have hden : 0 < max128 - L := by omega
        have hnum : max128 - Mv ≤ max128 - L := by omega
        exact mul_div_le_self hden hnum
      · exact Nat.zero_le _
    obtain ⟨t1, ht1, hpsp1, hC1, hP1, hS1, hw1⟩ :=
      run_psp_yes o sZ C P psc hC hPend hS hc hp hpsc_le hpos
    have hbr : execStmtList o fields sZ (brYes 9) = .continue t1 := ht1
    have hite : execStmtList o fields sZ (at_ 9) = execStmtList o fields t1 (at_ 10) := by
      rw [shape9]; exact go_ite_one hflag hbr rfl
    let sPsp := {t1 with bindings := bindValue t1.bindings "postSlashPendingFee" (pspN C P psc)}
    have hlet : execStmtList o fields t1 (at_ 10) = execStmtList o fields sPsp (at_ 11) := by
      rw [shape10]
      apply let_local (by
        simpa [psp, pspN, show ¬ C = 0 by omega] using hpsp1)
      simp [sPsp, pspN, show ¬ C = 0 by omega]
    have hmv : lookupValue sPsp.bindings "market_maturity" = maturity.val := by
      have hpfix : prefixList ["market_maturity"] (brYes 9) = true := by
        unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
      have hkeep := list_frame o fields sZ (brYes 9) ["market_maturity"] hpfix
      have h0 : lookupValue t1.bindings "market_maturity" = lookupValue sZ.bindings "market_maturity" := by
        have hf := hkeep
        simp [Frame, hbr] at hf
        exact hf.2
      rw [lookup_bind_other _ "postSlashPendingFee" "market_maturity" _ (by decide), h0, hMat]
    let sAe := {sPsp with bindings := bindValue sPsp.bindings "accrualEnd" ae}
    have hae : execStmtList o fields sPsp (at_ 11) = execStmtList o fields sAe (at_ 12) := by
      rw [shape11, exec_let_cons]
      have hts : sPsp.world.blockTimestamp.val = ts := by
        have : sPsp.world = sZ.world := by simp [sPsp, hw1]
        dsimp [sZ, sBit, sP] at this
        simp [hw0, ts, this]
      rw [eval_yul_min hts hmv w.blockTimestamp.isLt maturity.isLt]
    let sA := {sAe with bindings := bindValue sAe.bindings "_lastAccrual" A}
    have hlast : execStmtList o fields sAe (at_ 12) = execStmtList o fields sA (at_ 13) := by
      rw [shape12, exec_let_cons, evalExpr_structMember2_param (h := pos_ok "lastAccrual" (by simp))]
      have hidZ : lookupValue sZ.bindings "id" = id.val := by
        dsimp [sZ, sBit, sP]
        rw [lookup_bind_other _ "_verity_slice_tmp_22" "id" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_10" "id" _ (by decide),
          lookup_bind_other _ "_pendingFee" "id" _ (by decide)]
        exact hid0
      have huZ : lookupValue sZ.bindings "user" = user.val := by
        dsimp [sZ, sBit, sP]
        rw [lookup_bind_other _ "_verity_slice_tmp_22" "user" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_10" "user" _ (by decide),
          lookup_bind_other _ "_pendingFee" "user" _ (by decide)]
        exact huser0
      have hpid : prefixList ["id"] (brYes 9) = true := by
        unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
      have hpu : prefixList ["user"] (brYes 9) = true := by
        unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
      have hid1 : lookupValue t1.bindings "id" = lookupValue sZ.bindings "id" := by
        have hf := list_frame o fields sZ (brYes 9) ["id"] hpid
        simp [Frame, hbr] at hf
        exact hf.2
      have hu1 : lookupValue t1.bindings "user" = lookupValue sZ.bindings "user" := by
        have hf := list_frame o fields sZ (brYes 9) ["user"] hpu
        simp [Frame, hbr] at hf
        exact hf.2
      have hid : lookupValue sAe.bindings "id" = id.val := by
        rw [lookup_bind_other _ "accrualEnd" "id" _ (by decide),
          lookup_bind_other _ "postSlashPendingFee" "id" _ (by decide), hid1, hidZ]
      have hu : lookupValue sAe.bindings "user" = user.val := by
        rw [lookup_bind_other _ "accrualEnd" "user" _ (by decide),
          lookup_bind_other _ "postSlashPendingFee" "user" _ (by decide), hu1, huZ]
      have hwA : sAe.world = w := by
        have : sAe.world = sZ.world := by simp [sAe, sPsp, hw1]
        dsimp [sZ, sBit, sP] at this
        simp [hw0] at this
        exact this
      rw [hid, hu, hwA, hAread]
      simp [sA, hwA]
    refine ⟨sA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← at0]
      exact (hex0.trans (hpend.trans (hbit.trans (hz.trans (hite.trans (hlet.trans (hae.trans hlast)))))))
    · rw [lookup_bind_other (sAe.bindings) "_lastAccrual" "postSlashCredit" _ (by decide),
        lookup_bind_other _ "accrualEnd" "postSlashCredit" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "postSlashCredit" _ (by decide)]
      simpa [psp, pspN, hpos] using hS1
    ·       rw [lookup_bind_other _ "_lastAccrual" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "accrualEnd" "postSlashPendingFee" _ (by decide), lookup_bind_same]
    · rw [lookup_bind_other _ "_lastAccrual" "accrualEnd" _ (by decide), lookup_bind_same]
    · rw [lookup_bind_same]
    · rw [lookup_bind_other _ "_lastAccrual" "market_maturity" _ (by decide),
        lookup_bind_other _ "accrualEnd" "market_maturity" _ (by decide)]
      exact hmv
    · rw [lookup_bind_other _ "_lastAccrual" "_credit" _ (by decide),
        lookup_bind_other _ "accrualEnd" "_credit" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "_credit" _ (by decide)]
      exact hC1
    · rw [lookup_bind_other _ "_lastAccrual" "_pendingFee" _ (by decide),
        lookup_bind_other _ "accrualEnd" "_pendingFee" _ (by decide),
        lookup_bind_other _ "postSlashPendingFee" "_pendingFee" _ (by decide)]
      exact hP1
    · have : sA.world = sZ.world := by simp [sA, sAe, sPsp, hw1]
      dsimp [sZ, sBit, sP] at this
      simpa [hw0] using this

theorem shape13 : at_ 13 =
    .letVar "_verity_slice_tmp_23"
      (.lt (.localVar "_lastAccrual") (.param "market_maturity")) :: at_ 14 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape14 : at_ 14 = .letVar "_verity_slice_tmp_33" (.literal 0) :: at_ 15 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape15 : at_ 15 =
    .ite (.localVar "_verity_slice_tmp_23") (brYes 15) (brNo 15) :: at_ 16 := by
  unfold at_ brYes brNo skip body functionBody functionBody.go; rfl

theorem shape16 : at_ 16 = .letVar "fee" (.localVar "_verity_slice_tmp_33") :: at_ 17 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape27 : at_ 27 =
    [.returnValues [.localVar "_verity_slice_tmp_37", .localVar "_verity_slice_tmp_41", .localVar "fee"]] := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem br15no : brNo 15 = [.assignVar "_verity_slice_tmp_33" (.literal 0)] := by
  unfold brNo at_ skip body functionBody functionBody.go; rfl

theorem feeSubAe : brYes 15 =
    .letVar "_verity_slice_tmp_24" (.literal 0) ::
    .ite (.lt (.localVar "accrualEnd") (.localVar "_lastAccrual"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_24"
        (.sub (.localVar "accrualEnd") (.localVar "_lastAccrual"))] ::
    brYesAt 15 2 := by
  unfold brYes brYesAt at_ skip body functionBody functionBody.go; rfl

theorem feeCopyD1 : brYesAt 15 2 =
    .letVar "_verity_slice_tmp_26" (.localVar "_verity_slice_tmp_24") :: brYesAt 15 3 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeSubMat : brYes 15 = brYes 15 := rfl

theorem feeSubD2 : brYesAt 15 3 =
    .letVar "_verity_slice_tmp_25" (.literal 0) ::
    .ite (.lt (.param "market_maturity") (.localVar "_lastAccrual"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_25"
        (.sub (.param "market_maturity") (.localVar "_lastAccrual"))] ::
    brYesAt 15 5 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeCopyD2 : brYesAt 15 5 =
    .letVar "_verity_slice_tmp_27" (.localVar "_verity_slice_tmp_25") :: brYesAt 15 6 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeMul : brYesAt 15 6 =
    .letVar "_verity_slice_tmp_28" (.literal 0) ::
    .ite (.eq (.localVar "postSlashPendingFee") (.literal 0))
      [.assignVar "_verity_slice_tmp_28"
        (.mul (.localVar "postSlashPendingFee") (.localVar "_verity_slice_tmp_26"))]
      [.ite (.eq
          (.div (.mul (.localVar "postSlashPendingFee") (.localVar "_verity_slice_tmp_26"))
            (.localVar "postSlashPendingFee"))
          (.localVar "_verity_slice_tmp_26"))
        [.assignVar "_verity_slice_tmp_28"
          (.mul (.localVar "postSlashPendingFee") (.localVar "_verity_slice_tmp_26"))]
        [.panic .arithmeticOverflow]] ::
    brYesAt 15 8 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeMask : brYesAt 15 12 =
    .letVar "_verity_slice_tmp_32"
      (.bitAnd (.localVar "_verity_slice_tmp_31") (.literal max128)) ::
    brYesAt 15 13 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeAssign : brYesAt 15 13 =
    [.assignVar "_verity_slice_tmp_33" (.localVar "_verity_slice_tmp_32")] := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeCopyMul : brYesAt 15 8 =
    .letVar "_verity_slice_tmp_29" (.localVar "_verity_slice_tmp_28") :: brYesAt 15 9 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeDiv : brYesAt 15 9 =
    .letVar "_verity_slice_tmp_30" (.literal 0) ::
    .ite (.eq (.localVar "_verity_slice_tmp_27") (.literal 0))
      [.panic .divisionByZero]
      [.assignVar "_verity_slice_tmp_30"
        (.div (.localVar "_verity_slice_tmp_29") (.localVar "_verity_slice_tmp_27"))] ::
    brYesAt 15 11 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem feeCopyQuot : brYesAt 15 11 =
    .letVar "_verity_slice_tmp_31" (.localVar "_verity_slice_tmp_30") :: brYesAt 15 12 := by
  unfold brYesAt brYes at_ skip body functionBody functionBody.go; rfl

theorem shape17 : at_ 17 =
    .letVar "_verity_slice_tmp_34" (.bitAnd (.localVar "postSlashCredit") (.literal max128)) ::
    at_ 18 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape18 : at_ 18 =
    .letVar "_verity_slice_tmp_35" (.localVar "_verity_slice_tmp_34") :: at_ 19 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape20 : at_ 19 =
    .letVar "_verity_slice_tmp_36" (.literal 0) ::
    .ite (.lt (.localVar "_verity_slice_tmp_35") (.localVar "fee"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_36"
        (.sub (.localVar "_verity_slice_tmp_35") (.localVar "fee"))] ::
    at_ 21 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape21 : at_ 21 =
    .letVar "_verity_slice_tmp_37" (.localVar "_verity_slice_tmp_36") :: at_ 22 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape22 : at_ 22 =
    .letVar "_verity_slice_tmp_38"
      (.bitAnd (.localVar "postSlashPendingFee") (.literal max128)) :: at_ 23 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape23 : at_ 23 =
    .letVar "_verity_slice_tmp_39" (.localVar "_verity_slice_tmp_38") :: at_ 24 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape25 : at_ 24 =
    .letVar "_verity_slice_tmp_40" (.literal 0) ::
    .ite (.lt (.localVar "_verity_slice_tmp_39") (.localVar "fee"))
      [.panic .arithmeticOverflow]
      [.assignVar "_verity_slice_tmp_40"
        (.sub (.localVar "_verity_slice_tmp_39") (.localVar "fee"))] ::
    at_ 26 := by
  unfold at_ skip body functionBody functionBody.go; rfl

theorem shape26 : at_ 26 =
    .letVar "_verity_slice_tmp_41" (.localVar "_verity_slice_tmp_40") :: at_ 27 := by
  unfold at_ skip body functionBody functionBody.go; rfl

/-- Successful accrual returns `psc - fee`, `psp - fee`, and `fee`. -/
theorem suffix_stop
    (o : DenoteOracle) (s : DenoteState) (final : DenoteState)
    (psc psp A mat ts : Nat)
    (hpsc : lookupValue s.bindings "postSlashCredit" = psc)
    (hpsp : lookupValue s.bindings "postSlashPendingFee" = psp)
    (hA : lookupValue s.bindings "_lastAccrual" = A)
    (hmat : lookupValue s.bindings "market_maturity" = mat)
    (hae : lookupValue s.bindings "accrualEnd" = (if mat < ts then mat else ts))
    (hts : s.world.blockTimestamp.val = ts)
    (hpscB : psc ≤ max128) (hpspB : psp ≤ max128)
    (hA128 : A ≤ max128) (hmatM : mat < Uint256.modulus) (htsM : ts < Uint256.modulus)
    (h : execStmtList o fields s (at_ 13) = .stop final) :
    let ae := if mat < ts then mat else ts
    let feeN := if A < mat then psp * (ae - A) / (mat - A) else 0
    (A < mat → A ≤ ae) ∧
    (A < mat → psp * (ae - A) < Uint256.modulus) ∧
    feeN ≤ psc ∧ feeN ≤ psp ∧
    final.observedReturnWords = some [psc - feeN, psp - feeN, feeN] := by
  intro ae feeN
  -- Concrete trailing proof is in `finish_from_fee`; the accrual branch is
  -- reduced to it below.
  have finish : ∀ (s1 : DenoteState) (fee : Nat),
      lookupValue s1.bindings "_verity_slice_tmp_33" = fee →
      lookupValue s1.bindings "postSlashCredit" = psc →
      lookupValue s1.bindings "postSlashPendingFee" = psp →
      fee ≤ psp →
      execStmtList o fields s1 (at_ 16) = .stop final →
      fee ≤ psc ∧ final.observedReturnWords = some [psc - fee, psp - fee, fee] := by
    intro s1 fee hfee hs1 hp1 hle hstop
    let sF := {s1 with bindings := bindValue s1.bindings "fee" fee}
    have h1 : execStmtList o fields s1 (at_ 16) = execStmtList o fields sF (at_ 17) := by
      rw [shape16, let_local hfee]; simp [sF]
    have hpsc1 : lookupValue sF.bindings "postSlashCredit" = psc := by
      dsimp [sF]
      rw [lookup_bind_other _ "fee" "postSlashCredit" _ (by decide)]
      exact hs1
    have hpsp1 : lookupValue sF.bindings "postSlashPendingFee" = psp := by
      dsimp [sF]
      rw [lookup_bind_other _ "fee" "postSlashPendingFee" _ (by decide)]
      exact hp1
    have hfee1 : lookupValue sF.bindings "fee" = fee := by simp [sF, lookup_bind_same]
    rw [h1] at hstop
    let sM := {sF with bindings := bindValue sF.bindings "_verity_slice_tmp_34" psc}
    have h2 : execStmtList o fields sF (at_ 17) = execStmtList o fields sM (at_ 18) := by
      rw [shape17]; exact let_mask128 hpsc1 hpscB rfl
    let sM' := {sM with bindings := bindValue sM.bindings "_verity_slice_tmp_35" psc}
    have h3 : execStmtList o fields sM (at_ 18) = execStmtList o fields sM' (at_ 19) := by
      rw [shape18, let_local (lookup_here)]; simp [sM']
    have hmask : lookupValue sM'.bindings "_verity_slice_tmp_35" = psc := by
      simp [sM', lookup_bind_same]
    have hfee2 : lookupValue sM'.bindings "fee" = fee := by
      dsimp [sM', sM]
      rw [lookup_bind_other _ "_verity_slice_tmp_35" "fee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_34" "fee" _ (by decide)]
      exact hfee1
    rw [h2, h3, shape20] at hstop
    have ha : evalExpr o fields {sM' with bindings := bindValue sM'.bindings "_verity_slice_tmp_36" 0}
        (.localVar "_verity_slice_tmp_35") = some psc := by
      rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_36" "_verity_slice_tmp_35" _ (by decide)]
      exact congrArg some hmask
    have hb : evalExpr o fields {sM' with bindings := bindValue sM'.bindings "_verity_slice_tmp_36" 0}
        (.localVar "fee") = some fee := by
      rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_36" "fee" _ (by decide)]
      exact congrArg some hfee2
    obtain ⟨hleP, hrest⟩ := ex_checked_sub ha hb (lt_of_le_of_lt hpscB max128_lt)
      (lt_of_le_of_lt (le_trans hle hpspB) max128_lt) hstop
    -- `ex_checked_sub` yields `fee ≤ psc` and the tail from `at_ 21`.
    refine ⟨hleP, ?_⟩
    let sD := {sM' with bindings := bindValue sM'.bindings "_verity_slice_tmp_36" (psc - fee)}
    have htail : execStmtList o fields sD (at_ 21) = .stop final := by
      simpa [sD] using hrest
    let sC := {sD with bindings := bindValue sD.bindings "_verity_slice_tmp_37" (psc - fee)}
    have h4 : execStmtList o fields sD (at_ 21) = execStmtList o fields sC (at_ 22) := by
      rw [shape21, let_local (lookup_here)]; simp [sC]
    let sP := {sC with bindings := bindValue sC.bindings "_verity_slice_tmp_38" psp}
    have hpsp2 : lookupValue sC.bindings "postSlashPendingFee" = psp := by
      dsimp [sC, sD, sM', sM]
      rw [lookup_bind_other _ "_verity_slice_tmp_37" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_36" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_35" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_34" "postSlashPendingFee" _ (by decide)]
      exact hpsp1
    have h5 : execStmtList o fields sC (at_ 22) = execStmtList o fields sP (at_ 23) := by
      rw [shape22]; exact let_mask128 hpsp2 hpspB rfl
    let sP' := {sP with bindings := bindValue sP.bindings "_verity_slice_tmp_39" psp}
    have h6 : execStmtList o fields sP (at_ 23) = execStmtList o fields sP' (at_ 24) := by
      rw [shape23, let_local (lookup_here)]; simp [sP']
    have hpm : lookupValue sP'.bindings "_verity_slice_tmp_39" = psp := by
      simp [sP', lookup_bind_same]
    have hfee3 : lookupValue sP'.bindings "fee" = fee := by
      dsimp [sP', sP, sC, sD]
      rw [lookup_bind_other _ "_verity_slice_tmp_39" "fee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_38" "fee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_37" "fee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_36" "fee" _ (by decide)]
      exact hfee2
    rw [h4, h5, h6, shape25] at htail
    have ha2 : evalExpr o fields {sP' with bindings := bindValue sP'.bindings "_verity_slice_tmp_40" 0}
        (.localVar "_verity_slice_tmp_39") = some psp := by
      rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_40" "_verity_slice_tmp_39" _ (by decide)]
      exact congrArg some hpm
    have hb2 : evalExpr o fields {sP' with bindings := bindValue sP'.bindings "_verity_slice_tmp_40" 0}
        (.localVar "fee") = some fee := by
      rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_40" "fee" _ (by decide)]
      exact congrArg some hfee3
    obtain ⟨_, hrest2⟩ := ex_checked_sub ha2 hb2 (lt_of_le_of_lt hpspB max128_lt)
      (lt_of_le_of_lt (le_trans hle hpspB) max128_lt) htail
    let sE := {sP' with bindings := bindValue sP'.bindings "_verity_slice_tmp_40" (psp - fee)}
    have htail2 : execStmtList o fields sE (at_ 26) = .stop final := by simpa [sE] using hrest2
    let sR := {sE with bindings := bindValue sE.bindings "_verity_slice_tmp_41" (psp - fee)}
    have h7 : execStmtList o fields sE (at_ 26) = execStmtList o fields sR (at_ 27) := by
      rw [shape26, let_local (lookup_here)]; simp [sR]
    have hnc : lookupValue sR.bindings "_verity_slice_tmp_37" = psc - fee := by
      dsimp [sR, sE, sP', sP, sC]
      rw [lookup_bind_other _ "_verity_slice_tmp_41" "_verity_slice_tmp_37" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_40" "_verity_slice_tmp_37" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_39" "_verity_slice_tmp_37" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_38" "_verity_slice_tmp_37" _ (by decide),
        lookup_bind_same]
    have hnp : lookupValue sR.bindings "_verity_slice_tmp_41" = psp - fee := by
      simp [sR, lookup_bind_same]
    have hff : lookupValue sR.bindings "fee" = fee := by
      dsimp [sR, sE]
      rw [lookup_bind_other _ "_verity_slice_tmp_41" "fee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_40" "fee" _ (by decide)]
      exact hfee3
    rw [h7, shape27] at htail2
    have hret := @stop_return3 o fields sR "_verity_slice_tmp_37" "_verity_slice_tmp_41" "fee"
      (psc - fee) (psp - fee) fee hnc hnp hff
      (lt_of_le_of_lt (Nat.sub_le psc fee) (lt_of_le_of_lt hpscB max128_lt))
      (lt_of_le_of_lt (Nat.sub_le psp fee) (lt_of_le_of_lt hpspB max128_lt))
      (lt_of_le_of_lt (le_trans hle hpspB) max128_lt)
    have heq := hret.symm.trans htail2
    cases heq
    rfl
  -- Flag and accrual body. Both branches establish `feeN ≤ psp` before `finish`.
  let bit := boolWord (decide (A < mat))
  let sB := {s with bindings := bindValue s.bindings "_verity_slice_tmp_23" bit}
  have hflag : execStmtList o fields s (at_ 13) = execStmtList o fields sB (at_ 14) := by
    rw [shape13, exec_let_cons, evalExpr_lt_arm, evalExpr_localVar_arm, evalExpr_param_arm]
    rw [hA, hmat]
    simp [sB, bit]
  let sZ := {sB with bindings := bindValue sB.bindings "_verity_slice_tmp_33" 0}
  have hzero : execStmtList o fields sB (at_ 14) = execStmtList o fields sZ (at_ 15) := by
    rw [shape14, let_literal wordNormalize_zero]; simp [sZ]
  rw [hflag, hzero] at h
  by_cases hAcc : A < mat
  · -- Accrual branch: deferred to the arithmetic of `brYes 15`.
    have hbit : lookupValue sZ.bindings "_verity_slice_tmp_23" = 1 := by
      dsimp [sZ, sB, bit]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "_verity_slice_tmp_23" _ (by decide), lookup_bind_same]
      simp [bit, decide_true_of hAcc, boolWord_true]
    -- Preserve the inputs into the branch state `sZ`.
    have hpscZ : lookupValue sZ.bindings "postSlashCredit" = psc := by
      dsimp [sZ, sB]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashCredit" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_23" "postSlashCredit" _ (by decide)]
      exact hpsc
    have hpspZ : lookupValue sZ.bindings "postSlashPendingFee" = psp := by
      dsimp [sZ, sB]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_23" "postSlashPendingFee" _ (by decide)]
      exact hpsp
    have hAZ : lookupValue sZ.bindings "_lastAccrual" = A := by
      dsimp [sZ, sB]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "_lastAccrual" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_23" "_lastAccrual" _ (by decide)]
      exact hA
    have hmatZ : lookupValue sZ.bindings "market_maturity" = mat := by
      dsimp [sZ, sB]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "market_maturity" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_23" "market_maturity" _ (by decide)]
      exact hmat
    have haeZ : lookupValue sZ.bindings "accrualEnd" = ae := by
      dsimp [sZ, sB, ae]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "accrualEnd" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_23" "accrualEnd" _ (by decide)]
      exact hae
    -- `ae - A` succeeds only because the whole call stops.
    have hsub1 : evalExpr o fields {sZ with bindings := bindValue sZ.bindings "_verity_slice_tmp_24" 0}
        (.localVar "accrualEnd") = some ae := by
      rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_24" "accrualEnd" _ (by decide)]
      exact congrArg some haeZ
    have hsub2 : evalExpr o fields {sZ with bindings := bindValue sZ.bindings "_verity_slice_tmp_24" 0}
        (.localVar "_lastAccrual") = some A := by
      rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_24" "_lastAccrual" _ (by decide)]
      exact congrArg some hAZ
    rw [shape15] at h
    have hmatch := by
      simpa [hbit, execStmtList.eq_2, execStmt_ite_arm, evalExpr_localVar_arm,
        show ((1 : Nat) != 0) = true by decide] using h
    have hp : prefixList [] (brYes 15) = true := by
      unfold brYes at_ skip body functionBody functionBody.go prefixList prefixStmt; decide
    have hf := list_frame o fields sZ (brYes 15) [] hp
    match hrun : execStmtList o fields sZ (brYes 15) with
    | .continue tAcc =>
        have htail : execStmtList o fields tAcc (at_ 16) = .stop final := by
          simpa [hrun] using hmatch
        have hAeM : ae < Uint256.modulus := by
          dsimp [ae]; split <;> assumption
        rw [feeSubAe] at hrun
        obtain ⟨hAle, hrun1⟩ := ex_checked_sub_cont hsub1 hsub2 hAeM
          (lt_of_le_of_lt hA128 max128_lt) hrun
        let d1 := ae - A
        let sD1 := {sZ with bindings := bindValue sZ.bindings "_verity_slice_tmp_24" d1}
        have hrun1' : execStmtList o fields sD1 (brYesAt 15 2) = .continue tAcc := by
          simpa [sD1, d1] using hrun1
        rw [feeCopyD1] at hrun1'
        let sD1' := {sD1 with bindings := bindValue sD1.bindings "_verity_slice_tmp_26" d1}
        have hcopy1 : execStmtList o fields sD1 (brYesAt 15 2) =
            execStmtList o fields sD1' (brYesAt 15 3) := by
          rw [feeCopyD1]
          apply let_local (lookup_here)
          simp [sD1']
        have hA2 : lookupValue sD1'.bindings "_lastAccrual" = A := by
          dsimp [sD1', sD1]
          rw [lookup_bind_other _ "_verity_slice_tmp_26" "_lastAccrual" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_24" "_lastAccrual" _ (by decide)]
          exact hAZ
        have hmat2 : lookupValue sD1'.bindings "market_maturity" = mat := by
          dsimp [sD1', sD1]
          rw [lookup_bind_other _ "_verity_slice_tmp_26" "market_maturity" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_24" "market_maturity" _ (by decide)]
          exact hmatZ
        have hd2a : evalExpr o fields {sD1' with bindings := bindValue sD1'.bindings "_verity_slice_tmp_25" 0}
            (.param "market_maturity") = some mat := by
          rw [evalExpr_param_arm, lookup_bind_other _ "_verity_slice_tmp_25" "market_maturity" _ (by decide)]
          exact congrArg some hmat2
        have hd2b : evalExpr o fields {sD1' with bindings := bindValue sD1'.bindings "_verity_slice_tmp_25" 0}
            (.localVar "_lastAccrual") = some A := by
          rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_25" "_lastAccrual" _ (by decide)]
          exact congrArg some hA2
        rw [feeSubD2] at hrun1'
        have hrun2s : execStmtList o fields sD1' (brYesAt 15 3) = .continue tAcc :=
          hcopy1.symm.trans hrun1'
        obtain ⟨hAmat, hrun2⟩ := ex_checked_sub_cont hd2a hd2b hmatM
          (lt_of_le_of_lt hA128 max128_lt) hrun2s
        let d2 := mat - A
        let sD2 := {sD1' with bindings := bindValue sD1'.bindings "_verity_slice_tmp_25" d2}
        have hrun2' : execStmtList o fields sD2 (brYesAt 15 5) = .continue tAcc := by
          exact hrun2
        rw [feeCopyD2] at hrun2'
        let sD2' := {sD2 with bindings := bindValue sD2.bindings "_verity_slice_tmp_27" d2}
        have hcopy2 : execStmtList o fields sD2 (brYesAt 15 5) =
            execStmtList o fields sD2' (brYesAt 15 6) := by
          rw [feeCopyD2]
          apply let_local (lookup_here)
          simp [sD2']
        have hpsp3 : lookupValue sD2'.bindings "postSlashPendingFee" = psp := by
          dsimp [sD2', sD2, sD1', sD1]
          rw [lookup_bind_other _ "_verity_slice_tmp_27" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_25" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_26" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_24" "postSlashPendingFee" _ (by decide)]
          exact hpspZ
        have hd1l : lookupValue sD2'.bindings "_verity_slice_tmp_26" = d1 := by
          dsimp [sD2', sD2, sD1']
          rw [lookup_bind_other _ "_verity_slice_tmp_27" "_verity_slice_tmp_26" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_25" "_verity_slice_tmp_26" _ (by decide),
            lookup_bind_same]
        have hma : evalExpr o fields {sD2' with bindings := bindValue sD2'.bindings "_verity_slice_tmp_28" 0}
            (.localVar "postSlashPendingFee") = some psp := by
          rw [evalExpr_localVar_arm,
            lookup_bind_other _ "_verity_slice_tmp_28" "postSlashPendingFee" _ (by decide)]
          exact congrArg some hpsp3
        have hmb : evalExpr o fields {sD2' with bindings := bindValue sD2'.bindings "_verity_slice_tmp_28" 0}
            (.localVar "_verity_slice_tmp_26") = some d1 := by
          rw [evalExpr_localVar_arm,
            lookup_bind_other _ "_verity_slice_tmp_28" "_verity_slice_tmp_26" _ (by decide)]
          exact congrArg some hd1l
        rw [feeMul] at hrun2'
        have hrun3s : execStmtList o fields sD2' (brYesAt 15 6) = .continue tAcc :=
          hcopy2.symm.trans hrun2'
        obtain ⟨hprod, hrun3⟩ := ex_checked_mul_cont hma hmb
          (lt_of_le_of_lt hpspB max128_lt) (lt_of_le_of_lt (Nat.sub_le _ _) hAeM) hrun3s
        let prod := psp * d1
        let sP := {sD2' with bindings := bindValue sD2'.bindings "_verity_slice_tmp_28" prod}
        have hrun3' : execStmtList o fields sP (brYesAt 15 8) = .continue tAcc := by
          exact hrun3
        rw [feeCopyMul] at hrun3'
        let sP' := {sP with bindings := bindValue sP.bindings "_verity_slice_tmp_29" prod}
        have hcopy3 : execStmtList o fields sP (brYesAt 15 8) =
            execStmtList o fields sP' (brYesAt 15 9) := by
          rw [feeCopyMul]
          apply let_local (lookup_here)
          simp [sP']
        have hden : lookupValue sP'.bindings "_verity_slice_tmp_27" = d2 := by
          dsimp [sP', sP, sD2']
          rw [lookup_bind_other _ "_verity_slice_tmp_29" "_verity_slice_tmp_27" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_28" "_verity_slice_tmp_27" _ (by decide),
            lookup_bind_same]
        have hnum : lookupValue sP'.bindings "_verity_slice_tmp_29" = prod := by
          simp [sP', lookup_bind_same]
        have hda : evalExpr o fields {sP' with bindings := bindValue sP'.bindings "_verity_slice_tmp_30" 0}
            (.localVar "_verity_slice_tmp_29") = some prod := by
          rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_30" "_verity_slice_tmp_29" _ (by decide)]
          exact congrArg some hnum
        have hdb : evalExpr o fields {sP' with bindings := bindValue sP'.bindings "_verity_slice_tmp_30" 0}
            (.localVar "_verity_slice_tmp_27") = some d2 := by
          rw [evalExpr_localVar_arm, lookup_bind_other _ "_verity_slice_tmp_30" "_verity_slice_tmp_27" _ (by decide)]
          exact congrArg some hden
        have hd2pos : d2 ≠ 0 := by
          dsimp [d2]; omega
        rw [feeDiv] at hrun3'
        have hrun4s : execStmtList o fields sP' (brYesAt 15 9) = .continue tAcc :=
          hcopy3.symm.trans hrun3'
        -- Division cannot fail once `d2 ≠ 0`; rebuild it as a forward step and
        -- identify the resulting state with `tAcc` via the continuation.
        let quot := prod / d2
        let sQ := {sP' with bindings := bindValue sP'.bindings "_verity_slice_tmp_30" quot}
        have hdivStep : execStmtList o fields sP' (brYesAt 15 9) =
            execStmtList o fields sQ (brYesAt 15 11) := by
          rw [feeDiv]
          apply go_checked_div hda hdb hprod (lt_of_le_of_lt (Nat.sub_le _ _) hmatM) hd2pos
          dsimp [sQ, quot]
        have hrun4 : execStmtList o fields sQ (brYesAt 15 11) = .continue tAcc :=
          hdivStep.symm.trans hrun4s
        rw [feeCopyQuot] at hrun4
        let sQ' := {sQ with bindings := bindValue sQ.bindings "_verity_slice_tmp_31" quot}
        have hcopy4 : execStmtList o fields sQ (brYesAt 15 11) =
            execStmtList o fields sQ' (brYesAt 15 12) := by
          rw [feeCopyQuot]
          apply let_local (lookup_here)
          simp [sQ']
        have hquotL : lookupValue sQ'.bindings "_verity_slice_tmp_31" = quot := by
          simp [sQ', lookup_bind_same]
        have hd1le : d1 ≤ d2 := by
          dsimp [d1, d2, ae]
          split
          · next hlt => omega
          · next hge =>
              have htsLe : ts ≤ mat := Nat.le_of_not_lt hge
              omega
        have hquotLe : quot ≤ psp := by
          dsimp [quot, prod]
          exact accrued_le_pending (by dsimp [d2]; omega) hd1le
        have hquotB : quot ≤ max128 := le_trans hquotLe hpspB
        rw [feeMask] at hrun4
        have hrun5s : execStmtList o fields sQ' (brYesAt 15 12) = .continue tAcc :=
          hcopy4.symm.trans hrun4
        let sMask := {sQ' with bindings := bindValue sQ'.bindings "_verity_slice_tmp_32" quot}
        have hmaskStep : execStmtList o fields sQ' (brYesAt 15 12) =
            execStmtList o fields sMask (brYesAt 15 13) := by
          rw [feeMask]
          apply let_mask128 hquotL hquotB
          dsimp [sMask]
        have hrun5 : execStmtList o fields sMask (brYesAt 15 13) = .continue tAcc :=
          hmaskStep.symm.trans hrun5s
        rw [feeAssign] at hrun5
        let sFee := {sMask with bindings := bindValue sMask.bindings "_verity_slice_tmp_33" quot}
        have hassign : execStmtList o fields sMask (brYesAt 15 13) = .continue sFee := by
          apply assign_local (lookup_here)
          rw [execStmtList.eq_1]
        have htAcc : tAcc = sFee :=
          StmtOutcome.noConfusion (hrun5.symm.trans hassign) id
        have hfeeL : lookupValue tAcc.bindings "_verity_slice_tmp_33" = quot := by
          simpa [htAcc, sFee, lookup_bind_same]
        have hpscL : lookupValue tAcc.bindings "postSlashCredit" = psc := by
          rw [htAcc]
          dsimp [sFee, sMask, sQ', sQ, sP', sP, sD2', sD2, sD1', sD1]
          rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_32" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_31" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_30" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_29" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_28" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_27" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_25" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_26" "postSlashCredit" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_24" "postSlashCredit" _ (by decide)]
          exact hpscZ
        have hpspL : lookupValue tAcc.bindings "postSlashPendingFee" = psp := by
          rw [htAcc]
          dsimp [sFee, sMask, sQ', sQ, sP', sP, sD2', sD2, sD1', sD1]
          rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_32" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_31" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_30" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_29" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_28" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_27" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_25" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_26" "postSlashPendingFee" _ (by decide),
            lookup_bind_other _ "_verity_slice_tmp_24" "postSlashPendingFee" _ (by decide)]
          exact hpspZ
        have hfin := finish tAcc quot hfeeL hpscL hpspL hquotLe htail
        have hfeeEq : feeN = quot := by
          simp [feeN, quot, prod, d1, d2, ae, hAcc]
        refine ⟨fun _ => hAle, fun _ => hprod, ?_, ?_, ?_⟩
        · simpa [hfeeEq] using hfin.1
        · simpa [hfeeEq] using hquotLe
        · simpa [hfeeEq] using hfin.2
    | .stop _ => simp [Frame, hrun] at hf
    | .return _ _ => simp [Frame, hrun] at hf
    | .revert => simpa [hrun] using hmatch
  · have hbit : lookupValue sZ.bindings "_verity_slice_tmp_23" = 0 := by
      dsimp [sZ, sB, bit]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "_verity_slice_tmp_23" _ (by decide), lookup_bind_same]
      simp [bit, decide_false_of_not hAcc, boolWord_false]
    let sNo := {sZ with bindings := bindValue sZ.bindings "_verity_slice_tmp_33" 0}
    have hbr : execStmtList o fields sZ (brNo 15) = .continue sNo := by
      rw [br15no]; apply assign_literal wordNormalize_zero; rw [execStmtList.eq_1]
    have hite : execStmtList o fields sZ (at_ 15) = execStmtList o fields sNo (at_ 16) := by
      rw [shape15]; exact go_ite_zero hbit hbr rfl
    have hfee0 : lookupValue sNo.bindings "_verity_slice_tmp_33" = 0 := by
      simp [sNo, lookup_bind_same]
    have hpscN : lookupValue sNo.bindings "postSlashCredit" = psc := by
      dsimp [sNo]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashCredit" _ (by decide)]
      exact (by
        dsimp [sZ, sB]
        rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashCredit" _ (by decide),
          lookup_bind_other _ "_verity_slice_tmp_23" "postSlashCredit" _ (by decide)]
        exact hpsc)
    have hpspN : lookupValue sNo.bindings "postSlashPendingFee" = psp := by
      dsimp [sNo, sZ, sB]
      rw [lookup_bind_other _ "_verity_slice_tmp_33" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_33" "postSlashPendingFee" _ (by decide),
        lookup_bind_other _ "_verity_slice_tmp_23" "postSlashPendingFee" _ (by decide)]
      exact hpsp
    rw [hite] at h
    have hfin := finish sNo 0 hfee0 hpscN hpspN (Nat.zero_le _) h
    have hfeeEq : feeN = 0 := by simp [feeN, hAcc]
    refine ⟨fun hc => absurd hc hAcc, fun hc => absurd hc hAcc, ?_, ?_, ?_⟩
    · simpa [hfeeEq] using hfin.1
    · simpa [hfeeEq] using (Nat.zero_le psp)
    · simpa [hfeeEq] using hfin.2

/-- From the accrual flag onward the body only stops with a return or reverts. -/
theorem at13_ends (o : DenoteOracle) (s : DenoteState) :
    execStmtList o fields s (at_ 13) = .revert ∨
      ∃ t, execStmtList o fields s (at_ 13) = .stop t := by
  have hp : prefixList [] (at_ 13).dropLast = true := by
    unfold prefixList prefixStmt at_ skip body functionBody functionBody.go List.dropLast
    decide
  have hs : at_ 13 = (at_ 13).dropLast ++
      [.returnValues [.localVar "_verity_slice_tmp_37",
        .localVar "_verity_slice_tmp_41", .localVar "fee"]] := by
    unfold at_ skip body functionBody functionBody.go List.dropLast
    rfl
  rw [hs]
  exact ends_return o fields s (at_ 13).dropLast
    [.localVar "_verity_slice_tmp_37", .localVar "_verity_slice_tmp_41", .localVar "fee"] hp

theorem pspN_le (credit pending psc : Nat) : pspN credit pending psc ≤ pending := by
  unfold pspN
  split
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

theorem uint128_ofNat_val {n : Nat} (h : n < 2 ^ 128) : (UIntN.ofNat 128 n).val = n := by
  dsimp [UIntN.ofNat]
  exact Nat.mod_eq_of_lt h

theorem mapFactor_sub (x : UIntN 128) : Spec.mapFactor x = (max128 - x.val : Int) := by
  have hx : x.val ≤ max128 := uint128_le_max x
  simp only [Spec.mapFactor, max128]
  omega

theorem updatePositionViewProperties : Spec.updatePositionViewProperties := by
  intro o w maturity id user newCredit newPendingFee fee old req hcall
  have hLM : (midnight.position.lastLossFactor o w id user).val ≤
      (midnight.marketState.lossFactor o w id).val := by
    dsimp [old, Spec.old] at req
    exact req.lastLossFactorLeqMarketLossFactor
  let C := (midnight.position.credit o w id user).val
  let L := (midnight.position.lastLossFactor o w id user).val
  let Mv := (midnight.marketState.lossFactor o w id).val
  let P := (midnight.position.pendingFee o w id user).val
  let A := (midnight.position.lastAccrual o w id user).val
  let psc := postSlashCreditN C L Mv
  let psp := pspN C P psc
  let ts := w.blockTimestamp.val
  let ae := if maturity.val < ts then maturity.val else ts
  let s0 : DenoteState :=
    { world := w, bindings := [("market_maturity", maturity.val), ("id", id.val), ("user", user.val)] }
  obtain ⟨t, hex, hpsc, hpsp, haeL, hA, hmat, _hC, _hP, hw⟩ :=
    run_to_time o w maturity id user hLM
  have hCmax : C ≤ max128 := uint128_le_max _
  have hPmax : P ≤ max128 := uint128_le_max _
  have hAmax : A ≤ max128 := uint128_le_max _
  have hpscB : psc ≤ max128 := by
    dsimp [psc]
    exact le_trans (postSlashCredit_le (uint128_le_max _) hLM) hCmax
  have hpspB : psp ≤ max128 := le_trans (pspN_le C P psc) hPmax
  rcases at13_ends o t with hrev | ⟨final, hstop⟩
  · have hexr : execStmtList o fields s0 body = .revert := hex.trans hrev
    unfold body at hexr
    simp [midnight.updatePositionView, runFunction, s0, hexr,
      toWord_uint256, toWord_bytes32, toWord_address] at hcall
  · have hts : t.world.blockTimestamp.val = ts := by rw [hw]
    have hsuffix := suffix_stop o t final psc psp A maturity.val ts hpsc hpsp hA hmat haeL hts
      hpscB hpspB hAmax maturity.isLt w.blockTimestamp.isLt hstop
    dsimp only at hsuffix
    rcases hsuffix with ⟨_hAle, _hprod, hfeePsc, hfeePsp, hwords⟩
    let feeN := if A < maturity.val then psp * (ae - A) / (maturity.val - A) else 0
    have hwords' : final.observedReturnWords = some [psc - feeN, psp - feeN, feeN] := by
      simpa [feeN, ae] using hwords
    have hexw : execStmtList o midnight.model.fields s0 (functionBody midnight.model "updatePositionView") =
        .stop final := by
      have hexw := hex.trans hstop
      unfold body at hexw
      exact hexw
    unfold midnight.updatePositionView runFunction at hcall
    simp only [toWord_uint256, toWord_bytes32, toWord_address] at hcall
    rw [hexw] at hcall
    simp [hwords', ofWord_uintN] at hcall
    -- The returned words are exactly the narrowed success values.
    rcases hcall with ⟨hncEq, hnpEq, hfEq⟩
    have hpscC : psc ≤ C := by
      dsimp [psc]
      exact postSlashCredit_le (uint128_le_max _) hLM
    have hpspP : psp ≤ P := pspN_le C P psc
    have hfeeLeP : feeN ≤ P := le_trans hfeePsp hpspP
    have hsubC : psc - feeN ≤ C := le_trans (Nat.sub_le psc feeN) hpscC
    have hsubP : psp - feeN ≤ P := le_trans (Nat.sub_le psp feeN) hpspP
    have hltC : psc - feeN < 2 ^ 128 := by
      have : psc - feeN ≤ max128 := le_trans (Nat.sub_le _ _) hpscB
      unfold max128 at this
      omega
    have hltP : psp - feeN < 2 ^ 128 := by
      have : psp - feeN ≤ max128 := le_trans (Nat.sub_le _ _) hpspB
      unfold max128 at this
      omega
    have hltF : feeN < 2 ^ 128 := by
      have : feeN ≤ max128 := le_trans hfeePsp hpspB
      unfold max128 at this
      omega
    have hnc : newCredit.val = psc - feeN :=
      (congrArg UIntN.val hncEq.symm).trans (uint128_ofNat_val hltC)
    have hnp : newPendingFee.val = psp - feeN :=
      (congrArg UIntN.val hnpEq.symm).trans (uint128_ofNat_val hltP)
    have hfv : fee.val = feeN :=
      (congrArg UIntN.val hfEq.symm).trans (uint128_ofNat_val hltF)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- fee ≤ old pending fee
      change fee ≤ (Spec.old o w id user).pendingFee
      rw [show (Spec.old o w id user).pendingFee = midnight.position.pendingFee o w id user from rfl]
      change fee.val ≤ P
      simpa [hfv] using hfeeLeP
    · -- (newCredit + fee) * mapFactor(lastLoss) ≤ credit * mapFactor(loss)
      have hmul := postSlashCredit_mul_le (credit := C)
        (uint128_le_max (midnight.position.lastLossFactor o w id user))
        (uint128_le_max (midnight.marketState.lossFactor o w id)) hLM
      have hmul' : psc * (max128 - L) ≤ C * (max128 - Mv) := hmul
      have hcast : ((psc * (max128 - L) : Nat) : Int) ≤ ((C * (max128 - Mv) : Nat) : Int) :=
        Nat.cast_le.mpr hmul'
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (uint128_le_max (midnight.position.lastLossFactor o w id user)),
        Nat.cast_sub (uint128_le_max (midnight.marketState.lossFactor o w id))] at hcast
      have hsum : (newCredit.val : Int) + fee.val = (psc : Int) := by
        rw [hnc, hfv, Nat.cast_sub hfeePsc]
        exact Int.sub_add_cancel (↑psc) (↑feeN)
      change ((newCredit.val : Int) + fee.val) * Spec.mapFactor (Spec.old o w id user).lastLossFactor ≤
        (Spec.old o w id user).credit.val * Spec.mapFactor (Spec.old o w id user).lossFactor
      rw [hsum, mapFactor_sub, mapFactor_sub]
      simpa [Spec.old, C, L, Mv] using hcast
    · change newCredit ≤ (Spec.old o w id user).credit
      rw [show (Spec.old o w id user).credit = midnight.position.credit o w id user from rfl]
      change newCredit.val ≤ C
      simpa [hnc] using hsubC
    · change newPendingFee ≤ (Spec.old o w id user).pendingFee
      rw [show (Spec.old o w id user).pendingFee = midnight.position.pendingFee o w id user from rfl]
      change newPendingFee.val ≤ P
      simpa [hnp] using hsubP
    · intro hzero
      have hMv : Mv = max128 := by
        have hz : Spec.mapFactor (midnight.marketState.lossFactor o w id) = 0 := by
          simpa [old, Spec.old] using hzero
        rw [mapFactor_sub] at hz
        have hle : (midnight.marketState.lossFactor o w id).val ≤ max128 := uint128_le_max _
        omega
      have hpsc0 : psc = 0 := by
        dsimp [psc, postSlashCreditN]
        by_cases hlt : L < max128
        · simp [hlt, hMv]
        · have hLmax : L = max128 := by
            have hLle : L ≤ Mv := hLM
            omega
          simp [hLmax]
      have hfee0 : feeN = 0 := by
        have hle : feeN ≤ psc := hfeePsc
        omega
      have hnc0 : newCredit.val = 0 := by simpa [hpsc0, hfee0] using hnc
      have hf0 : fee.val = 0 := by simpa [hfee0] using hfv
      have hzeroVal : (0 : UIntN 128).val = 0 := by
        show (UIntN.ofNat 128 0).val = 0
        exact uint128_ofNat_val (by decide)
      refine ⟨?_, ?_⟩
      · apply UIntN.ext
        rw [hzeroVal]
        exact hnc0
      · apply UIntN.ext
        rw [hzeroVal]
        exact hf0

end Midnight
