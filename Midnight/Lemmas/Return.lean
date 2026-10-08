import Midnight.Lemmas.PostSlash

/-!
Return words of a successful `postFee` execution, and framing of
`postSlashCredit` / `postSlashPendingFee` across `midFee`.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight.Lemmas

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- Concrete shape of `postFee` (definitionally equal). -/
theorem postFee_concrete : postFee =
[Stmt.letVar
   "_verity_slice_tmp_34"
   (Expr.bitAnd
     (Expr.localVar "postSlashCredit")
     (Expr.literal max128)),
 Stmt.letVar
   "_verity_slice_tmp_35"
   (Expr.localVar "_verity_slice_tmp_34"),
 Stmt.letVar "_verity_slice_tmp_36" (Expr.literal 0),
 Stmt.ite
   (Expr.lt
     (Expr.localVar "_verity_slice_tmp_35")
     (Expr.localVar "fee"))
   [Stmt.panic PanicCode.arithmeticOverflow]
   [Stmt.assignVar
      "_verity_slice_tmp_36"
      (Expr.sub
        (Expr.localVar "_verity_slice_tmp_35")
        (Expr.localVar "fee"))],
 Stmt.letVar
   "_verity_slice_tmp_37"
   (Expr.localVar "_verity_slice_tmp_36"),
 Stmt.letVar
   "_verity_slice_tmp_38"
   (Expr.bitAnd
     (Expr.localVar "postSlashPendingFee")
     (Expr.literal max128)),
 Stmt.letVar
   "_verity_slice_tmp_39"
   (Expr.localVar "_verity_slice_tmp_38"),
 Stmt.letVar "_verity_slice_tmp_40" (Expr.literal 0),
 Stmt.ite
   (Expr.lt
     (Expr.localVar "_verity_slice_tmp_39")
     (Expr.localVar "fee"))
   [Stmt.panic PanicCode.arithmeticOverflow]
   [Stmt.assignVar
      "_verity_slice_tmp_40"
      (Expr.sub
        (Expr.localVar "_verity_slice_tmp_39")
        (Expr.localVar "fee"))],
 Stmt.letVar
   "_verity_slice_tmp_41"
   (Expr.localVar "_verity_slice_tmp_40"),
 Stmt.returnValues
   [Expr.localVar "_verity_slice_tmp_37",
    Expr.localVar "_verity_slice_tmp_41",
    Expr.localVar "fee"]]
:= rfl

theorem retArgs_concrete : retArgs =
    [.localVar "_verity_slice_tmp_37",
     .localVar "_verity_slice_tmp_41",
     .localVar "fee"] := by
  simp only [retArgs, returnArgsOf, postFee_concrete]

theorem postFeePre_concrete : postFeePre =
[Stmt.letVar
   "_verity_slice_tmp_34"
   (Expr.bitAnd
     (Expr.localVar "postSlashCredit")
     (Expr.literal max128)),
 Stmt.letVar
   "_verity_slice_tmp_35"
   (Expr.localVar "_verity_slice_tmp_34"),
 Stmt.letVar "_verity_slice_tmp_36" (Expr.literal 0),
 Stmt.ite
   (Expr.lt
     (Expr.localVar "_verity_slice_tmp_35")
     (Expr.localVar "fee"))
   [Stmt.panic PanicCode.arithmeticOverflow]
   [Stmt.assignVar
      "_verity_slice_tmp_36"
      (Expr.sub
        (Expr.localVar "_verity_slice_tmp_35")
        (Expr.localVar "fee"))],
 Stmt.letVar
   "_verity_slice_tmp_37"
   (Expr.localVar "_verity_slice_tmp_36"),
 Stmt.letVar
   "_verity_slice_tmp_38"
   (Expr.bitAnd
     (Expr.localVar "postSlashPendingFee")
     (Expr.literal max128)),
 Stmt.letVar
   "_verity_slice_tmp_39"
   (Expr.localVar "_verity_slice_tmp_38"),
 Stmt.letVar "_verity_slice_tmp_40" (Expr.literal 0),
 Stmt.ite
   (Expr.lt
     (Expr.localVar "_verity_slice_tmp_39")
     (Expr.localVar "fee"))
   [Stmt.panic PanicCode.arithmeticOverflow]
   [Stmt.assignVar
      "_verity_slice_tmp_40"
      (Expr.sub
        (Expr.localVar "_verity_slice_tmp_39")
        (Expr.localVar "fee"))],
 Stmt.letVar
   "_verity_slice_tmp_41"
   (Expr.localVar "_verity_slice_tmp_40")]
:= by
  simp only [postFeePre, dropLastStmt, postFee_concrete]

/-- `bitAnd` with `max128` is the identity on values already `≤ max128`. -/
theorem eval_bitAnd_mask
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (e : Expr) (a : Nat)
    (ha : evalExpr oracle fs s e = some a)
    (hle : a ≤ max128) :
    evalExpr oracle fs s (.bitAnd e (.literal max128)) = some a := by
  have hm := eval_lit_max128 oracle fs s
  change (do
      let lhs ← evalExpr oracle fs s e
      let rhs ← evalExpr oracle fs s (.literal max128)
      pure (Uint256.and lhs rhs).val) = some a
  simp only [ha, hm, bind, pure, Option.bind]
  exact congrArg some (mask_eq hle)

/-- `midFee` does not rewrite `postSlashCredit` or `postSlashPendingFee`. -/
theorem midFee_preserves_postSlash
    (oracle : DenoteOracle) (fs : List Field) (s t : DenoteState)
    (h : execStmtList oracle fs s midFee = .continue t) :
    lookupValue t.bindings "postSlashCredit" =
      lookupValue s.bindings "postSlashCredit" ∧
    lookupValue t.bindings "postSlashPendingFee" =
      lookupValue s.bindings "postSlashPendingFee" := by
  have hf := list_frame oracle fs s midFee
    ["postSlashCredit", "postSlashPendingFee"] midFee_frames_postSlash
  simp only [Frame, h] at hf
  exact ⟨hf.2 "postSlashCredit" (by simp),
    hf.2 "postSlashPendingFee" (by simp)⟩

/-- Successful `postFee` continue through the credit subtraction. -/
theorem postFee_credit_checked
    (oracle : DenoteOracle) (fs : List Field) (s t : DenoteState)
    (psc feeVal : Nat)
    (hpsc : lookupValue s.bindings "postSlashCredit" = psc)
    (hfee : lookupValue s.bindings "fee" = feeVal)
    (hpsc_le : psc ≤ max128)
    (h : execStmtList oracle fs s
      [.letVar "_verity_slice_tmp_34"
          (.bitAnd (.localVar "postSlashCredit") (.literal max128)),
       .letVar "_verity_slice_tmp_35" (.localVar "_verity_slice_tmp_34"),
       .letVar "_verity_slice_tmp_36" (.literal 0),
       .ite (.lt (.localVar "_verity_slice_tmp_35") (.localVar "fee"))
         [.panic .arithmeticOverflow]
         [.assignVar "_verity_slice_tmp_36"
            (.sub (.localVar "_verity_slice_tmp_35") (.localVar "fee"))],
       .letVar "_verity_slice_tmp_37" (.localVar "_verity_slice_tmp_36")] =
      .continue t) :
    feeVal ≤ psc ∧
    lookupValue t.bindings "_verity_slice_tmp_37" = psc - feeVal ∧
    lookupValue t.bindings "fee" = feeVal ∧
    lookupValue t.bindings "postSlashPendingFee" =
      lookupValue s.bindings "postSlashPendingFee" := by
  have he_psc := eval_local_eq oracle fs s "postSlashCredit" psc hpsc
  have he_mask := eval_bitAnd_mask oracle fs s (.localVar "postSlashCredit") psc he_psc hpsc_le
  have step34 := exec_let_continue oracle fs s "_verity_slice_tmp_34" _ psc he_mask
  set s34 : DenoteState :=
    { s with bindings := bindValue s.bindings "_verity_slice_tmp_34" psc }
  have he35 : evalExpr oracle fs s34 (.localVar "_verity_slice_tmp_34") = some psc := by
    simp only [evalExpr, s34, lookup_bind_same]
  have step35 := exec_let_continue oracle fs s34 "_verity_slice_tmp_35" _ psc he35
  set s35 : DenoteState :=
    { s34 with bindings := bindValue s34.bindings "_verity_slice_tmp_35" psc }
  have step36 := exec_let_continue oracle fs s35 "_verity_slice_tmp_36" (.literal 0) 0
    (eval_lit_zero _ _ _)
  set s36 : DenoteState :=
    { s35 with bindings := bindValue s35.bindings "_verity_slice_tmp_36" 0 }
  have hfee36 : lookupValue s36.bindings "fee" = feeVal := by
    simp only [s36, s35, s34]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), hfee]
  have hpsp36 : lookupValue s36.bindings "postSlashPendingFee" =
      lookupValue s.bindings "postSlashPendingFee" := by
    simp only [s36, s35, s34]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide)]
  have htmp35 : lookupValue s36.bindings "_verity_slice_tmp_35" = psc := by
    simp only [s36, s35]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_same]
  have he_tmp35 := eval_local_eq oracle fs s36 "_verity_slice_tmp_35" psc htmp35
  have he_fee := eval_local_eq oracle fs s36 "fee" feeVal hfee36
  have hlist :
      [Stmt.letVar "_verity_slice_tmp_34"
          (Expr.bitAnd (Expr.localVar "postSlashCredit") (Expr.literal max128)),
       Stmt.letVar "_verity_slice_tmp_35" (Expr.localVar "_verity_slice_tmp_34"),
       Stmt.letVar "_verity_slice_tmp_36" (Expr.literal 0),
       Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))
         [Stmt.panic PanicCode.arithmeticOverflow]
         [Stmt.assignVar "_verity_slice_tmp_36"
            (Expr.sub (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))],
       Stmt.letVar "_verity_slice_tmp_37" (Expr.localVar "_verity_slice_tmp_36")] =
      [Stmt.letVar "_verity_slice_tmp_34"
          (Expr.bitAnd (Expr.localVar "postSlashCredit") (Expr.literal max128))] ++
      [Stmt.letVar "_verity_slice_tmp_35" (Expr.localVar "_verity_slice_tmp_34"),
       Stmt.letVar "_verity_slice_tmp_36" (Expr.literal 0),
       Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))
         [Stmt.panic PanicCode.arithmeticOverflow]
         [Stmt.assignVar "_verity_slice_tmp_36"
            (Expr.sub (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))],
       Stmt.letVar "_verity_slice_tmp_37" (Expr.localVar "_verity_slice_tmp_36")] := rfl
  rw [hlist, exec_append, step34] at h
  change execStmtList oracle fs s34
      [Stmt.letVar "_verity_slice_tmp_35" (Expr.localVar "_verity_slice_tmp_34"),
       Stmt.letVar "_verity_slice_tmp_36" (Expr.literal 0),
       Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))
         [Stmt.panic PanicCode.arithmeticOverflow]
         [Stmt.assignVar "_verity_slice_tmp_36"
            (Expr.sub (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))],
       Stmt.letVar "_verity_slice_tmp_37" (Expr.localVar "_verity_slice_tmp_36")] =
      .continue t at h
  rw [exec_cons_continue (t := s35) (hhead := step35),
    exec_cons_continue (t := s36) (hhead := step36)] at h
  have hlt := eval_lt_of_vals oracle fs s36
    (.localVar "_verity_slice_tmp_35") (.localVar "fee") psc feeVal he_tmp35 he_fee
  by_cases hltPf : psc < feeVal
  · have hbw : boolWord (decide (psc < feeVal)) = 1 := boolWord_true_of hltPf
    have hcond1 : evalExpr oracle fs s36
        (.lt (.localVar "_verity_slice_tmp_35") (.localVar "fee")) = some 1 := by
      simp [hlt, hbw]
    have hflat :
        [Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))
           [Stmt.panic PanicCode.arithmeticOverflow]
           [Stmt.assignVar "_verity_slice_tmp_36"
              (Expr.sub (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))],
         Stmt.letVar "_verity_slice_tmp_37" (Expr.localVar "_verity_slice_tmp_36")] =
        [Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))
           [Stmt.panic PanicCode.arithmeticOverflow]
           [Stmt.assignVar "_verity_slice_tmp_36"
              (Expr.sub (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))]] ++
        [Stmt.letVar "_verity_slice_tmp_37" (Expr.localVar "_verity_slice_tmp_36")] := rfl
    rw [hflat, exec_append, exec_ite_one oracle fs s36 _ _ _ hcond1] at h
    simp only [exec_singleton, execStmt] at h
    cases h
  · have hle : feeVal ≤ psc := Nat.not_lt.mp hltPf
    have hbw : boolWord (decide (psc < feeVal)) = 0 := boolWord_false_of_not hltPf
    have hcond0 : evalExpr oracle fs s36
        (.lt (.localVar "_verity_slice_tmp_35") (.localVar "fee")) = some 0 := by
      simp [hlt, hbw]
    have hpsc_mod : psc < Uint256.modulus := lt_of_le_of_lt hpsc_le max128_lt
    have step_ite := exec_checked_sub oracle fs s36 "_verity_slice_tmp_36"
      (.localVar "_verity_slice_tmp_35") (.localVar "fee") psc feeVal
      he_tmp35 he_fee hpsc_mod hle
    set sSub : DenoteState :=
      { s36 with bindings := bindValue s36.bindings "_verity_slice_tmp_36" (psc - feeVal) }
    have he37 : evalExpr oracle fs sSub (.localVar "_verity_slice_tmp_36") =
        some (psc - feeVal) := by
      simp only [evalExpr, sSub, lookup_bind_same]
    have step37 := exec_let_continue oracle fs sSub "_verity_slice_tmp_37" _ (psc - feeVal) he37
    set s37 : DenoteState :=
      { sSub with bindings := bindValue sSub.bindings "_verity_slice_tmp_37" (psc - feeVal) }
    have hexec :
        execStmtList oracle fs s36
          [Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))
             [Stmt.panic PanicCode.arithmeticOverflow]
             [Stmt.assignVar "_verity_slice_tmp_36"
                (Expr.sub (Expr.localVar "_verity_slice_tmp_35") (Expr.localVar "fee"))],
           Stmt.letVar "_verity_slice_tmp_37" (Expr.localVar "_verity_slice_tmp_36")] =
          .continue s37 := by
      rw [exec_cons_continue (t := sSub) (hhead := step_ite)]
      exact step37
    rw [hexec] at h
    have hsEq : t = s37 := StmtOutcome.continue.inj h.symm
    subst hsEq
    refine ⟨hle, ?_, ?_, ?_⟩
    · simp only [s37, lookup_bind_same]
    · simp only [s37, sSub, s36, s35, s34]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), hfee]
    · simp only [s37, sSub, s36, s35, s34]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide)]

/-- Successful `postFee` continue through the pending-fee subtraction. -/
theorem postFee_pending_checked
    (oracle : DenoteOracle) (fs : List Field) (s t : DenoteState)
    (psp feeVal pscMinus : Nat)
    (hpsp : lookupValue s.bindings "postSlashPendingFee" = psp)
    (hfee : lookupValue s.bindings "fee" = feeVal)
    (htmp37 : lookupValue s.bindings "_verity_slice_tmp_37" = pscMinus)
    (hpsp_le : psp ≤ max128)
    (h : execStmtList oracle fs s
      [.letVar "_verity_slice_tmp_38"
          (.bitAnd (.localVar "postSlashPendingFee") (.literal max128)),
       .letVar "_verity_slice_tmp_39" (.localVar "_verity_slice_tmp_38"),
       .letVar "_verity_slice_tmp_40" (.literal 0),
       .ite (.lt (.localVar "_verity_slice_tmp_39") (.localVar "fee"))
         [.panic .arithmeticOverflow]
         [.assignVar "_verity_slice_tmp_40"
            (.sub (.localVar "_verity_slice_tmp_39") (.localVar "fee"))],
       .letVar "_verity_slice_tmp_41" (.localVar "_verity_slice_tmp_40")] =
      .continue t) :
    feeVal ≤ psp ∧
    lookupValue t.bindings "_verity_slice_tmp_41" = psp - feeVal ∧
    lookupValue t.bindings "_verity_slice_tmp_37" = pscMinus ∧
    lookupValue t.bindings "fee" = feeVal := by
  have he_psp := eval_local_eq oracle fs s "postSlashPendingFee" psp hpsp
  have he_mask := eval_bitAnd_mask oracle fs s (.localVar "postSlashPendingFee") psp he_psp hpsp_le
  have step38 := exec_let_continue oracle fs s "_verity_slice_tmp_38" _ psp he_mask
  set s38 : DenoteState :=
    { s with bindings := bindValue s.bindings "_verity_slice_tmp_38" psp }
  have he39 : evalExpr oracle fs s38 (.localVar "_verity_slice_tmp_38") = some psp := by
    simp only [evalExpr, s38, lookup_bind_same]
  have step39 := exec_let_continue oracle fs s38 "_verity_slice_tmp_39" _ psp he39
  set s39 : DenoteState :=
    { s38 with bindings := bindValue s38.bindings "_verity_slice_tmp_39" psp }
  have step40 := exec_let_continue oracle fs s39 "_verity_slice_tmp_40" (.literal 0) 0
    (eval_lit_zero _ _ _)
  set s40 : DenoteState :=
    { s39 with bindings := bindValue s39.bindings "_verity_slice_tmp_40" 0 }
  have hfee40 : lookupValue s40.bindings "fee" = feeVal := by
    simp only [s40, s39, s38]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), hfee]
  have htmp37_40 : lookupValue s40.bindings "_verity_slice_tmp_37" = pscMinus := by
    simp only [s40, s39, s38]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), htmp37]
  have htmp39 : lookupValue s40.bindings "_verity_slice_tmp_39" = psp := by
    simp only [s40, s39]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_same]
  have he_tmp39 := eval_local_eq oracle fs s40 "_verity_slice_tmp_39" psp htmp39
  have he_fee := eval_local_eq oracle fs s40 "fee" feeVal hfee40
  have hlist :
      [Stmt.letVar "_verity_slice_tmp_38"
          (Expr.bitAnd (Expr.localVar "postSlashPendingFee") (Expr.literal max128)),
       Stmt.letVar "_verity_slice_tmp_39" (Expr.localVar "_verity_slice_tmp_38"),
       Stmt.letVar "_verity_slice_tmp_40" (Expr.literal 0),
       Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))
         [Stmt.panic PanicCode.arithmeticOverflow]
         [Stmt.assignVar "_verity_slice_tmp_40"
            (Expr.sub (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))],
       Stmt.letVar "_verity_slice_tmp_41" (Expr.localVar "_verity_slice_tmp_40")] =
      [Stmt.letVar "_verity_slice_tmp_38"
          (Expr.bitAnd (Expr.localVar "postSlashPendingFee") (Expr.literal max128))] ++
      [Stmt.letVar "_verity_slice_tmp_39" (Expr.localVar "_verity_slice_tmp_38"),
       Stmt.letVar "_verity_slice_tmp_40" (Expr.literal 0),
       Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))
         [Stmt.panic PanicCode.arithmeticOverflow]
         [Stmt.assignVar "_verity_slice_tmp_40"
            (Expr.sub (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))],
       Stmt.letVar "_verity_slice_tmp_41" (Expr.localVar "_verity_slice_tmp_40")] := rfl
  rw [hlist, exec_append, step38] at h
  change execStmtList oracle fs s38
      [Stmt.letVar "_verity_slice_tmp_39" (Expr.localVar "_verity_slice_tmp_38"),
       Stmt.letVar "_verity_slice_tmp_40" (Expr.literal 0),
       Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))
         [Stmt.panic PanicCode.arithmeticOverflow]
         [Stmt.assignVar "_verity_slice_tmp_40"
            (Expr.sub (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))],
       Stmt.letVar "_verity_slice_tmp_41" (Expr.localVar "_verity_slice_tmp_40")] =
      .continue t at h
  rw [exec_cons_continue (t := s39) (hhead := step39),
    exec_cons_continue (t := s40) (hhead := step40)] at h
  have hlt := eval_lt_of_vals oracle fs s40
    (.localVar "_verity_slice_tmp_39") (.localVar "fee") psp feeVal he_tmp39 he_fee
  by_cases hltPf : psp < feeVal
  · have hbw : boolWord (decide (psp < feeVal)) = 1 := boolWord_true_of hltPf
    have hcond1 : evalExpr oracle fs s40
        (.lt (.localVar "_verity_slice_tmp_39") (.localVar "fee")) = some 1 := by
      simp [hlt, hbw]
    have hflat :
        [Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))
           [Stmt.panic PanicCode.arithmeticOverflow]
           [Stmt.assignVar "_verity_slice_tmp_40"
              (Expr.sub (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))],
         Stmt.letVar "_verity_slice_tmp_41" (Expr.localVar "_verity_slice_tmp_40")] =
        [Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))
           [Stmt.panic PanicCode.arithmeticOverflow]
           [Stmt.assignVar "_verity_slice_tmp_40"
              (Expr.sub (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))]] ++
        [Stmt.letVar "_verity_slice_tmp_41" (Expr.localVar "_verity_slice_tmp_40")] := rfl
    rw [hflat, exec_append, exec_ite_one oracle fs s40 _ _ _ hcond1] at h
    simp only [exec_singleton, execStmt] at h
    cases h
  · have hle : feeVal ≤ psp := Nat.not_lt.mp hltPf
    have hbw : boolWord (decide (psp < feeVal)) = 0 := boolWord_false_of_not hltPf
    have hcond0 : evalExpr oracle fs s40
        (.lt (.localVar "_verity_slice_tmp_39") (.localVar "fee")) = some 0 := by
      simp [hlt, hbw]
    have hpsp_mod : psp < Uint256.modulus := lt_of_le_of_lt hpsp_le max128_lt
    have step_ite := exec_checked_sub oracle fs s40 "_verity_slice_tmp_40"
      (.localVar "_verity_slice_tmp_39") (.localVar "fee") psp feeVal
      he_tmp39 he_fee hpsp_mod hle
    set sSub : DenoteState :=
      { s40 with bindings := bindValue s40.bindings "_verity_slice_tmp_40" (psp - feeVal) }
    have he41 : evalExpr oracle fs sSub (.localVar "_verity_slice_tmp_40") =
        some (psp - feeVal) := by
      simp only [evalExpr, sSub, lookup_bind_same]
    have step41 := exec_let_continue oracle fs sSub "_verity_slice_tmp_41" _ (psp - feeVal) he41
    set s41 : DenoteState :=
      { sSub with bindings := bindValue sSub.bindings "_verity_slice_tmp_41" (psp - feeVal) }
    have hexec :
        execStmtList oracle fs s40
          [Stmt.ite (Expr.lt (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))
             [Stmt.panic PanicCode.arithmeticOverflow]
             [Stmt.assignVar "_verity_slice_tmp_40"
                (Expr.sub (Expr.localVar "_verity_slice_tmp_39") (Expr.localVar "fee"))],
           Stmt.letVar "_verity_slice_tmp_41" (Expr.localVar "_verity_slice_tmp_40")] =
          .continue s41 := by
      rw [exec_cons_continue (t := sSub) (hhead := step_ite)]
      exact step41
    rw [hexec] at h
    have hsEq : t = s41 := StmtOutcome.continue.inj h.symm
    subst hsEq
    refine ⟨hle, ?_, ?_, ?_⟩
    · simp only [s41, lookup_bind_same]
    · simp only [s41, sSub, s40, s39, s38]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), htmp37]
    · simp only [s41, sSub, s40, s39, s38]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), hfee]

/-- After a successful `.stop` of `postFee`, the three return words are
`psc - fee`, `psp - fee`, and `fee`. -/
theorem postFee_stop_return
    (oracle : DenoteOracle) (fs : List Field) (s final : DenoteState)
    (psc psp feeVal : Nat)
    (hpsc : lookupValue s.bindings "postSlashCredit" = psc)
    (hpsp : lookupValue s.bindings "postSlashPendingFee" = psp)
    (hfee : lookupValue s.bindings "fee" = feeVal)
    (hpsc_le : psc ≤ max128)
    (hpsp_le : psp ≤ max128)
    (h : execStmtList oracle fs s postFee = .stop final) :
    ∃ (w0 w1 w2 : Nat),
      final.observedReturnWords = some [w0, w1, w2] ∧
      w2 = feeVal ∧
      feeVal ≤ psc ∧ w0 = psc - feeVal ∧
      feeVal ≤ psp ∧ w1 = psp - feeVal := by
  rw [postFee_eq_pre_return] at h
  obtain ⟨sPre, hPre, hRet⟩ :=
    split_prefix oracle fs s final postFeePre [.returnValues retArgs]
      postFeePre_prefix h
  -- Split postFeePre into credit half ++ pending half.
  set creditHalf : List Stmt :=
    [.letVar "_verity_slice_tmp_34"
        (.bitAnd (.localVar "postSlashCredit") (.literal max128)),
     .letVar "_verity_slice_tmp_35" (.localVar "_verity_slice_tmp_34"),
     .letVar "_verity_slice_tmp_36" (.literal 0),
     .ite (.lt (.localVar "_verity_slice_tmp_35") (.localVar "fee"))
       [.panic .arithmeticOverflow]
       [.assignVar "_verity_slice_tmp_36"
          (.sub (.localVar "_verity_slice_tmp_35") (.localVar "fee"))],
     .letVar "_verity_slice_tmp_37" (.localVar "_verity_slice_tmp_36")]
  set pendingHalf : List Stmt :=
    [.letVar "_verity_slice_tmp_38"
        (.bitAnd (.localVar "postSlashPendingFee") (.literal max128)),
     .letVar "_verity_slice_tmp_39" (.localVar "_verity_slice_tmp_38"),
     .letVar "_verity_slice_tmp_40" (.literal 0),
     .ite (.lt (.localVar "_verity_slice_tmp_39") (.localVar "fee"))
       [.panic .arithmeticOverflow]
       [.assignVar "_verity_slice_tmp_40"
          (.sub (.localVar "_verity_slice_tmp_39") (.localVar "fee"))],
     .letVar "_verity_slice_tmp_41" (.localVar "_verity_slice_tmp_40")]
  have hPre_eq : postFeePre = creditHalf ++ pendingHalf := by
    simp only [postFeePre_concrete, creditHalf, pendingHalf]
    rfl
  rw [hPre_eq] at hPre
  obtain ⟨sCred, hCred, hPend⟩ :=
    split_prefix_continue oracle fs s sPre creditHalf pendingHalf hPre
  have hCred' := postFee_credit_checked oracle fs s sCred psc feeVal
    hpsc hfee hpsc_le hCred
  rcases hCred' with ⟨hle_c, htmp37, hfeeCred, hpspCred⟩
  have hpspCred' : lookupValue sCred.bindings "postSlashPendingFee" = psp := by
    rw [hpspCred, hpsp]
  have hPend' := postFee_pending_checked oracle fs sCred sPre psp feeVal (psc - feeVal)
    hpspCred' hfeeCred htmp37 hpsp_le hPend
  rcases hPend' with ⟨hle_p, htmp41, htmp37', hfeePre⟩
  -- Evaluate the return list.
  simp only [exec_singleton, execStmt, retArgs_concrete] at hRet
  have he37 : evalExpr oracle fs sPre (.localVar "_verity_slice_tmp_37") =
      some (psc - feeVal) := by
    simp only [evalExpr, htmp37']
  have he41 : evalExpr oracle fs sPre (.localVar "_verity_slice_tmp_41") =
      some (psp - feeVal) := by
    simp only [evalExpr, htmp41]
  have heFee : evalExpr oracle fs sPre (.localVar "fee") = some feeVal := by
    simp only [evalExpr, hfeePre]
  have hlist :
      evalExprList oracle fs sPre
        [.localVar "_verity_slice_tmp_37",
         .localVar "_verity_slice_tmp_41",
         .localVar "fee"] =
        some [psc - feeVal, psp - feeVal, feeVal] := by
    simp only [evalExprList, he37, he41, heFee, bind, pure, Option.bind]
  rw [hlist] at hRet
  cases hRet
  refine ⟨wordNormalize (psc - feeVal), wordNormalize (psp - feeVal), wordNormalize feeVal,
    rfl, ?_, hle_c, ?_, hle_p, ?_⟩
  · have hfee_le : feeVal ≤ max128 := le_trans hle_c hpsc_le
    exact wordNormalize_of_le hfee_le
  · have hw0 : psc - feeVal ≤ max128 := le_trans (Nat.sub_le _ _) hpsc_le
    exact (wordNormalize_of_le hw0).symm ▸ rfl
  · have hw1 : psp - feeVal ≤ max128 := le_trans (Nat.sub_le _ _) hpsp_le
    exact (wordNormalize_of_le hw1).symm ▸ rfl

end Midnight.Lemmas
