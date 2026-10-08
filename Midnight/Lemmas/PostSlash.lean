import Midnight.Lemmas.Exec

/-!
Characterization of `postSlashCredit` after a successful `preCredit` prefix,
and of `postSlashPendingFee` after a successful `midPending` prefix.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas
open Midnight.Spec

namespace Midnight.Lemmas

/-- Slash formula matching the Solidity ternary. -/
def slashFormula (credit lastLoss loss : Nat) : Nat :=
  if lastLoss < max128 then credit * (max128 - loss) / (max128 - lastLoss) else 0

/-- After a successful `preCredit` continue, the post-slash binding and inputs. -/
structure PostSlashState
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) (s : DenoteState) : Prop where
  credit_eq : lookupValue s.bindings "_credit" =
    (midnight.position.credit oracle world id user).val
  lastLoss_eq : lookupValue s.bindings "_lastLossFactor" =
    (midnight.position.lastLossFactor oracle world id user).val
  postSlash_eq : lookupValue s.bindings "postSlashCredit" =
    slashFormula
      (midnight.position.credit oracle world id user).val
      (midnight.position.lastLossFactor oracle world id user).val
      (midnight.marketState.lossFactor oracle world id).val
  world_eq : s.world = world

theorem eval_lit_zero (oracle : DenoteOracle) (fs : List Field) (s : DenoteState) :
    evalExpr oracle fs s (.literal 0) = some 0 := by
  change some (wordNormalize 0) = some 0
  simp [wordNormalize, Uint256.ofNat]

theorem eval_lit_max128 (oracle : DenoteOracle) (fs : List Field) (s : DenoteState) :
    evalExpr oracle fs s (.literal max128) = some max128 := by
  simp [evalExpr, wordNormalize_max128]

theorem eval_local_eq
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState) (n : String) (v : Nat)
    (h : lookupValue s.bindings n = v) :
    evalExpr oracle fs s (.localVar n) = some v := by
  simp [evalExpr, h]

/-- Helper: execute a single successful `letVar`. -/
theorem exec_let_continue
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (n : String) (e : Expr) (v : Nat)
    (hv : evalExpr oracle fs s e = some v) :
    execStmtList oracle fs s [.letVar n e] =
      .continue { s with bindings := bindValue s.bindings n v } := by
  simp only [exec_singleton, execStmt, hv]

/-- Helper: execute a single successful `assignVar`. -/
theorem exec_assign_continue
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (n : String) (e : Expr) (v : Nat)
    (hv : evalExpr oracle fs s e = some v) :
    execStmtList oracle fs s [.assignVar n e] =
      .continue { s with bindings := bindValue s.bindings n v } := by
  simp only [exec_singleton, execStmt, hv]

theorem eval_lt_of_vals
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b) :
    evalExpr oracle fs s (.lt ea eb) = some (boolWord (decide (a < b))) := by
  simp [evalExpr, ha, hb]

theorem eval_eq_of_vals
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b) :
    evalExpr oracle fs s (.eq ea eb) = some (boolWord (decide (a = b))) := by
  simp [evalExpr, ha, hb]

theorem eval_gt_of_vals
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b) :
    evalExpr oracle fs s (.gt ea eb) = some (boolWord (decide (b < a))) := by
  simp [evalExpr, ha, hb]

theorem eval_sub_of_vals
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b)
    (haBound : a < Uint256.modulus) (hb_le : b ≤ a) :
    evalExpr oracle fs s (.sub ea eb) = some (a - b) := by
  simp only [evalExpr, ha, hb, Option.bind]
  exact congrArg some (sub_word haBound hb_le)

theorem eval_mul_of_vals128
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b)
    (haBound : a ≤ max128) (hbBound : b ≤ max128) :
    evalExpr oracle fs s (.mul ea eb) = some (a * b) := by
  simp only [evalExpr, ha, hb, Option.bind]
  exact congrArg some (mul_word128 haBound hbBound)

theorem eval_div_of_vals
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b)
    (haBound : a < Uint256.modulus) (hbBound : b < Uint256.modulus) :
    evalExpr oracle fs s (.div ea eb) = some (a / b) := by
  simp only [evalExpr, ha, hb, Option.bind]
  exact congrArg some (div_word haBound hbBound)

theorem boolWord_false_of_not {p : Prop} [Decidable p] (h : ¬ p) :
    boolWord (decide p) = 0 := by
  simp [boolWord, h]

theorem boolWord_true_of {p : Prop} [Decidable p] (h : p) :
    boolWord (decide p) = 1 := by
  simp [boolWord, h]

/-- An `ite` whose condition evaluates to nonzero runs the then-branch list. -/
theorem exec_ite_true
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (cond : Expr) (yes no : List Stmt) (c : Nat)
    (hc : evalExpr oracle fs s cond = some c) (hne : c ≠ 0) :
    execStmtList oracle fs s [.ite cond yes no] =
      execStmtList oracle fs s yes := by
  simp only [exec_singleton, execStmt, hc]
  simp [hne]

/-- An `ite` whose condition evaluates to zero runs the else-branch list. -/
theorem exec_ite_false
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (cond : Expr) (yes no : List Stmt) (c : Nat)
    (hc : evalExpr oracle fs s cond = some c) (h0 : c = 0) :
    execStmtList oracle fs s [.ite cond yes no] =
      execStmtList oracle fs s no := by
  subst h0
  simp only [exec_singleton, execStmt, hc]
  simp

/-- An `ite` whose condition evaluates to one runs the then-branch list. -/
theorem exec_ite_one
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (cond : Expr) (yes no : List Stmt)
    (hc : evalExpr oracle fs s cond = some 1) :
    execStmtList oracle fs s [.ite cond yes no] =
      execStmtList oracle fs s yes := by
  simp only [exec_singleton, execStmt, hc]
  simp

/-- Successful continue of a checked underflow-guarded subtraction (singleton ite). -/
theorem exec_checked_sub
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (tmp : String) (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b)
    (haBound : a < Uint256.modulus) (hle : b ≤ a) :
    execStmtList oracle fs s
      [.ite (.lt ea eb) [.panic .arithmeticOverflow]
         [.assignVar tmp (.sub ea eb)]] =
      .continue { s with bindings := bindValue s.bindings tmp (a - b) } := by
  have hlt := eval_lt_of_vals oracle fs s ea eb a b ha hb
  have hsub := eval_sub_of_vals oracle fs s ea eb a b ha hb haBound hle
  have hbw : boolWord (decide (a < b)) = 0 :=
    boolWord_false_of_not (Nat.not_lt.mpr hle)
  rw [exec_ite_false oracle fs s _ _ _ _ hlt hbw]
  exact exec_assign_continue oracle fs s tmp _ _ hsub

/-- Successful continue of a checked division (nonzero divisor). -/
theorem exec_checked_div
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (tmp : String) (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b)
    (haBound : a < Uint256.modulus) (hbBound : b < Uint256.modulus) (hbpos : b ≠ 0) :
    execStmtList oracle fs s
      [.ite (.eq eb (.literal 0)) [.panic .divisionByZero]
         [.assignVar tmp (.div ea eb)]] =
      .continue { s with bindings := bindValue s.bindings tmp (a / b) } := by
  have h0 := eval_lit_zero oracle fs s
  have heq := eval_eq_of_vals oracle fs s eb (.literal 0) b 0 hb h0
  have hdiv := eval_div_of_vals oracle fs s ea eb a b ha hb haBound hbBound
  have hbw : boolWord (decide (b = 0)) = 0 := boolWord_false_of_not hbpos
  rw [exec_ite_false oracle fs s _ _ _ _ heq hbw]
  exact exec_assign_continue oracle fs s tmp _ _ hdiv

/-- Successful continue of the checked multiplication used by `mulDivDown`. -/
theorem exec_checked_mul128
    (oracle : DenoteOracle) (fs : List Field) (s : DenoteState)
    (tmp : String) (ea eb : Expr) (a b : Nat)
    (ha : evalExpr oracle fs s ea = some a) (hb : evalExpr oracle fs s eb = some b)
    (haBound : a ≤ max128) (hbBound : b ≤ max128) :
    execStmtList oracle fs s
      [.ite (.eq ea (.literal 0))
         [.assignVar tmp (.mul ea eb)]
         [.ite (.eq (.div (.mul ea eb) ea) eb)
            [.assignVar tmp (.mul ea eb)]
            [.panic .arithmeticOverflow]]] =
      .continue { s with bindings := bindValue s.bindings tmp (a * b) } := by
  have h0 := eval_lit_zero oracle fs s
  have heq0 := eval_eq_of_vals oracle fs s ea (.literal 0) a 0 ha h0
  have hmul := eval_mul_of_vals128 oracle fs s ea eb a b ha hb haBound hbBound
  have haMod : a < Uint256.modulus := lt_of_le_of_lt haBound max128_lt
  have hprod_lt : a * b < Uint256.modulus :=
    lt_of_le_of_lt (Nat.mul_le_mul haBound hbBound) (by decide)
  by_cases ha0 : a = 0
  · have hbw : boolWord (decide (a = 0)) = 1 := boolWord_true_of ha0
    have heq0' : evalExpr oracle fs s (.eq ea (.literal 0)) = some 1 := by
      simpa [hbw] using heq0
    rw [exec_ite_one oracle fs s _ _ _ heq0']
    exact exec_assign_continue oracle fs s tmp _ _ hmul
  · have hbw : boolWord (decide (a = 0)) = 0 := boolWord_false_of_not ha0
    rw [exec_ite_false oracle fs s _ _ _ _ heq0 hbw]
    have hdiv_ev := eval_div_of_vals oracle fs s (.mul ea eb) ea (a * b) a hmul ha
      hprod_lt haMod
    have hdiv_id : a * b / a = b := by
      rw [Nat.mul_comm]; exact Nat.mul_div_left b (Nat.pos_of_ne_zero ha0)
    have heq_chk := eval_eq_of_vals oracle fs s (.div (.mul ea eb) ea) eb (a * b / a) b
      hdiv_ev hb
    have heq_chk' : evalExpr oracle fs s
        (.eq (.div (.mul ea eb) ea) eb) = some 1 := by
      simpa [hdiv_id, boolWord] using heq_chk
    rw [exec_ite_one oracle fs s _ _ _ heq_chk']
    exact exec_assign_continue oracle fs s tmp _ _ hmul

/-- Bind `_credit` and `_lastLossFactor` from storage. -/
theorem exec_credit_and_lastLoss
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (mat : Uint256) (id : BytesN 32) (user : Address) :
    ∃ s,
      execStmtList oracle midnight.model.fields (initState world mat id user)
        [.letVar "_credit"
          (.structMember2 "position" (.param "id") (.param "user") "credit"),
         .letVar "_lastLossFactor"
          (.structMember2 "position" (.param "id") (.param "user") "lastLossFactor")] =
        .continue s ∧
      lookupValue s.bindings "_credit" =
        (midnight.position.credit oracle world id user).val ∧
      lookupValue s.bindings "_lastLossFactor" =
        (midnight.position.lastLossFactor oracle world id user).val ∧
      lookupValue s.bindings "id" = id.val ∧
      lookupValue s.bindings "user" = user.val ∧
      s.world = world := by
  set s0 := initState world mat id user
  have hworld0 : s0.world = world := rfl
  have hid : lookupValue s0.bindings "id" = id.val := by
    simp [s0, initState, callBindings, lookupValue, Word.toWord]
  have huser : lookupValue s0.bindings "user" = user.val := by
    simp [s0, initState, callBindings, lookupValue, Word.toWord]
  have hcredit := evalExpr_structMember2_param oracle midnight.model s0
    "position" "id" "user" "credit" position_credit_ready
  simp only [hid, huser, credit_read_eq, hworld0] at hcredit
  set credit := (midnight.position.credit oracle world id user).val
  set s1 : DenoteState :=
    { s0 with bindings := bindValue s0.bindings "_credit" credit }
  have hid1 : lookupValue s1.bindings "id" = id.val := by
    simp only [s1]
    rw [lookup_bind_other _ _ _ _ (by decide : "_credit" ≠ "id"), hid]
  have huser1 : lookupValue s1.bindings "user" = user.val := by
    simp only [s1]
    rw [lookup_bind_other _ _ _ _ (by decide : "_credit" ≠ "user"), huser]
  have hlast := evalExpr_structMember2_param oracle midnight.model s1
    "position" "id" "user" "lastLossFactor" position_lastLossFactor_ready
  simp only [hid1, huser1, lastLossFactor_read_eq, s1, hworld0] at hlast
  set lastLoss := (midnight.position.lastLossFactor oracle world id user).val
  set s2 : DenoteState :=
    { s1 with bindings := bindValue s1.bindings "_lastLossFactor" lastLoss }
  refine ⟨s2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [exec_let_cons, hcredit]
    exact exec_let_continue oracle midnight.model.fields s1 "_lastLossFactor" _ lastLoss hlast
  · simp only [s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide : "_lastLossFactor" ≠ "_credit"),
      lookup_bind_same]
  · simp only [s2, lookup_bind_same]
  · simp only [s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide : "_lastLossFactor" ≠ "id"),
      lookup_bind_other _ _ _ _ (by decide : "_credit" ≠ "id"), hid]
  · simp only [s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide : "_lastLossFactor" ≠ "user"),
      lookup_bind_other _ _ _ _ (by decide : "_credit" ≠ "user"), huser]
  · rfl

/-- Binding facts after credit and lastLoss have been loaded. -/
structure CreditLastLoss
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) (s : DenoteState) : Prop where
  credit_eq : lookupValue s.bindings "_credit" =
    (midnight.position.credit oracle world id user).val
  lastLoss_eq : lookupValue s.bindings "_lastLossFactor" =
    (midnight.position.lastLossFactor oracle world id user).val
  id_eq : lookupValue s.bindings "id" = id.val
  world_eq : s.world = world

/-- Chain `exec_append` for a singleton head that continues. -/
theorem exec_cons_continue
    (oracle : DenoteOracle) (fs : List Field) (s t : DenoteState)
    (stmt : Stmt) (rest : List Stmt)
    (hhead : execStmtList oracle fs s [stmt] = .continue t) :
    execStmtList oracle fs s (stmt :: rest) =
      execStmtList oracle fs t rest := by
  have happ := exec_append oracle fs s [stmt] rest
  simp only [List.singleton_append] at happ
  rw [happ, hhead]


set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- Concrete shape of `preCredit` (definitionally equal). -/
theorem preCredit_concrete : preCredit =
[Stmt.letVar
   "_credit"
   (Expr.structMember2
     "position"
     (Expr.param "id")
     (Expr.param "user")
     "credit"),
 Stmt.letVar
   "_lastLossFactor"
   (Expr.structMember2
     "position"
     (Expr.param "id")
     (Expr.param "user")
     "lastLossFactor"),
 Stmt.letVar
   "_verity_slice_tmp_0"
   (Expr.lt
     (Expr.localVar "_lastLossFactor")
     (Expr.literal 340282366920938463463374607431768211455)),
 Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
 Stmt.ite
   (Expr.localVar "_verity_slice_tmp_0")
   [Stmt.letVar
      "_verity_slice_tmp_1"
      (Expr.structMember
        "marketState"
        (Expr.param "id")
        "lossFactor"),
    Stmt.letVar "_verity_slice_tmp_2" (Expr.literal 0),
    Stmt.ite
      (Expr.lt
        (Expr.literal 340282366920938463463374607431768211455)
        (Expr.localVar "_verity_slice_tmp_1"))
      [Stmt.panic (PanicCode.arithmeticOverflow)]
      [Stmt.assignVar
         "_verity_slice_tmp_2"
         (Expr.sub
           (Expr.literal 340282366920938463463374607431768211455)
           (Expr.localVar "_verity_slice_tmp_1"))],
    Stmt.letVar
      "_verity_slice_tmp_4"
      (Expr.localVar "_verity_slice_tmp_2"),
    Stmt.letVar "_verity_slice_tmp_3" (Expr.literal 0),
    Stmt.ite
      (Expr.lt
        (Expr.literal 340282366920938463463374607431768211455)
        (Expr.localVar "_lastLossFactor"))
      [Stmt.panic (PanicCode.arithmeticOverflow)]
      [Stmt.assignVar
         "_verity_slice_tmp_3"
         (Expr.sub
           (Expr.literal 340282366920938463463374607431768211455)
           (Expr.localVar "_lastLossFactor"))],
    Stmt.letVar
      "_verity_slice_tmp_5"
      (Expr.localVar "_verity_slice_tmp_3"),
    Stmt.letVar "_verity_slice_tmp_6" (Expr.literal 0),
    Stmt.ite
      (Expr.eq
        (Expr.localVar "_credit")
        (Expr.literal 0))
      [Stmt.assignVar
         "_verity_slice_tmp_6"
         (Expr.mul
           (Expr.localVar "_credit")
           (Expr.localVar "_verity_slice_tmp_4"))]
      [Stmt.ite
         (Expr.eq
           (Expr.div
             (Expr.mul
               (Expr.localVar "_credit")
               (Expr.localVar "_verity_slice_tmp_4"))
             (Expr.localVar "_credit"))
           (Expr.localVar "_verity_slice_tmp_4"))
         [Stmt.assignVar
            "_verity_slice_tmp_6"
            (Expr.mul
              (Expr.localVar "_credit")
              (Expr.localVar "_verity_slice_tmp_4"))]
         [Stmt.panic (PanicCode.arithmeticOverflow)]],
    Stmt.letVar
      "_verity_slice_tmp_7"
      (Expr.localVar "_verity_slice_tmp_6"),
    Stmt.letVar "_verity_slice_tmp_8" (Expr.literal 0),
    Stmt.ite
      (Expr.eq
        (Expr.localVar "_verity_slice_tmp_5")
        (Expr.literal 0))
      [Stmt.panic (PanicCode.divisionByZero)]
      [Stmt.assignVar
         "_verity_slice_tmp_8"
         (Expr.div
           (Expr.localVar "_verity_slice_tmp_7")
           (Expr.localVar "_verity_slice_tmp_5"))],
    Stmt.assignVar
      "_verity_slice_tmp_9"
      (Expr.localVar "_verity_slice_tmp_8")]
   [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
 Stmt.letVar
   "postSlashCredit"
   (Expr.localVar "_verity_slice_tmp_9")]
:= rfl

/-- Concrete shape of `midPending` (definitionally equal). -/
theorem midPending_concrete : midPending =
[Stmt.letVar
   "_pendingFee"
   (Expr.structMember2
     "position"
     (Expr.param "id")
     (Expr.param "user")
     "pendingFee"),
 Stmt.letVar
   "_verity_slice_tmp_10"
   (Expr.gt
     (Expr.localVar "_credit")
     (Expr.literal 0)),
 Stmt.letVar "_verity_slice_tmp_22" (Expr.literal 0),
 Stmt.ite
   (Expr.localVar "_verity_slice_tmp_10")
   [Stmt.letVar "_verity_slice_tmp_11" (Expr.literal 0),
    Stmt.ite
      (Expr.lt
        (Expr.localVar "_credit")
        (Expr.localVar "postSlashCredit"))
      [Stmt.panic (PanicCode.arithmeticOverflow)]
      [Stmt.assignVar
         "_verity_slice_tmp_11"
         (Expr.sub
           (Expr.localVar "_credit")
           (Expr.localVar "postSlashCredit"))],
    Stmt.letVar
      "_verity_slice_tmp_12"
      (Expr.localVar "_verity_slice_tmp_11"),
    Stmt.letVar "_verity_slice_tmp_13" (Expr.literal 0),
    Stmt.ite
      (Expr.eq
        (Expr.localVar "_pendingFee")
        (Expr.literal 0))
      [Stmt.assignVar
         "_verity_slice_tmp_13"
         (Expr.mul
           (Expr.localVar "_pendingFee")
           (Expr.localVar "_verity_slice_tmp_12"))]
      [Stmt.ite
         (Expr.eq
           (Expr.div
             (Expr.mul
               (Expr.localVar "_pendingFee")
               (Expr.localVar "_verity_slice_tmp_12"))
             (Expr.localVar "_pendingFee"))
           (Expr.localVar "_verity_slice_tmp_12"))
         [Stmt.assignVar
            "_verity_slice_tmp_13"
            (Expr.mul
              (Expr.localVar "_pendingFee")
              (Expr.localVar "_verity_slice_tmp_12"))]
         [Stmt.panic (PanicCode.arithmeticOverflow)]],
    Stmt.letVar
      "_verity_slice_tmp_15"
      (Expr.localVar "_verity_slice_tmp_13"),
    Stmt.letVar "_verity_slice_tmp_14" (Expr.literal 0),
    Stmt.ite
      (Expr.lt
        (Expr.localVar "_credit")
        (Expr.literal 1))
      [Stmt.panic (PanicCode.arithmeticOverflow)]
      [Stmt.assignVar
         "_verity_slice_tmp_14"
         (Expr.sub
           (Expr.localVar "_credit")
           (Expr.literal 1))],
    Stmt.letVar
      "_verity_slice_tmp_16"
      (Expr.localVar "_verity_slice_tmp_14"),
    Stmt.letVar "_verity_slice_tmp_17" (Expr.literal 0),
    Stmt.ite
      (Expr.lt
        (Expr.add
          (Expr.localVar "_verity_slice_tmp_15")
          (Expr.localVar "_verity_slice_tmp_16"))
        (Expr.localVar "_verity_slice_tmp_15"))
      [Stmt.panic (PanicCode.arithmeticOverflow)]
      [Stmt.assignVar
         "_verity_slice_tmp_17"
         (Expr.add
           (Expr.localVar "_verity_slice_tmp_15")
           (Expr.localVar "_verity_slice_tmp_16"))],
    Stmt.letVar
      "_verity_slice_tmp_18"
      (Expr.localVar "_verity_slice_tmp_17"),
    Stmt.letVar "_verity_slice_tmp_19" (Expr.literal 0),
    Stmt.ite
      (Expr.eq
        (Expr.localVar "_credit")
        (Expr.literal 0))
      [Stmt.panic (PanicCode.divisionByZero)]
      [Stmt.assignVar
         "_verity_slice_tmp_19"
         (Expr.div
           (Expr.localVar "_verity_slice_tmp_18")
           (Expr.localVar "_credit"))],
    Stmt.letVar
      "_verity_slice_tmp_20"
      (Expr.localVar "_verity_slice_tmp_19"),
    Stmt.letVar "_verity_slice_tmp_21" (Expr.literal 0),
    Stmt.ite
      (Expr.lt
        (Expr.localVar "_pendingFee")
        (Expr.localVar "_verity_slice_tmp_20"))
      [Stmt.panic (PanicCode.arithmeticOverflow)]
      [Stmt.assignVar
         "_verity_slice_tmp_21"
         (Expr.sub
           (Expr.localVar "_pendingFee")
           (Expr.localVar "_verity_slice_tmp_20"))],
    Stmt.assignVar
      "_verity_slice_tmp_22"
      (Expr.localVar "_verity_slice_tmp_21")]
   [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)],
 Stmt.letVar
   "postSlashPendingFee"
   (Expr.localVar "_verity_slice_tmp_22")]
:= rfl

end Midnight.Lemmas
