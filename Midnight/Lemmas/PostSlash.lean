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

def slashThenBranch : List Stmt :=
  [.letVar "_verity_slice_tmp_1"
      (.structMember "marketState" (.param "id") "lossFactor"),
   .letVar "_verity_slice_tmp_2" (.literal 0),
   .ite (.lt (.literal max128) (.localVar "_verity_slice_tmp_1"))
     [.panic .arithmeticOverflow]
     [.assignVar "_verity_slice_tmp_2"
       (.sub (.literal max128) (.localVar "_verity_slice_tmp_1"))],
   .letVar "_verity_slice_tmp_4" (.localVar "_verity_slice_tmp_2"),
   .letVar "_verity_slice_tmp_3" (.literal 0),
   .ite (.lt (.literal max128) (.localVar "_lastLossFactor"))
     [.panic .arithmeticOverflow]
     [.assignVar "_verity_slice_tmp_3"
       (.sub (.literal max128) (.localVar "_lastLossFactor"))],
   .letVar "_verity_slice_tmp_5" (.localVar "_verity_slice_tmp_3"),
   .letVar "_verity_slice_tmp_6" (.literal 0),
   .ite (.eq (.localVar "_credit") (.literal 0))
     [.assignVar "_verity_slice_tmp_6"
       (.mul (.localVar "_credit") (.localVar "_verity_slice_tmp_4"))]
     [.ite (.eq (.div (.mul (.localVar "_credit") (.localVar "_verity_slice_tmp_4"))
         (.localVar "_credit")) (.localVar "_verity_slice_tmp_4"))
       [.assignVar "_verity_slice_tmp_6"
         (.mul (.localVar "_credit") (.localVar "_verity_slice_tmp_4"))]
       [.panic .arithmeticOverflow]],
   .letVar "_verity_slice_tmp_7" (.localVar "_verity_slice_tmp_6"),
   .letVar "_verity_slice_tmp_8" (.literal 0),
   .ite (.eq (.localVar "_verity_slice_tmp_5") (.literal 0))
     [.panic .divisionByZero]
     [.assignVar "_verity_slice_tmp_8"
       (.div (.localVar "_verity_slice_tmp_7") (.localVar "_verity_slice_tmp_5"))],
   .assignVar "_verity_slice_tmp_9" (.localVar "_verity_slice_tmp_8")]

theorem preCredit_parts :
    preCredit =
      [.letVar "_credit"
          (.structMember2 "position" (.param "id") (.param "user") "credit"),
       .letVar "_lastLossFactor"
          (.structMember2 "position" (.param "id") (.param "user") "lastLossFactor"),
       .letVar "_verity_slice_tmp_0"
          (.lt (.localVar "_lastLossFactor") (.literal max128)),
       .letVar "_verity_slice_tmp_9" (.literal 0),
       .ite (.localVar "_verity_slice_tmp_0") slashThenBranch
         [.assignVar "_verity_slice_tmp_9" (.literal 0)],
       .letVar "postSlashCredit" (.localVar "_verity_slice_tmp_9")] := by
  simp only [preCredit_concrete, slashThenBranch]
  rfl

/-- Collapse a chain of `lookup_bind_other` to the original env. -/
macro "keep_lookup" : tactic => `(tactic|
  (simp only [lookupValue] at *
   repeat rw [lookup_bind_other _ _ _ _ (by decide)]
   try rfl))

theorem exec_slash_then
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) (s : DenoteState)
    (hs : CreditLastLoss oracle world id user s)
    (hlast : (midnight.position.lastLossFactor oracle world id user).val < max128) :
    ∃ t,
      execStmtList oracle midnight.model.fields s slashThenBranch = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_9" =
        (midnight.position.credit oracle world id user).val *
          (max128 - (midnight.marketState.lossFactor oracle world id).val) /
          (max128 - (midnight.position.lastLossFactor oracle world id user).val) ∧
      lookupValue t.bindings "_credit" =
        (midnight.position.credit oracle world id user).val ∧
      lookupValue t.bindings "_lastLossFactor" =
        (midnight.position.lastLossFactor oracle world id user).val ∧
      lookupValue t.bindings "id" = id.val ∧
      t.world = world := by
  set credit := (midnight.position.credit oracle world id user).val
  set lastLoss := (midnight.position.lastLossFactor oracle world id user).val
  set loss := (midnight.marketState.lossFactor oracle world id).val
  have hcredit_le := credit_val_le_max oracle world id user
  have hlast_le := lastLossFactor_val_le_max oracle world id user
  have hloss_le := lossFactor_val_le_max oracle world id
  have hid := hs.id_eq
  have hworld := hs.world_eq
  have hloss_ev := evalExpr_structMember_param oracle midnight.model s
    "marketState" "id" "lossFactor" marketState_lossFactor_ready
  simp only [hid, lossFactor_read_eq, hworld] at hloss_ev
  have step1 := exec_let_continue oracle midnight.model.fields s
    "_verity_slice_tmp_1" _ loss hloss_ev
  set s1 : DenoteState := { s with bindings := bindValue s.bindings "_verity_slice_tmp_1" loss }
  have step2 := exec_let_continue oracle midnight.model.fields s1
    "_verity_slice_tmp_2" (.literal 0) 0 (eval_lit_zero _ _ _)
  set s2 : DenoteState := { s1 with bindings := bindValue s1.bindings "_verity_slice_tmp_2" 0 }
  have htmp1 : evalExpr oracle midnight.model.fields s2 (.localVar "_verity_slice_tmp_1") =
      some loss := by
    change some (lookupValue s2.bindings "_verity_slice_tmp_1") = some loss
    simp only [s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_same]
  have step3 := exec_checked_sub oracle midnight.model.fields s2
    "_verity_slice_tmp_2" (.literal max128) (.localVar "_verity_slice_tmp_1")
    max128 loss (eval_lit_max128 _ _ _) htmp1 max128_lt hloss_le
  set s3 : DenoteState :=
    { s2 with bindings := bindValue s2.bindings "_verity_slice_tmp_2" (max128 - loss) }
  have htmp2 : evalExpr oracle midnight.model.fields s3 (.localVar "_verity_slice_tmp_2") =
      some (max128 - loss) := by
    change some (lookupValue s3.bindings "_verity_slice_tmp_2") = some (max128 - loss)
    simp only [s3, lookup_bind_same]
  have step4 := exec_let_continue oracle midnight.model.fields s3
    "_verity_slice_tmp_4" _ (max128 - loss) htmp2
  set s4 : DenoteState :=
    { s3 with bindings := bindValue s3.bindings "_verity_slice_tmp_4" (max128 - loss) }
  have step5 := exec_let_continue oracle midnight.model.fields s4
    "_verity_slice_tmp_3" (.literal 0) 0 (eval_lit_zero _ _ _)
  set s5 : DenoteState := { s4 with bindings := bindValue s4.bindings "_verity_slice_tmp_3" 0 }
  have hlast_ev : evalExpr oracle midnight.model.fields s5 (.localVar "_lastLossFactor") =
      some lastLoss := by
    change some (lookupValue s5.bindings "_lastLossFactor") = some lastLoss
    simp only [s5, s4, s3, s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), hs.lastLoss_eq]
  have step6 := exec_checked_sub oracle midnight.model.fields s5
    "_verity_slice_tmp_3" (.literal max128) (.localVar "_lastLossFactor")
    max128 lastLoss (eval_lit_max128 _ _ _) hlast_ev max128_lt hlast_le
  set s6 : DenoteState :=
    { s5 with bindings := bindValue s5.bindings "_verity_slice_tmp_3" (max128 - lastLoss) }
  have htmp3 : evalExpr oracle midnight.model.fields s6 (.localVar "_verity_slice_tmp_3") =
      some (max128 - lastLoss) := by
    change some (lookupValue s6.bindings "_verity_slice_tmp_3") = some (max128 - lastLoss)
    simp only [s6, lookup_bind_same]
  have step7 := exec_let_continue oracle midnight.model.fields s6
    "_verity_slice_tmp_5" _ (max128 - lastLoss) htmp3
  set s7 : DenoteState :=
    { s6 with bindings := bindValue s6.bindings "_verity_slice_tmp_5" (max128 - lastLoss) }
  have step8 := exec_let_continue oracle midnight.model.fields s7
    "_verity_slice_tmp_6" (.literal 0) 0 (eval_lit_zero _ _ _)
  set s8 : DenoteState := { s7 with bindings := bindValue s7.bindings "_verity_slice_tmp_6" 0 }
  have hcredit_ev : evalExpr oracle midnight.model.fields s8 (.localVar "_credit") =
      some credit := by
    change some (lookupValue s8.bindings "_credit") = some credit
    simp only [s8, s7, s6, s5, s4, s3, s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      hs.credit_eq]
  have htmp4 : evalExpr oracle midnight.model.fields s8 (.localVar "_verity_slice_tmp_4") =
      some (max128 - loss) := by
    change some (lookupValue s8.bindings "_verity_slice_tmp_4") = some (max128 - loss)
    simp only [s8, s7, s6, s5, s4]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_same]
  have hnum_le : max128 - loss ≤ max128 := Nat.sub_le _ _
  have step9 := exec_checked_mul128 oracle midnight.model.fields s8
    "_verity_slice_tmp_6" (.localVar "_credit") (.localVar "_verity_slice_tmp_4")
    credit (max128 - loss) hcredit_ev htmp4 hcredit_le hnum_le
  set s9 : DenoteState :=
    { s8 with bindings := bindValue s8.bindings "_verity_slice_tmp_6" (credit * (max128 - loss)) }
  have htmp6 : evalExpr oracle midnight.model.fields s9 (.localVar "_verity_slice_tmp_6") =
      some (credit * (max128 - loss)) := by
    change some (lookupValue s9.bindings "_verity_slice_tmp_6") = some (credit * (max128 - loss))
    simp only [s9, lookup_bind_same]
  have step10 := exec_let_continue oracle midnight.model.fields s9
    "_verity_slice_tmp_7" _ (credit * (max128 - loss)) htmp6
  set s10 : DenoteState :=
    { s9 with bindings := bindValue s9.bindings "_verity_slice_tmp_7" (credit * (max128 - loss)) }
  have step11 := exec_let_continue oracle midnight.model.fields s10
    "_verity_slice_tmp_8" (.literal 0) 0 (eval_lit_zero _ _ _)
  set s11 : DenoteState := { s10 with bindings := bindValue s10.bindings "_verity_slice_tmp_8" 0 }
  have htmp7 : evalExpr oracle midnight.model.fields s11 (.localVar "_verity_slice_tmp_7") =
      some (credit * (max128 - loss)) := by
    change some (lookupValue s11.bindings "_verity_slice_tmp_7") = some (credit * (max128 - loss))
    simp only [s11, s10]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_same]
  have htmp5 : evalExpr oracle midnight.model.fields s11 (.localVar "_verity_slice_tmp_5") =
      some (max128 - lastLoss) := by
    change some (lookupValue s11.bindings "_verity_slice_tmp_5") = some (max128 - lastLoss)
    simp only [s11, s10, s9, s8, s7]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_same]
  have hden_pos : max128 - lastLoss ≠ 0 := Nat.sub_ne_zero_of_lt hlast
  have hprod_lt : credit * (max128 - loss) < Uint256.modulus :=
    lt_of_le_of_lt (Nat.mul_le_mul hcredit_le hnum_le) (by decide)
  have hden_lt : max128 - lastLoss < Uint256.modulus :=
    lt_of_le_of_lt (Nat.sub_le _ _) max128_lt
  have step12 := exec_checked_div oracle midnight.model.fields s11
    "_verity_slice_tmp_8"
    (.localVar "_verity_slice_tmp_7") (.localVar "_verity_slice_tmp_5")
    (credit * (max128 - loss)) (max128 - lastLoss)
    htmp7 htmp5 hprod_lt hden_lt hden_pos
  set s12 : DenoteState :=
    { s11 with bindings := (bindValue s11.bindings "_verity_slice_tmp_8"
        (credit * (max128 - loss) / (max128 - lastLoss))) }
  have htmp8 : evalExpr oracle midnight.model.fields s12 (.localVar "_verity_slice_tmp_8") =
      some (credit * (max128 - loss) / (max128 - lastLoss)) := by
    change some (lookupValue s12.bindings "_verity_slice_tmp_8") =
      some (credit * (max128 - loss) / (max128 - lastLoss))
    simp only [s12, lookup_bind_same]
  have step13 := exec_assign_continue oracle midnight.model.fields s12
    "_verity_slice_tmp_9" _ _ htmp8
  set s13 : DenoteState :=
    { s12 with bindings := (bindValue s12.bindings "_verity_slice_tmp_9"
        (credit * (max128 - loss) / (max128 - lastLoss))) }
  refine ⟨s13, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [slashThenBranch]
    rw [exec_cons_continue (t := s1) (hhead := step1),
      exec_cons_continue (t := s2) (hhead := step2),
      exec_cons_continue (t := s3) (hhead := step3),
      exec_cons_continue (t := s4) (hhead := step4),
      exec_cons_continue (t := s5) (hhead := step5),
      exec_cons_continue (t := s6) (hhead := step6),
      exec_cons_continue (t := s7) (hhead := step7),
      exec_cons_continue (t := s8) (hhead := step8),
      exec_cons_continue (t := s9) (hhead := step9),
      exec_cons_continue (t := s10) (hhead := step10),
      exec_cons_continue (t := s11) (hhead := step11),
      exec_cons_continue (t := s12) (hhead := step12)]
    exact step13
  · change lookupValue s13.bindings "_verity_slice_tmp_9" = _
    simp only [s13, lookup_bind_same]
  · change lookupValue s13.bindings "_credit" = credit
    simp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), hs.credit_eq]
  · change lookupValue s13.bindings "_lastLossFactor" = lastLoss
    simp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), hs.lastLoss_eq]
  · change lookupValue s13.bindings "id" = id.val
    simp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
      lookup_bind_other _ _ _ _ (by decide), hs.id_eq]
  · simp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hworld]

/-- `preCredit` always continues with the slash formula. -/
theorem preCredit_exec
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (mat : Uint256) (id : BytesN 32) (user : Address) :
    ∃ s,
      execStmtList oracle midnight.model.fields (initState world mat id user) preCredit =
        .continue s ∧
      PostSlashState oracle world id user s := by
  set credit := (midnight.position.credit oracle world id user).val
  set lastLoss := (midnight.position.lastLossFactor oracle world id user).val
  set loss := (midnight.marketState.lossFactor oracle world id).val
  obtain ⟨sCL, hCL, hcredit, hlastLoss, hid, huser, hworld⟩ :=
    exec_credit_and_lastLoss oracle world mat id user
  have hsCL : CreditLastLoss oracle world id user sCL :=
    ⟨hcredit, hlastLoss, hid, hworld⟩
  have hlast_ev : evalExpr oracle midnight.model.fields sCL (Expr.localVar "_lastLossFactor") =
      some lastLoss := by
    simp only [evalExpr, lastLoss, hlastLoss]
  have hlt := eval_lt_of_vals oracle midnight.model.fields sCL
    (Expr.localVar "_lastLossFactor") (Expr.literal max128) lastLoss max128
    hlast_ev (eval_lit_max128 _ _ _)
  have step_tmp0 := exec_let_continue oracle midnight.model.fields sCL
    "_verity_slice_tmp_0" _ (boolWord (decide (lastLoss < max128))) hlt
  set s0 : DenoteState :=
    { sCL with bindings := (bindValue sCL.bindings "_verity_slice_tmp_0"
        (boolWord (decide (lastLoss < max128)))) }
  have step_tmp9 := exec_let_continue oracle midnight.model.fields s0
    "_verity_slice_tmp_9" (Expr.literal 0) 0 (eval_lit_zero _ _ _)
  set sTmp : DenoteState :=
    { s0 with bindings := bindValue s0.bindings "_verity_slice_tmp_9" 0 }
  have hsTmp : CreditLastLoss oracle world id user sTmp := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change lookupValue sTmp.bindings "_credit" = credit
      simp only [sTmp, s0]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide), hcredit]
    · change lookupValue sTmp.bindings "_lastLossFactor" = lastLoss
      simp only [sTmp, s0]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide), hlastLoss]
    · change lookupValue sTmp.bindings "id" = id.val
      simp only [sTmp, s0]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide), hid]
    · simp only [sTmp, s0, hworld]
  have hcond_ev : evalExpr oracle midnight.model.fields sTmp (Expr.localVar "_verity_slice_tmp_0") =
      some (boolWord (decide (lastLoss < max128))) := by
    change some (lookupValue sTmp.bindings "_verity_slice_tmp_0") =
      some (boolWord (decide (lastLoss < max128)))
    simp only [sTmp, s0]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_same]
  by_cases hltL : lastLoss < max128
  · have hbw : boolWord (decide (lastLoss < max128)) = 1 := boolWord_true_of hltL
    have hcond1 : evalExpr oracle midnight.model.fields sTmp
        (Expr.localVar "_verity_slice_tmp_0") = some 1 := by
      simpa [hbw] using hcond_ev
    obtain ⟨sThen, hThen, htmp9, hcred', hlast', hid', hworld'⟩ :=
      exec_slash_then oracle world id user sTmp hsTmp hltL
    have step_ite :
        execStmtList oracle midnight.model.fields sTmp
          [Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
            [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)]] =
          .continue sThen := by
      rw [exec_ite_one oracle midnight.model.fields sTmp _ _ _ hcond1, hThen]
    have hpsc_ev : evalExpr oracle midnight.model.fields sThen
        (Expr.localVar "_verity_slice_tmp_9") =
        some (credit * (max128 - loss) / (max128 - lastLoss)) := by
      simp only [evalExpr, credit, loss, lastLoss, htmp9]
    have step_psc := exec_let_continue oracle midnight.model.fields sThen
      "postSlashCredit" _ (credit * (max128 - loss) / (max128 - lastLoss)) hpsc_ev
    set sFinal : DenoteState :=
      { sThen with bindings := (bindValue sThen.bindings "postSlashCredit"
          (credit * (max128 - loss) / (max128 - lastLoss))) }
    refine ⟨sFinal, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [preCredit_parts]
      have hshape :
          [Stmt.letVar "_credit"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "credit"),
           Stmt.letVar "_lastLossFactor"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "lastLossFactor"),
           Stmt.letVar "_verity_slice_tmp_0"
              (Expr.lt (Expr.localVar "_lastLossFactor") (Expr.literal max128)),
           Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
           Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
             [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
           Stmt.letVar "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9")] =
          [Stmt.letVar "_credit"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "credit"),
           Stmt.letVar "_lastLossFactor"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "lastLossFactor")] ++
          [Stmt.letVar "_verity_slice_tmp_0"
              (Expr.lt (Expr.localVar "_lastLossFactor") (Expr.literal max128)),
           Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
           Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
             [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
           Stmt.letVar "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9")] := rfl
      rw [hshape, exec_append, hCL]
      change execStmtList oracle midnight.model.fields sCL
          [Stmt.letVar "_verity_slice_tmp_0"
              (Expr.lt (Expr.localVar "_lastLossFactor") (Expr.literal max128)),
           Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
           Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
             [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
           Stmt.letVar "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9")] =
          .continue sFinal
      rw [exec_cons_continue (t := s0) (hhead := step_tmp0),
        exec_cons_continue (t := sTmp) (hhead := step_tmp9),
        exec_cons_continue (t := sThen) (hhead := step_ite)]
      exact step_psc
    · change lookupValue sFinal.bindings "_credit" = credit
      simp only [sFinal]
      rw [lookup_bind_other _ _ _ _ (by decide), hcred']
    · change lookupValue sFinal.bindings "_lastLossFactor" = lastLoss
      simp only [sFinal]
      rw [lookup_bind_other _ _ _ _ (by decide), hlast']
    · change lookupValue sFinal.bindings "postSlashCredit" =
        slashFormula credit lastLoss loss
      simp only [sFinal, slashFormula, hltL, ↓reduceIte, lookup_bind_same]
    · simp only [sFinal, hworld']
  · have hbw : boolWord (decide (lastLoss < max128)) = 0 := boolWord_false_of_not hltL
    have step_ite :
        execStmtList oracle midnight.model.fields sTmp
          [Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
            [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)]] =
          .continue { sTmp with bindings := bindValue sTmp.bindings "_verity_slice_tmp_9" 0 } := by
      have h0 : boolWord (decide (lastLoss < max128)) = 0 := hbw
      rw [exec_ite_false oracle midnight.model.fields sTmp _ _ _ _ hcond_ev h0]
      exact exec_assign_continue oracle midnight.model.fields sTmp
        "_verity_slice_tmp_9" (Expr.literal 0) 0 (eval_lit_zero _ _ _)
    set sElse : DenoteState :=
      { sTmp with bindings := bindValue sTmp.bindings "_verity_slice_tmp_9" 0 }
    have hpsc_ev : evalExpr oracle midnight.model.fields sElse
        (Expr.localVar "_verity_slice_tmp_9") = some 0 := by
      change some (lookupValue sElse.bindings "_verity_slice_tmp_9") = some 0
      simp only [sElse, lookup_bind_same]
    have step_psc := exec_let_continue oracle midnight.model.fields sElse
      "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9") 0 hpsc_ev
    set sFinal : DenoteState :=
      { sElse with bindings := bindValue sElse.bindings "postSlashCredit" 0 }
    refine ⟨sFinal, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [preCredit_parts]
      have hshape :
          [Stmt.letVar "_credit"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "credit"),
           Stmt.letVar "_lastLossFactor"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "lastLossFactor"),
           Stmt.letVar "_verity_slice_tmp_0"
              (Expr.lt (Expr.localVar "_lastLossFactor") (Expr.literal max128)),
           Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
           Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
             [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
           Stmt.letVar "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9")] =
          [Stmt.letVar "_credit"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "credit"),
           Stmt.letVar "_lastLossFactor"
              (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "lastLossFactor")] ++
          [Stmt.letVar "_verity_slice_tmp_0"
              (Expr.lt (Expr.localVar "_lastLossFactor") (Expr.literal max128)),
           Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
           Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
             [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
           Stmt.letVar "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9")] := rfl
      rw [hshape, exec_append, hCL]
      change execStmtList oracle midnight.model.fields sCL
          [Stmt.letVar "_verity_slice_tmp_0"
              (Expr.lt (Expr.localVar "_lastLossFactor") (Expr.literal max128)),
           Stmt.letVar "_verity_slice_tmp_9" (Expr.literal 0),
           Stmt.ite (Expr.localVar "_verity_slice_tmp_0") slashThenBranch
             [Stmt.assignVar "_verity_slice_tmp_9" (Expr.literal 0)],
           Stmt.letVar "postSlashCredit" (Expr.localVar "_verity_slice_tmp_9")] =
          .continue sFinal
      rw [exec_cons_continue (t := s0) (hhead := step_tmp0),
        exec_cons_continue (t := sTmp) (hhead := step_tmp9),
        exec_cons_continue (t := sElse) (hhead := step_ite)]
      exact step_psc
    · change lookupValue sFinal.bindings "_credit" = credit
      simp only [sFinal, sElse, sTmp, s0]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide), hcredit]
    · change lookupValue sFinal.bindings "_lastLossFactor" = lastLoss
      simp only [sFinal, sElse, sTmp, s0]
      rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
        lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide), hlastLoss]
    · change lookupValue sFinal.bindings "postSlashCredit" =
        slashFormula credit lastLoss loss
      simp only [sFinal, slashFormula, hltL, ↓reduceIte, lookup_bind_same]
    · simp only [sFinal, sElse, sTmp, s0, hworld]

/-- A successful `preCredit` continue yields `PostSlashState`. -/
theorem preCredit_continue_postSlash
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (mat : Uint256) (id : BytesN 32) (user : Address) (s : DenoteState)
    (h : execStmtList oracle midnight.model.fields (initState world mat id user) preCredit =
      .continue s) :
    PostSlashState oracle world id user s := by
  obtain ⟨s', h', hs'⟩ := preCredit_exec oracle world mat id user
  rw [h'] at h
  exact (StmtOutcome.continue.inj h) ▸ hs'

/-- The then-branch of midPending's `credit > 0` ternary. -/
def pendingThenBranch : List Stmt :=
  match midPending with
  | [_, _, _, .ite _ yes _, _] => yes
  | _ => []

/-- All but the last two statements of `pendingThenBranch`. -/
def pendingThenPre : List Stmt := List.dropLast (List.dropLast pendingThenBranch)

theorem midPending_parts :
    midPending =
      [.letVar "_pendingFee"
          (.structMember2 "position" (.param "id") (.param "user") "pendingFee"),
       .letVar "_verity_slice_tmp_10" (.gt (.localVar "_credit") (.literal 0)),
       .letVar "_verity_slice_tmp_22" (.literal 0),
       .ite (.localVar "_verity_slice_tmp_10") pendingThenBranch
         [.assignVar "_verity_slice_tmp_22" (.literal 0)],
       .letVar "postSlashPendingFee" (.localVar "_verity_slice_tmp_22")] := by
  simp only [pendingThenBranch, midPending_concrete]

theorem pendingThen_eq_pre_suf :
    pendingThenBranch = pendingThenPre ++
      [.ite (.lt (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20"))
        [.panic .arithmeticOverflow]
        [.assignVar "_verity_slice_tmp_21"
          (.sub (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20"))],
       .assignVar "_verity_slice_tmp_22" (.localVar "_verity_slice_tmp_21")] := by
  unfold pendingThenPre pendingThenBranch
  simp only [midPending_concrete]
  rfl

theorem pendingThenPre_keeps_pendingFee :
    prefixList ["_pendingFee"] pendingThenPre = true := by
  unfold pendingThenPre pendingThenBranch
  simp only [midPending_concrete]
  decide

/-- Successful continue of the pending then-branch leaves `tmp22 ≤ pendingFee`. -/
theorem pendingThen_tmp22_le
    (oracle : DenoteOracle) (fs : List Field) (s t : DenoteState) (pending : Nat)
    (hpend : lookupValue s.bindings "_pendingFee" = pending)
    (hpend_le : pending ≤ max128)
    (h : execStmtList oracle fs s pendingThenBranch = .continue t) :
    lookupValue t.bindings "_verity_slice_tmp_22" ≤ pending := by
  rw [pendingThen_eq_pre_suf] at h
  obtain ⟨sPre, hPre, hSuf⟩ :=
    split_prefix_continue oracle fs s t pendingThenPre
      [.ite (.lt (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20"))
        [.panic .arithmeticOverflow]
        [.assignVar "_verity_slice_tmp_21"
          (.sub (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20"))],
       .assignVar "_verity_slice_tmp_22" (.localVar "_verity_slice_tmp_21")] h
  have hf := list_frame oracle fs s pendingThenPre ["_pendingFee"]
    pendingThenPre_keeps_pendingFee
  simp only [Frame, hPre] at hf
  have hpendPre : lookupValue sPre.bindings "_pendingFee" = pending := by
    rw [hf.2 "_pendingFee" (by simp), hpend]
  set sufChecked : List Stmt :=
    [Stmt.ite (Expr.lt (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20"))
      [Stmt.panic PanicCode.arithmeticOverflow]
      [Stmt.assignVar "_verity_slice_tmp_21"
        (Expr.sub (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20"))]]
  set sufAssign : List Stmt :=
    [Stmt.assignVar "_verity_slice_tmp_22" (Expr.localVar "_verity_slice_tmp_21")]
  have hsuf_eq :
      [Stmt.ite (Expr.lt (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20"))
        [Stmt.panic PanicCode.arithmeticOverflow]
        [Stmt.assignVar "_verity_slice_tmp_21"
          (Expr.sub (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20"))],
       Stmt.assignVar "_verity_slice_tmp_22" (Expr.localVar "_verity_slice_tmp_21")] =
      sufChecked ++ sufAssign := by
    simp only [sufChecked, sufAssign]
    rfl
  rw [hsuf_eq] at hSuf
  obtain ⟨sSub, hSub, hAsgn⟩ :=
    split_prefix_continue oracle fs sPre t sufChecked sufAssign hSuf
  have hpendE : evalExpr oracle fs sPre (Expr.localVar "_pendingFee") = some pending := by
    simp only [evalExpr, hpendPre]
  cases htmp20 : evalExpr oracle fs sPre (Expr.localVar "_verity_slice_tmp_20") with
  | none =>
    have hlt_none :
        evalExpr oracle fs sPre
          (Expr.lt (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20")) =
          none := by
      change (Option.bind (evalExpr oracle fs sPre (Expr.localVar "_pendingFee"))
          fun lhs => Option.bind (evalExpr oracle fs sPre (Expr.localVar "_verity_slice_tmp_20"))
            fun rhs => some (boolWord (decide (lhs < rhs)))) = none
      rw [hpendE, htmp20]
      rfl
    simp only [sufChecked] at hSub
    rw [exec_singleton, execStmt, hlt_none] at hSub
    cases hSub
  | some x =>
    have hlt := eval_lt_of_vals oracle fs sPre
      (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20") pending x hpendE
      htmp20
    by_cases hltPx : pending < x
    · have hbw : boolWord (decide (pending < x)) = 1 := boolWord_true_of hltPx
      have hcond1 : evalExpr oracle fs sPre
          (Expr.lt (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20")) =
          some 1 := by
        simpa [hlt, hbw]
      simp only [sufChecked] at hSub
      rw [exec_ite_one oracle fs sPre _ _ _ hcond1] at hSub
      simp only [exec_singleton, execStmt] at hSub
      cases hSub
    · have hle : x ≤ pending := Nat.not_lt.mp hltPx
      have hbw : boolWord (decide (pending < x)) = 0 := boolWord_false_of_not hltPx
      have hcond0 : evalExpr oracle fs sPre
          (Expr.lt (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20")) =
          some 0 := by
        simpa [hlt, hbw]
      have hpend_mod : pending < Uint256.modulus := lt_of_le_of_lt hpend_le max128_lt
      have hsub := eval_sub_of_vals oracle fs sPre
        (Expr.localVar "_pendingFee") (Expr.localVar "_verity_slice_tmp_20")
        pending x hpendE htmp20 hpend_mod hle
      have step_sub :
          execStmtList oracle fs sPre sufChecked =
            .continue { sPre with bindings :=
              (bindValue sPre.bindings "_verity_slice_tmp_21" (pending - x)) } := by
        simp only [sufChecked]
        rw [exec_ite_false oracle fs sPre _ _ _ _ hcond0 rfl]
        exact exec_assign_continue oracle fs sPre "_verity_slice_tmp_21" _ _ hsub
      rw [step_sub] at hSub
      cases hSub
      set sSub' : DenoteState :=
        { sPre with bindings := (bindValue sPre.bindings "_verity_slice_tmp_21" (pending - x)) }
      have htmp21 : evalExpr oracle fs sSub' (Expr.localVar "_verity_slice_tmp_21") =
          some (pending - x) := by
        simp only [evalExpr, sSub', lookup_bind_same]
      have step_asgn := exec_assign_continue oracle fs sSub'
        "_verity_slice_tmp_22" _ (pending - x) htmp21
      simp only [sufAssign] at hAsgn
      rw [step_asgn] at hAsgn
      cases hAsgn
      change lookupValue
        { sSub' with bindings :=
            (bindValue sSub'.bindings "_verity_slice_tmp_22" (pending - x)) }.bindings
        "_verity_slice_tmp_22" ≤ pending
      rw [lookup_bind_same]
      exact Nat.sub_le pending x

/-- After a successful `midPending` continue: pending is not increased; zero if credit is 0. -/
theorem midPending_continue_le
    (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address) (s0 s : DenoteState)
    (hps : PostSlashState oracle world id user s0)
    (hid : lookupValue s0.bindings "id" = id.val)
    (huser : lookupValue s0.bindings "user" = user.val)
    (h : execStmtList oracle midnight.model.fields s0 midPending = .continue s) :
    lookupValue s.bindings "postSlashPendingFee" ≤
      (midnight.position.pendingFee oracle world id user).val ∧
    ((midnight.position.credit oracle world id user).val = 0 →
      lookupValue s.bindings "postSlashPendingFee" = 0) := by
  set credit := (midnight.position.credit oracle world id user).val
  set pending := (midnight.position.pendingFee oracle world id user).val
  have hpend_le := pendingFee_val_le_max oracle world id user
  have hpend_ev := evalExpr_structMember2_param oracle midnight.model s0
    "position" "id" "user" "pendingFee" position_pendingFee_ready
  simp only [hid, huser, pendingFee_read_eq, hps.world_eq] at hpend_ev
  have step_pend := exec_let_continue oracle midnight.model.fields s0
    "_pendingFee" _ pending hpend_ev
  set s1 : DenoteState :=
    { s0 with bindings := bindValue s0.bindings "_pendingFee" pending }
  have hcred1 : lookupValue s1.bindings "_credit" = credit := by
    simp only [s1]
    rw [lookup_bind_other _ _ _ _ (by decide), hps.credit_eq]
  have hgt := eval_gt_of_vals oracle midnight.model.fields s1
    (.localVar "_credit") (.literal 0) credit 0
    (by simp only [evalExpr, hcred1]) (eval_lit_zero _ _ _)
  have step_t10 := exec_let_continue oracle midnight.model.fields s1
    "_verity_slice_tmp_10" _ (boolWord (decide (0 < credit))) hgt
  set s2 : DenoteState :=
    { s1 with bindings := (bindValue s1.bindings "_verity_slice_tmp_10"
        (boolWord (decide (0 < credit)))) }
  have step_t22 := exec_let_continue oracle midnight.model.fields s2
    "_verity_slice_tmp_22" (.literal 0) 0 (eval_lit_zero _ _ _)
  set s3 : DenoteState :=
    { s2 with bindings := bindValue s2.bindings "_verity_slice_tmp_22" 0 }
  have hcond_ev : evalExpr oracle midnight.model.fields s3 (.localVar "_verity_slice_tmp_10") =
      some (boolWord (decide (0 < credit))) := by
    change some (lookupValue s3.bindings "_verity_slice_tmp_10") = _
    simp only [s3, s2]
    rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_same]
  rw [midPending_parts] at h
  have hflat :
      [Stmt.letVar "_pendingFee"
          (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "pendingFee"),
       Stmt.letVar "_verity_slice_tmp_10" (Expr.gt (Expr.localVar "_credit") (Expr.literal 0)),
       Stmt.letVar "_verity_slice_tmp_22" (Expr.literal 0),
       Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
         [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)],
       Stmt.letVar "postSlashPendingFee" (Expr.localVar "_verity_slice_tmp_22")] =
      [Stmt.letVar "_pendingFee"
          (Expr.structMember2 "position" (Expr.param "id") (Expr.param "user") "pendingFee")] ++
      [Stmt.letVar "_verity_slice_tmp_10" (Expr.gt (Expr.localVar "_credit") (Expr.literal 0)),
       Stmt.letVar "_verity_slice_tmp_22" (Expr.literal 0),
       Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
         [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)],
       Stmt.letVar "postSlashPendingFee" (Expr.localVar "_verity_slice_tmp_22")] := rfl
  rw [hflat, exec_append, step_pend] at h
  change execStmtList oracle midnight.model.fields s1
      [Stmt.letVar "_verity_slice_tmp_10" (Expr.gt (Expr.localVar "_credit") (Expr.literal 0)),
       Stmt.letVar "_verity_slice_tmp_22" (Expr.literal 0),
       Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
         [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)],
       Stmt.letVar "postSlashPendingFee" (Expr.localVar "_verity_slice_tmp_22")] =
      .continue s at h
  rw [exec_cons_continue (t := s2) (hhead := step_t10),
    exec_cons_continue (t := s3) (hhead := step_t22)] at h
  by_cases hc0 : credit = 0
  · have hbw : boolWord (decide (0 < credit)) = 0 := by simp [boolWord, hc0]
    have hcond0 : evalExpr oracle midnight.model.fields s3
        (Expr.localVar "_verity_slice_tmp_10") = some 0 := by
      simpa [hbw] using hcond_ev
    have step_ite :
        execStmtList oracle midnight.model.fields s3
          [Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
            [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)]] =
          .continue { s3 with bindings := bindValue s3.bindings "_verity_slice_tmp_22" 0 } := by
      rw [exec_ite_false oracle midnight.model.fields s3 _ _ _ _ hcond0 rfl]
      exact exec_assign_continue oracle midnight.model.fields s3
        "_verity_slice_tmp_22" (Expr.literal 0) 0 (eval_lit_zero _ _ _)
    set s4 : DenoteState :=
      { s3 with bindings := bindValue s3.bindings "_verity_slice_tmp_22" 0 }
    have htmp : evalExpr oracle midnight.model.fields s4 (.localVar "_verity_slice_tmp_22") =
        some 0 := by
      change some (lookupValue s4.bindings "_verity_slice_tmp_22") = some 0
      simp only [s4, lookup_bind_same]
    have step_final := exec_let_continue oracle midnight.model.fields s4
      "postSlashPendingFee" _ 0 htmp
    set sFinal : DenoteState :=
      { s4 with bindings := bindValue s4.bindings "postSlashPendingFee" 0 }
    have hexec :
        execStmtList oracle midnight.model.fields s3
          [Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
            [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)],
           Stmt.letVar "postSlashPendingFee" (Expr.localVar "_verity_slice_tmp_22")] =
          .continue sFinal := by
      rw [exec_cons_continue (t := s4) (hhead := step_ite)]
      exact step_final
    rw [hexec] at h
    have hsEq : s = sFinal := StmtOutcome.continue.inj h.symm
    subst hsEq
    refine ⟨Nat.zero_le _, fun _ => ?_⟩
    change lookupValue sFinal.bindings "postSlashPendingFee" = 0
    simp only [sFinal, lookup_bind_same]
  · have hpos : 0 < credit := Nat.pos_of_ne_zero hc0
    have hbw : boolWord (decide (0 < credit)) = 1 := boolWord_true_of hpos
    have hcond1 : evalExpr oracle midnight.model.fields s3
        (Expr.localVar "_verity_slice_tmp_10") = some 1 := by
      simpa [hbw] using hcond_ev
    have hlist :
        [Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
          [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)],
         Stmt.letVar "postSlashPendingFee" (Expr.localVar "_verity_slice_tmp_22")] =
        [Stmt.ite (Expr.localVar "_verity_slice_tmp_10") pendingThenBranch
          [Stmt.assignVar "_verity_slice_tmp_22" (Expr.literal 0)]] ++
        [Stmt.letVar "postSlashPendingFee" (Expr.localVar "_verity_slice_tmp_22")] := rfl
    rw [hlist, exec_append,
      exec_ite_one oracle midnight.model.fields s3 _ _ _ hcond1] at h
    match hy : execStmtList oracle midnight.model.fields s3 pendingThenBranch with
    | .revert => simp only [hy] at h; cases h
    | .stop _ => simp only [hy] at h; cases h
    | .return _ _ => simp only [hy] at h; cases h
    | .continue sYes =>
      simp only [hy] at h
      have hpend3 : lookupValue s3.bindings "_pendingFee" = pending := by
        simp only [s3, s2, s1]
        rw [lookup_bind_other _ _ _ _ (by decide), lookup_bind_other _ _ _ _ (by decide),
          lookup_bind_same]
      have hle := pendingThen_tmp22_le oracle midnight.model.fields s3 sYes pending
        hpend3 hpend_le hy
      match hv : evalExpr oracle midnight.model.fields sYes
          (Expr.localVar "_verity_slice_tmp_22") with
      | none =>
        simp only [exec_singleton, execStmt, hv] at h
        cases h
      | some v =>
        have hv'' : v = lookupValue sYes.bindings "_verity_slice_tmp_22" := by
          simpa [evalExpr] using Option.some.inj hv.symm
        have hstep := exec_let_continue oracle midnight.model.fields sYes
          "postSlashPendingFee" _ v hv
        rw [hstep] at h
        have hsEq : s = { sYes with bindings :=
            (bindValue sYes.bindings "postSlashPendingFee" v) } :=
          StmtOutcome.continue.inj h.symm
        subst hsEq
        refine ⟨?_, fun h' => (hc0 h').elim⟩
        change lookupValue
          { sYes with bindings := (bindValue sYes.bindings "postSlashPendingFee" v) }.bindings
          "postSlashPendingFee" ≤ pending
        rw [lookup_bind_same, hv'']
        exact hle


end Midnight.Lemmas
