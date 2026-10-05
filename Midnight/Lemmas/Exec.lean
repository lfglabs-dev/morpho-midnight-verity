import Midnight.Lemmas.Arith

/-!
Stepping lemmas for the checked arithmetic the Solidity importer emits.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas

namespace Midnight.Lemmas

theorem exec_cons_continue {o : DenoteOracle} {fs s stmt rest s' out}
    (h1 : execStmt o fs s stmt = .continue s')
    (h2 : execStmtList o fs s' rest = out) :
    execStmtList o fs s (stmt :: rest) = out := by
  simp [execStmtList, h1, h2]

theorem exec_append_continue {o : DenoteOracle} {fs s a b t out}
    (h1 : execStmtList o fs s a = .continue t)
    (h2 : execStmtList o fs t b = out) :
    execStmtList o fs s (a ++ b) = out := by
  rw [exec_append, h1]
  exact h2

theorem wordNormalize_zero : wordNormalize 0 = 0 :=
  wordNormalize_of_lt Uint256.modulus_pos

theorem bind_shadow (env : Env) (name : String) (v w : Nat) :
    bindValue (bindValue env name v) name w = bindValue env name w := by
  simp only [bindValue]
  have hnn : (name != name) = false := by simp
  simp only [List.filter_cons, hnn, Bool.false_eq_true, ite_false, List.filter_filter]
  congr 1
  refine List.filter_congr fun x _ => ?_
  simp

theorem let_literal {o : DenoteOracle} {fs s name rest out n}
    (hn : wordNormalize n = n)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings name n} rest = out) :
    execStmtList o fs s (.letVar name (.literal n) :: rest) = out := by
  rw [exec_let_cons, evalExpr_literal_arm, hn]
  exact hrest

theorem let_local {o : DenoteOracle} {fs s name src rest out v}
    (hv : lookupValue s.bindings src = v)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings name v} rest = out) :
    execStmtList o fs s (.letVar name (.localVar src) :: rest) = out := by
  rw [exec_let_cons, evalExpr_localVar_arm, hv]
  exact hrest

theorem assign_local {o : DenoteOracle} {fs s name src rest out v}
    (hv : lookupValue s.bindings src = v)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings name v} rest = out) :
    execStmtList o fs s (.assignVar name (.localVar src) :: rest) = out := by
  rw [execStmtList, execStmt_assignVar_arm, evalExpr_localVar_arm, hv]
  exact hrest

theorem assign_literal {o : DenoteOracle} {fs s name rest out n}
    (hn : wordNormalize n = n)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings name n} rest = out) :
    execStmtList o fs s (.assignVar name (.literal n) :: rest) = out := by
  rw [execStmtList, execStmt_assignVar_arm, evalExpr_literal_arm, hn]
  exact hrest

private theorem sub_val {av bv : Nat} (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus)
    (hle : bv ≤ av) :
    ((Uint256.ofNat av - Uint256.ofNat bv : Uint256) : Nat) = av - bv := by
  rw [Uint256.sub_eq_of_le]
  · simp [Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv]
  · simpa [Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hle

private theorem eval_sub_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hle : bv ≤ av) :
    evalExpr o fs s (.sub a b) = some (av - bv) := by
  rw [evalExpr_sub_arm, ha, hb]
  simp [sub_val hav hbv hle]

private theorem eval_lt_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv) :
    evalExpr o fs s (.lt a b) = some (boolWord (decide (av < bv))) := by
  rw [evalExpr_lt_arm, ha, hb]
  simp [Option.bind_some]

theorem if_false_eq {α : Type} (a b : α) : (if false = true then a else b) = b := rfl

/-- A checked subtraction that is known not to underflow. -/
theorem go_checked_sub {o : DenoteOracle} {fs s dest rest out av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hle : bv ≤ av)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings dest (av - bv)} rest = out) :
    execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.lt a b) [.panic .arithmeticOverflow] [.assignVar dest (.sub a b)] :: rest) = out := by
  let s0 := {s with bindings := bindValue s.bindings dest 0}
  have hstep : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.lt a b) [.panic .arithmeticOverflow] [.assignVar dest (.sub a b)] :: rest) =
      execStmtList o fs s0
        (.ite (.lt a b) [.panic .arithmeticOverflow] [.assignVar dest (.sub a b)] :: rest) := by
    rw [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero]
  rw [hstep, execStmtList.eq_2, execStmt_ite_arm, eval_lt_val ha hb]
  have hdec : decide (av < bv) = false := decide_false_of_not (Nat.not_lt.mpr hle)
  simp only [hdec, boolWord_false]
  have hif : ((0 : Nat) != 0) = false := by decide
  simp only [hif, if_false_eq, exec_singleton, execStmt_assignVar_arm, s0,
    eval_sub_val ha hb hav hbv hle, bind_shadow]
  exact hrest

/-- A successful checked subtraction did not underflow. -/
theorem ex_checked_sub {o : DenoteOracle} {fs s dest rest final av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus)
    (h : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.lt a b) [.panic .arithmeticOverflow] [.assignVar dest (.sub a b)] :: rest) =
        .stop final) :
    bv ≤ av ∧
      execStmtList o fs {s with bindings := bindValue s.bindings dest (av - bv)} rest = .stop final := by
  simp only [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero] at h
  rw [execStmtList.eq_2, execStmt_ite_arm, eval_lt_val ha hb] at h
  by_cases hlt : av < bv
  · have hdec : decide (av < bv) = true := decide_true_of hlt
    simp only [hdec, boolWord_true] at h
    have hif : ((1 : Nat) != 0) = true := by decide
    simp only [hif, ite_true, exec_singleton, execStmt_panic_arm] at h
    cases h
  · have hle : bv ≤ av := Nat.le_of_not_lt hlt
    have hdec : decide (av < bv) = false := decide_false_of_not hlt
    simp only [hdec, boolWord_false] at h
    have hif : ((0 : Nat) != 0) = false := by decide
    simp only [hif, if_false_eq, exec_singleton, execStmt_assignVar_arm,
      eval_sub_val ha hb hav hbv hle, bind_shadow] at h
    exact ⟨hle, h⟩

private theorem eval_mul_mod {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) :
    evalExpr o fs s (.mul a b) = some ((av * bv) % Uint256.modulus) := by
  rw [evalExpr_mul_arm, ha, hb]
  simp [HMul.hMul, Uint256.mul, Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv]

/-- Same extraction when the surrounding execution continues rather than stops. -/
theorem ex_checked_sub_cont {o : DenoteOracle} {fs s dest rest t av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus)
    (h : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.lt a b) [.panic .arithmeticOverflow] [.assignVar dest (.sub a b)] :: rest) =
        .continue t) :
    bv ≤ av ∧
      execStmtList o fs {s with bindings := bindValue s.bindings dest (av - bv)} rest =
        .continue t := by
  simp only [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero] at h
  rw [execStmtList.eq_2, execStmt_ite_arm, eval_lt_val ha hb] at h
  by_cases hlt : av < bv
  · have hdec : decide (av < bv) = true := decide_true_of hlt
    simp only [hdec, boolWord_true] at h
    have hif : ((1 : Nat) != 0) = true := by decide
    simp only [hif, ite_true, exec_singleton, execStmt_panic_arm] at h
    cases h
  · have hle : bv ≤ av := Nat.le_of_not_lt hlt
    have hdec : decide (av < bv) = false := decide_false_of_not hlt
    simp only [hdec, boolWord_false] at h
    have hif : ((0 : Nat) != 0) = false := by decide
    simp only [hif, if_false_eq, exec_singleton, execStmt_assignVar_arm,
      eval_sub_val ha hb hav hbv hle, bind_shadow] at h
    exact ⟨hle, h⟩

theorem eval_lit {o : DenoteOracle} {fs s n} (hn : wordNormalize n = n) :
    evalExpr o fs s (.literal n) = some n := by
  rw [evalExpr_literal_arm, hn]

theorem eval_lit_zero {o : DenoteOracle} {fs s} : evalExpr o fs s (.literal 0) = some 0 :=
  eval_lit wordNormalize_zero

private theorem mul_nat {av bv : Nat} (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus)
    (hlt : av * bv < Uint256.modulus) :
    ((Uint256.ofNat av * Uint256.ofNat bv : Uint256) : Nat) = av * bv := by
  rw [Uint256.mul_eq_of_lt]
  · simp [Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv]
  · simpa [Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hlt

private theorem add_nat {av bv : Nat} (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus)
    (hlt : av + bv < Uint256.modulus) :
    ((Uint256.ofNat av + Uint256.ofNat bv : Uint256) : Nat) = av + bv := by
  rw [Uint256.add_eq_of_lt]
  · simp [Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv]
  · simpa [Uint256.ofNat, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hlt

private theorem eval_mul_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hlt : av * bv < Uint256.modulus) :
    evalExpr o fs s (.mul a b) = some (av * bv) := by
  rw [evalExpr_mul_arm, ha, hb]
  simp [mul_nat hav hbv hlt]

private theorem eval_add_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hlt : av + bv < Uint256.modulus) :
    evalExpr o fs s (.add a b) = some (av + bv) := by
  rw [evalExpr_add_arm, ha, hb]
  simp [add_nat hav hbv hlt]

private theorem eval_div_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) :
    evalExpr o fs s (.div a b) = some (av / bv) := by
  rw [evalExpr_div_arm, ha, hb]
  simp [div_word hav hbv]

private theorem eval_eq_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv) :
    evalExpr o fs s (.eq a b) = some (boolWord (decide (av = bv))) := by
  rw [evalExpr_eq_arm, ha, hb]
  simp

private theorem eval_gt_val {o : DenoteOracle} {fs s a b av bv}
    (ha : evalExpr o fs s a = some av) (hb : evalExpr o fs s b = some bv) :
    evalExpr o fs s (.gt a b) = some (boolWord (decide (bv < av))) := by
  rw [evalExpr_gt_arm, ha, hb]
  simp

/-- Checked division by a non-zero denominator. -/
theorem go_checked_div {o : DenoteOracle} {fs s dest rest out av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hpos : bv ≠ 0)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings dest (av / bv)} rest = out) :
    execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.eq b (.literal 0)) [.panic .divisionByZero] [.assignVar dest (.div a b)] :: rest) =
      out := by
  let s0 := {s with bindings := bindValue s.bindings dest 0}
  have hstep : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.eq b (.literal 0)) [.panic .divisionByZero] [.assignVar dest (.div a b)] :: rest) =
      execStmtList o fs s0
        (.ite (.eq b (.literal 0)) [.panic .divisionByZero] [.assignVar dest (.div a b)] :: rest) := by
    rw [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero]
  rw [hstep, execStmtList.eq_2, execStmt_ite_arm, eval_eq_val hb eval_lit_zero]
  have hdec : decide (bv = 0) = false := decide_false_of_not hpos
  simp only [hdec, boolWord_false]
  have hif : ((0 : Nat) != 0) = false := by decide
  simp only [hif, if_false_eq, exec_singleton, execStmt_assignVar_arm, s0,
    eval_div_val ha hb hav hbv, bind_shadow]
  exact hrest

/-- Checked addition that is known not to overflow. -/
theorem go_checked_add {o : DenoteOracle} {fs s dest rest out av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hlt : av + bv < Uint256.modulus)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings dest (av + bv)} rest = out) :
    execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.lt (.add a b) a) [.panic .arithmeticOverflow] [.assignVar dest (.add a b)] :: rest) =
      out := by
  let s0 := {s with bindings := bindValue s.bindings dest 0}
  have hstep : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.lt (.add a b) a) [.panic .arithmeticOverflow] [.assignVar dest (.add a b)] :: rest) =
      execStmtList o fs s0
        (.ite (.lt (.add a b) a) [.panic .arithmeticOverflow] [.assignVar dest (.add a b)] :: rest) := by
    rw [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero]
  have hadd : evalExpr o fs s0 (.add a b) = some (av + bv) := eval_add_val ha hb hav hbv hlt
  rw [hstep, execStmtList.eq_2, execStmt_ite_arm, eval_lt_val hadd ha]
  have hdec : decide (av + bv < av) = false := decide_false_of_not (by omega)
  simp only [hdec, boolWord_false]
  have hif : ((0 : Nat) != 0) = false := by decide
  simp only [hif, if_false_eq, exec_singleton, execStmt_assignVar_arm, s0, hadd, bind_shadow]
  exact hrest

/-- Checked `uint256` multiplication that is known not to overflow. -/
theorem go_checked_mul {o : DenoteOracle} {fs s dest rest out av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus) (hlt : av * bv < Uint256.modulus)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings dest (av * bv)} rest = out) :
    execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.eq a (.literal 0))
          [.assignVar dest (.mul a b)]
          [.ite (.eq (.div (.mul a b) a) b)
            [.assignVar dest (.mul a b)]
            [.panic .arithmeticOverflow]] ::
        rest) = out := by
  let s0 := {s with bindings := bindValue s.bindings dest 0}
  have hmul : evalExpr o fs s0 (.mul a b) = some (av * bv) := eval_mul_val ha hb hav hbv hlt
  have hstep : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.eq a (.literal 0))
          [.assignVar dest (.mul a b)]
          [.ite (.eq (.div (.mul a b) a) b)
            [.assignVar dest (.mul a b)]
            [.panic .arithmeticOverflow]] ::
        rest) =
      execStmtList o fs s0
        (.ite (.eq a (.literal 0))
          [.assignVar dest (.mul a b)]
          [.ite (.eq (.div (.mul a b) a) b)
            [.assignVar dest (.mul a b)]
            [.panic .arithmeticOverflow]] ::
        rest) := by
    rw [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero]
  rw [hstep, execStmtList.eq_2, execStmt_ite_arm, eval_eq_val ha eval_lit_zero]
  by_cases hzero : av = 0
  · have hdec : decide (av = 0) = true := decide_true_of hzero
    simp only [hdec, boolWord_true]
    have hif : ((1 : Nat) != 0) = true := by decide
    simp only [hif, ite_true, exec_singleton, execStmt_assignVar_arm, s0, hmul, bind_shadow]
    simpa [hzero] using hrest
  · have hdec : decide (av = 0) = false := decide_false_of_not hzero
    simp only [hdec, boolWord_false]
    have hif : ((0 : Nat) != 0) = false := by decide
    simp only [hif, if_false_eq, execStmtList.eq_2, execStmt_ite_arm]
    have hdiv : evalExpr o fs s0 (.div (.mul a b) a) = some bv := by
      have hquot : evalExpr o fs s0 (.div (.mul a b) a) = some (av * bv / av) :=
        eval_div_val hmul ha hlt hav
      have hcancel : av * bv / av = bv := by
        rw [Nat.mul_comm]
        exact Nat.mul_div_cancel bv (Nat.pos_of_ne_zero hzero)
      simpa [hcancel] using hquot
    -- The bound above is a mess; replace below if it fails.
    rw [eval_eq_val hdiv hb]
    have hok : decide (bv = bv) = true := decide_true_of rfl
    simp only [hok, boolWord_true]
    have hif1 : ((1 : Nat) != 0) = true := by decide
    simp only [hif1, ite_true, exec_singleton, execStmt_assignVar_arm, s0, hmul, bind_shadow]
    exact hrest

theorem go_ite_one {o : DenoteOracle} {fs s cond yes no rest out t}
    (hc : lookupValue s.bindings cond = 1)
    (hbr : execStmtList o fs s yes = .continue t)
    (hrest : execStmtList o fs t rest = out) :
    execStmtList o fs s (.ite (.localVar cond) yes no :: rest) = out := by
  rw [execStmtList.eq_2, execStmt_ite_arm, evalExpr_localVar_arm, hc]
  have hif : ((1 : Nat) != 0) = true := by decide
  simp only [hif, ite_true, hbr]
  exact hrest

theorem go_ite_zero {o : DenoteOracle} {fs s cond yes no rest out t}
    (hc : lookupValue s.bindings cond = 0)
    (hbr : execStmtList o fs s no = .continue t)
    (hrest : execStmtList o fs t rest = out) :
    execStmtList o fs s (.ite (.localVar cond) yes no :: rest) = out := by
  rw [execStmtList.eq_2, execStmt_ite_arm, evalExpr_localVar_arm, hc]
  have hif : ((0 : Nat) != 0) = false := by decide
  simp only [hif, if_false_eq, hbr]
  exact hrest

theorem let_mask128 {o : DenoteOracle} {fs s dest src rest out v}
    (hv : lookupValue s.bindings src = v) (hle : v ≤ max128)
    (hrest : execStmtList o fs {s with bindings := bindValue s.bindings dest v} rest = out) :
    execStmtList o fs s
      (.letVar dest (.bitAnd (.localVar src) (.literal max128)) :: rest) = out := by
  rw [exec_let_cons, evalExpr_bitAnd_arm, evalExpr_localVar_arm, eval_lit normalize_max, hv]
  simp [mask_of_le hle]
  exact hrest

theorem eval_yul_min {o : DenoteOracle} {fs s ts mat}
    (hts : s.world.blockTimestamp.val = ts)
    (hmat : lookupValue s.bindings "market_maturity" = mat)
    (htsM : ts < Uint256.modulus) (hmatM : mat < Uint256.modulus) :
    evalExpr o fs s
      (.bitXor .blockTimestamp
        (.mul (.bitXor .blockTimestamp (.param "market_maturity"))
          (.lt (.param "market_maturity") .blockTimestamp))) =
      some (if mat < ts then mat else ts) := by
  have htsE : evalExpr o fs s .blockTimestamp = some ts := by
    simpa [hts] using evalExpr_blockTimestamp_arm o fs s
  have hmatE : evalExpr o fs s (.param "market_maturity") = some mat := by
    simpa [hmat] using evalExpr_param_arm o fs s "market_maturity"
  have hxor : evalExpr o fs s (.bitXor .blockTimestamp (.param "market_maturity")) =
      some ((Uint256.xor (Uint256.ofNat ts) (Uint256.ofNat mat)).val) := by
    rw [evalExpr_bitXor_arm, htsE, hmatE]
    simp
  have hlt : evalExpr o fs s (.lt (.param "market_maturity") .blockTimestamp) =
      some (boolWord (decide (mat < ts))) := by
    rw [evalExpr_lt_arm, hmatE, htsE]
    simp
  have hmul : evalExpr o fs s
      (.mul (.bitXor .blockTimestamp (.param "market_maturity"))
        (.lt (.param "market_maturity") .blockTimestamp)) =
      some (((Uint256.xor (Uint256.ofNat ts) (Uint256.ofNat mat)) *
        Uint256.ofNat (boolWord (decide (mat < ts)))).val) := by
    rw [evalExpr_mul_arm, hxor, hlt]
    simp [ofNat_val]
  rw [evalExpr_bitXor_arm, htsE, hmul]
  simp only [bind, Option.bind, pure]
  rw [ofNat_val]
  exact congrArg some (yul_min htsM hmatM)

/-- A continuing checked multiplication did not overflow. -/
theorem ex_checked_mul_cont {o : DenoteOracle} {fs s dest rest t av bv} {a b : Expr}
    (ha : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} a = some av)
    (hb : evalExpr o fs {s with bindings := bindValue s.bindings dest 0} b = some bv)
    (hav : av < Uint256.modulus) (hbv : bv < Uint256.modulus)
    (h : execStmtList o fs s
      (.letVar dest (.literal 0) ::
        .ite (.eq a (.literal 0))
          [.assignVar dest (.mul a b)]
          [.ite (.eq (.div (.mul a b) a) b)
            [.assignVar dest (.mul a b)]
            [.panic .arithmeticOverflow]] ::
        rest) = .continue t) :
    av * bv < Uint256.modulus ∧
      execStmtList o fs {s with bindings := bindValue s.bindings dest (av * bv)} rest =
        .continue t := by
  let s0 := {s with bindings := bindValue s.bindings dest 0}
  simp only [exec_let_cons, evalExpr_literal_arm, wordNormalize_zero] at h
  rw [execStmtList.eq_2, execStmt_ite_arm, eval_eq_val ha eval_lit_zero] at h
  by_cases hzero : av = 0
  · have hdec : decide (av = 0) = true := decide_true_of hzero
    simp only [hdec, boolWord_true] at h
    have hif : ((1 : Nat) != 0) = true := by decide
    simp only [hif, ite_true, exec_singleton, execStmt_assignVar_arm, eval_mul_mod ha hb hav hbv,
      bind_shadow] at h
    have hlt0 : av * bv < Uint256.modulus := by simpa [hzero] using Uint256.modulus_pos
    have hmod0 : (av * bv) % Uint256.modulus = av * bv := Nat.mod_eq_of_lt hlt0
    exact ⟨hlt0, by simpa [hmod0] using h⟩
  · have hdec : decide (av = 0) = false := decide_false_of_not hzero
    simp only [hdec, boolWord_false] at h
    have hif : ((0 : Nat) != 0) = false := by decide
    have hmul := eval_mul_mod ha hb hav hbv
    have hdiv : evalExpr o fs s0 (.div (.mul a b) a) =
        some (((av * bv) % Uint256.modulus) / av) :=
      eval_div_val hmul ha (Nat.mod_lt _ Uint256.modulus_pos) hav
    have hcond := eval_eq_val hdiv hb
    simp only [s0] at hcond
    simp only [hif, if_false_eq, execStmtList.eq_2, execStmt_ite_arm] at h
    simp only [hcond] at h
    by_cases hok : ((av * bv) % Uint256.modulus) / av = bv
    · simp [hok] at h
      have hif1 : ((1 : Nat) != 0) = true := by decide
      simp only [hif1, ite_true, exec_singleton, execStmt_assignVar_arm, hmul, bind_shadow] at h
      have hlt : av * bv < Uint256.modulus := mul_check_lt hzero hok
      have hmod : (av * bv) % Uint256.modulus = av * bv := Nat.mod_eq_of_lt hlt
      simp [execStmtList.eq_1, hmod] at h
      exact ⟨hlt, h⟩
    · simp [hok] at h
      have hif0 : ((0 : Nat) != 0) = false := by decide
      simp only [hif0, if_false_eq, exec_singleton, execStmt_panic_arm] at h
      cases h


theorem stop_return3 {o : DenoteOracle} {fs s a b c va vb vc}
    (ha : lookupValue s.bindings a = va) (hb : lookupValue s.bindings b = vb)
    (hc : lookupValue s.bindings c = vc)
    (hva : va < Uint256.modulus) (hvb : vb < Uint256.modulus) (hvc : vc < Uint256.modulus) :
    execStmtList o fs s [.returnValues [.localVar a, .localVar b, .localVar c]] =
      .stop {s with observedReturnWords := some [va, vb, vc]} := by
  rw [execStmtList.eq_2, execStmt_returnValues_arm]
  simp [evalExprList, evalExpr_localVar_arm, ha, hb, hc, wordNormalize_of_lt hva,
    wordNormalize_of_lt hvb, wordNormalize_of_lt hvc]

end Midnight.Lemmas
