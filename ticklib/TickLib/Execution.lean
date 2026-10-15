import TickLib.Import
import TickLib.Signed
import Compiler.SolidityImport.Proofs

/-!
# What the imported code computes

`run_wExp` and `run_tickToPrice` show that running the imported bodies of
`wExp` and `tickToPrice` returns `wExpW x` and `tickW tick`: plain functions
built from the word operations of `Signed.lean`.

The bodies are restated below statement by statement, and `wExp_body` /
`tickToPrice_body` check by `rfl` that they are the imported ones. Each part is
executed by its own lemma:

| part           | Solidity                                          | lemma            |
| -------------- | ------------------------------------------------- | ---------------- |
| `wPos`         | the `x >= 0` branch of `wExp`                     | `exec_wPos`      |
| `wNeg`         | `1e36 / wExp(-x)`, with the inlined recursive call | `exec_wNeg_*`    |
| `wTail`        | `return`                                          | `exec_wTail`     |
| `tHead`        | `require(tick <= MAX_TICK)`, `LN * (3372 - tick)`  | `tickToPrice_start`, `tickToPrice_out` |
| `tPos`, `tNeg` | the inlined `wExp` call                           | `exec_tPos`, `exec_tNeg_*` |
| `tTail`        | the two `divHalfDownUnchecked` and `* 1e11`        | `exec_tTail`     |

The importer inlines the recursive call `wExp(-x)` with a guard that reverts if
`-x` is still negative (only `x = type(int256).min`). It is the
`.ite (.slt _verity_slice_tmp_1 0) [.revertReturndata] []` statement in `wNeg`.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote Compiler.CompilationModel.SolidityImport
open Verity.Core TickLib.Signed
namespace TickLib.Execution

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## Expression evaluation, one constructor at a time -/

section
variable (o : DenoteOracle) (fs : List Field) (s : DenoteState)
theorem ev_lit (n : Nat) : evalExpr o fs s (.literal n) = some (wordNormalize n) := by simp [evalExpr]
theorem ev_param (n : String) : evalExpr o fs s (.param n) = some (lookupValue s.bindings n) := by
  simp [evalExpr]
theorem ev_local (n : String) : evalExpr o fs s (.localVar n) = some (lookupValue s.bindings n) := by
  simp [evalExpr]
theorem ev_add (a b : Expr) : evalExpr o fs s (.add a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (addW x y) := by
  simp only [evalExpr]; rfl
theorem ev_sub (a b : Expr) : evalExpr o fs s (.sub a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (subW x y) := by
  simp only [evalExpr]; rfl
theorem ev_mul (a b : Expr) : evalExpr o fs s (.mul a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (mulW x y) := by
  simp only [evalExpr]; rfl
theorem ev_div (a b : Expr) : evalExpr o fs s (.div a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (divW x y) := by
  simp only [evalExpr]; rfl
theorem ev_sdiv (a b : Expr) : evalExpr o fs s (.sdiv a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (sdivW x y) := by
  simp only [evalExpr]; rfl
theorem ev_slt (a b : Expr) : evalExpr o fs s (.slt a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (boolWord (sltW x y)) := by
  simp only [evalExpr]; rfl
theorem ev_eq (a b : Expr) : evalExpr o fs s (.eq a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (boolWord (decide (x = y))) := by
  simp only [evalExpr]; rfl
theorem ev_le (a b : Expr) : evalExpr o fs s (.le a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (boolWord (decide (x ≤ y))) := by
  simp only [evalExpr]; rfl
theorem ev_shl (a b : Expr) : evalExpr o fs s (.shl a b) =
    (evalExpr o fs s a).bind fun x => (evalExpr o fs s b).bind fun y => some (shlW x y) := by
  simp only [evalExpr]; rfl
end

/-! ## Statements, one at a time -/

/-- How `runFunction` reads an outcome. -/
def result : StmtOutcome → Option (List Nat)
  | .stop state | .continue state | .return _ state => state.observedReturnWords
  | .revert | .revertWithData _ => none

theorem one_bne' : ((1 : Nat) != 0) = true := rfl

section
variable (o : DenoteOracle) (fs : List Field) (s : DenoteState) (rest : List Stmt)
theorem st_let (n : String) (e : Expr) : execStmtList o fs s (.letVar n e :: rest) =
    match evalExpr o fs s e with
    | some v => execStmtList o fs { s with bindings := bindValue s.bindings n v } rest
    | none => .revert := by
  simp only [execStmtList, execStmt]; cases evalExpr o fs s e <;> rfl
theorem st_assign (n : String) (e : Expr) : execStmtList o fs s (.assignVar n e :: rest) =
    match evalExpr o fs s e with
    | some v => execStmtList o fs { s with bindings := bindValue s.bindings n v } rest
    | none => .revert := by
  simp only [execStmtList, execStmt]; cases evalExpr o fs s e <;> rfl
theorem st_ite (c : Expr) (y n : List Stmt) : execStmtList o fs s (.ite c y n :: rest) =
    match evalExpr o fs s c with
    | some v => execStmtList o fs s ((if v != 0 then y else n) ++ rest)
    | none => .revert := by
  rw [execStmtList, execStmt]
  cases evalExpr o fs s c with
  | none => rfl
  | some v =>
    simp only [exec_append]
    by_cases h : (v != 0) = true
    · simp only [h, ↓reduceIte]; cases execStmtList o fs s y <;> rfl
    · simp only [h, ↓reduceIte, Bool.false_eq_true]; cases execStmtList o fs s n <;> rfl
theorem st_panic (c : PanicCode) : execStmtList o fs s (.panic c :: rest) =
    .revertWithData (panicBytes c.toNat) := rfl
theorem st_revertReturndata : execStmtList o fs s (.revertReturndata :: rest) =
    .revertWithData (s.world.returndata.flatMap wordBytes) := rfl
theorem st_ret (args : List Expr) : execStmtList o fs s (.returnValues args :: rest) =
    match evalExprList o fs s args with
    | some vs => .stop { s with observedReturnWords := some (vs.map wordNormalize), observedStop := false }
    | none => .revert := by
  simp only [execStmtList, execStmt]; cases evalExprList o fs s args <;> rfl
theorem st_require_ok (c : Expr) (name : String) (args : List Expr) (h : evalExpr o fs s c = some 1) :
    execStmtList o fs s (.requireError c name args :: rest) = execStmtList o fs s rest := by
  simp only [execStmtList, execStmt, h, one_bne', ↓reduceIte]
theorem st_require_fail (c : Expr) (name : String) (h : evalExpr o fs s c = some 0) :
    result (execStmtList o fs s (.requireError c name [] :: rest)) = none := by
  simp only [execStmtList, execStmt, h, evalExprList]
  cases customErrorBytes o s.errors name [] <;> rfl
theorem evl_one (e : Expr) : evalExprList o fs s [e] = (evalExpr o fs s e).map fun v => [v] := by
  simp only [evalExprList]; cases evalExpr o fs s e <;> rfl
end

theorem wn (n : Nat) : wordNormalize n = n % 2 ^ 256 := rfl
theorem one_bne : ((1 : Nat) != 0) = true := rfl
theorem zero_bne : ((0 : Nat) != 0) = false := rfl
theorem bw_ne (b : Bool) : ((if b = true then 1 else 0 : Nat) != 0) = b := by cases b <;> rfl
theorem bw_dec_ne (p : Prop) [Decidable p] : ((if decide p = true then 1 else 0 : Nat) != 0) = decide p :=
  bw_ne _

/-- Execute straight-line imported statements symbolically. -/
syntax "wsimp" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| wsimp [$args,*]) => `(tactic| simp only [st_let, st_assign, st_ite, st_panic,
      st_revertReturndata, st_ret, evl_one, ev_lit, ev_param, ev_local, ev_add, ev_sub, ev_mul, ev_div,
      ev_sdiv, ev_slt, ev_eq, ev_le, ev_shl, Option.bind_some, Option.map_some, Option.map_none,
      lookup_bind_same, ne_eq, String.reduceEq, not_false_eq_true, lookup_bind_other, wn,
      Nat.reducePow, Nat.reduceMod, boolWord, bw_ne, bw_dec_ne, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, decide_false, decide_true, Nat.reduceEqDiff, ↓reduceIte,
      Bool.false_eq_true, Bool.not_eq_true, one_bne, zero_bne, $args,*])

/-! ## The imported bodies -/

def wNeg : List Stmt := [
    .letVar "_verity_slice_tmp_1" (.sub (.literal 0) (.param "x")),
    .ite (.slt (.localVar "_verity_slice_tmp_1") (.literal 0)) [.revertReturndata] [],
    .letVar "ln2" (.literal 693147180559945309),
    .letVar "offset" (.literal 322611214989459870),
    .letVar "_verity_slice_tmp_2" (.add (.localVar "_verity_slice_tmp_1") (.localVar "offset")),
    .letVar "_verity_slice_tmp_3" (.literal 0),
    .ite (.eq (.localVar "ln2") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_3" (.sdiv (.localVar "_verity_slice_tmp_2") (.localVar "ln2"))],
    .letVar "q" (.localVar "_verity_slice_tmp_3"),
    .letVar "_verity_slice_tmp_4" (.mul (.localVar "q") (.localVar "ln2")),
    .letVar "r" (.sub (.localVar "_verity_slice_tmp_1") (.localVar "_verity_slice_tmp_4")),
    .letVar "_verity_slice_tmp_5" (.mul (.localVar "r") (.localVar "r")),
    .letVar "_verity_slice_tmp_6" (.literal 0),
    .ite (.eq (.literal 2000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_6" (.sdiv (.localVar "_verity_slice_tmp_5") (.literal 2000000000000000000))],
    .letVar "secondTerm" (.localVar "_verity_slice_tmp_6"),
    .letVar "_verity_slice_tmp_7" (.mul (.localVar "secondTerm") (.localVar "r")),
    .letVar "_verity_slice_tmp_8" (.literal 0),
    .ite (.eq (.literal 3000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_8" (.sdiv (.localVar "_verity_slice_tmp_7") (.literal 3000000000000000000))],
    .letVar "thirdTerm" (.localVar "_verity_slice_tmp_8"),
    .letVar "_verity_slice_tmp_9" (.add (.literal 1000000000000000000) (.localVar "r")),
    .letVar "_verity_slice_tmp_10" (.add (.localVar "_verity_slice_tmp_9") (.localVar "secondTerm")),
    .letVar "expR" (.add (.localVar "_verity_slice_tmp_10") (.localVar "thirdTerm")),
    .letVar "_verity_slice_tmp_11" (.shl (.localVar "q") (.localVar "expR")),
    .letVar "_verity_slice_tmp_12" (.literal 0),
    .ite (.eq (.localVar "_verity_slice_tmp_11") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_12" (.div (.literal 1000000000000000000000000000000000000) (.localVar "_verity_slice_tmp_11"))],
    .assignVar "_verity_slice_tmp_22" (.localVar "_verity_slice_tmp_12")]

def wPos : List Stmt := [
    .letVar "ln2_1" (.literal 693147180559945309),
    .letVar "offset_1" (.literal 322611214989459870),
    .letVar "_verity_slice_tmp_13" (.add (.param "x") (.localVar "offset_1")),
    .letVar "_verity_slice_tmp_14" (.literal 0),
    .ite (.eq (.localVar "ln2_1") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_14" (.sdiv (.localVar "_verity_slice_tmp_13") (.localVar "ln2_1"))],
    .letVar "q_1" (.localVar "_verity_slice_tmp_14"),
    .letVar "_verity_slice_tmp_15" (.mul (.localVar "q_1") (.localVar "ln2_1")),
    .letVar "r_1" (.sub (.param "x") (.localVar "_verity_slice_tmp_15")),
    .letVar "_verity_slice_tmp_16" (.mul (.localVar "r_1") (.localVar "r_1")),
    .letVar "_verity_slice_tmp_17" (.literal 0),
    .ite (.eq (.literal 2000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_17" (.sdiv (.localVar "_verity_slice_tmp_16") (.literal 2000000000000000000))],
    .letVar "secondTerm_1" (.localVar "_verity_slice_tmp_17"),
    .letVar "_verity_slice_tmp_18" (.mul (.localVar "secondTerm_1") (.localVar "r_1")),
    .letVar "_verity_slice_tmp_19" (.literal 0),
    .ite (.eq (.literal 3000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_19" (.sdiv (.localVar "_verity_slice_tmp_18") (.literal 3000000000000000000))],
    .letVar "thirdTerm_1" (.localVar "_verity_slice_tmp_19"),
    .letVar "_verity_slice_tmp_20" (.add (.literal 1000000000000000000) (.localVar "r_1")),
    .letVar "_verity_slice_tmp_21" (.add (.localVar "_verity_slice_tmp_20") (.localVar "secondTerm_1")),
    .letVar "expR_1" (.add (.localVar "_verity_slice_tmp_21") (.localVar "thirdTerm_1")),
    .assignVar "_verity_slice_tmp_22" (.shl (.localVar "q_1") (.localVar "expR_1"))]

def wTail : List Stmt := [
    .letVar "_verity_slice_tmp_23" (.localVar "_verity_slice_tmp_22"),
    .returnValues [.localVar "_verity_slice_tmp_23"]]

def tHead : List Stmt := [
    .letVar "_verity_slice_tmp_0" (.le (.param "tick") (.literal 6744)),
    .requireError (.localVar "_verity_slice_tmp_0") "TickOutOfRange" [],
    .letVar "_verity_slice_tmp_1" (.literal 0),
    .ite (.eq (.literal 2) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_1" (.div (.literal 6744) (.literal 2))],
    .letVar "_verity_slice_tmp_2" (.localVar "_verity_slice_tmp_1"),
    .letVar "_verity_slice_tmp_3" (.sub (.localVar "_verity_slice_tmp_2") (.param "tick")),
    .letVar "_verity_slice_tmp_4" (.mul (.literal 4987541511039073) (.localVar "_verity_slice_tmp_3")),
    .letVar "_verity_slice_tmp_5" (.slt (.localVar "_verity_slice_tmp_4") (.literal 0)),
    .letVar "_verity_slice_tmp_27" (.literal 0)]

def tNeg : List Stmt := [
    .letVar "_verity_slice_tmp_6" (.sub (.literal 0) (.localVar "_verity_slice_tmp_4")),
    .ite (.slt (.localVar "_verity_slice_tmp_6") (.literal 0)) [.revertReturndata] [],
    .letVar "ln2" (.literal 693147180559945309),
    .letVar "offset" (.literal 322611214989459870),
    .letVar "_verity_slice_tmp_7" (.add (.localVar "_verity_slice_tmp_6") (.localVar "offset")),
    .letVar "_verity_slice_tmp_8" (.literal 0),
    .ite (.eq (.localVar "ln2") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_8" (.sdiv (.localVar "_verity_slice_tmp_7") (.localVar "ln2"))],
    .letVar "q" (.localVar "_verity_slice_tmp_8"),
    .letVar "_verity_slice_tmp_9" (.mul (.localVar "q") (.localVar "ln2")),
    .letVar "r" (.sub (.localVar "_verity_slice_tmp_6") (.localVar "_verity_slice_tmp_9")),
    .letVar "_verity_slice_tmp_10" (.mul (.localVar "r") (.localVar "r")),
    .letVar "_verity_slice_tmp_11" (.literal 0),
    .ite (.eq (.literal 2000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_11" (.sdiv (.localVar "_verity_slice_tmp_10") (.literal 2000000000000000000))],
    .letVar "secondTerm" (.localVar "_verity_slice_tmp_11"),
    .letVar "_verity_slice_tmp_12" (.mul (.localVar "secondTerm") (.localVar "r")),
    .letVar "_verity_slice_tmp_13" (.literal 0),
    .ite (.eq (.literal 3000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_13" (.sdiv (.localVar "_verity_slice_tmp_12") (.literal 3000000000000000000))],
    .letVar "thirdTerm" (.localVar "_verity_slice_tmp_13"),
    .letVar "_verity_slice_tmp_14" (.add (.literal 1000000000000000000) (.localVar "r")),
    .letVar "_verity_slice_tmp_15" (.add (.localVar "_verity_slice_tmp_14") (.localVar "secondTerm")),
    .letVar "expR" (.add (.localVar "_verity_slice_tmp_15") (.localVar "thirdTerm")),
    .letVar "_verity_slice_tmp_16" (.shl (.localVar "q") (.localVar "expR")),
    .letVar "_verity_slice_tmp_17" (.literal 0),
    .ite (.eq (.localVar "_verity_slice_tmp_16") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_17" (.div (.literal 1000000000000000000000000000000000000) (.localVar "_verity_slice_tmp_16"))],
    .assignVar "_verity_slice_tmp_27" (.localVar "_verity_slice_tmp_17")]

def tPos : List Stmt := [
    .letVar "ln2_1" (.literal 693147180559945309),
    .letVar "offset_1" (.literal 322611214989459870),
    .letVar "_verity_slice_tmp_18" (.add (.localVar "_verity_slice_tmp_4") (.localVar "offset_1")),
    .letVar "_verity_slice_tmp_19" (.literal 0),
    .ite (.eq (.localVar "ln2_1") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_19" (.sdiv (.localVar "_verity_slice_tmp_18") (.localVar "ln2_1"))],
    .letVar "q_1" (.localVar "_verity_slice_tmp_19"),
    .letVar "_verity_slice_tmp_20" (.mul (.localVar "q_1") (.localVar "ln2_1")),
    .letVar "r_1" (.sub (.localVar "_verity_slice_tmp_4") (.localVar "_verity_slice_tmp_20")),
    .letVar "_verity_slice_tmp_21" (.mul (.localVar "r_1") (.localVar "r_1")),
    .letVar "_verity_slice_tmp_22" (.literal 0),
    .ite (.eq (.literal 2000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_22" (.sdiv (.localVar "_verity_slice_tmp_21") (.literal 2000000000000000000))],
    .letVar "secondTerm_1" (.localVar "_verity_slice_tmp_22"),
    .letVar "_verity_slice_tmp_23" (.mul (.localVar "secondTerm_1") (.localVar "r_1")),
    .letVar "_verity_slice_tmp_24" (.literal 0),
    .ite (.eq (.literal 3000000000000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_24" (.sdiv (.localVar "_verity_slice_tmp_23") (.literal 3000000000000000000))],
    .letVar "thirdTerm_1" (.localVar "_verity_slice_tmp_24"),
    .letVar "_verity_slice_tmp_25" (.add (.literal 1000000000000000000) (.localVar "r_1")),
    .letVar "_verity_slice_tmp_26" (.add (.localVar "_verity_slice_tmp_25") (.localVar "secondTerm_1")),
    .letVar "expR_1" (.add (.localVar "_verity_slice_tmp_26") (.localVar "thirdTerm_1")),
    .assignVar "_verity_slice_tmp_27" (.shl (.localVar "q_1") (.localVar "expR_1"))]

def tTail : List Stmt := [
    .letVar "_verity_slice_tmp_28" (.localVar "_verity_slice_tmp_27"),
    .letVar "_verity_slice_tmp_29" (.add (.literal 1000000000000000000) (.localVar "_verity_slice_tmp_28")),
    .letVar "_verity_slice_tmp_30" (.sub (.localVar "_verity_slice_tmp_29") (.literal 1)),
    .letVar "_verity_slice_tmp_31" (.literal 0),
    .ite (.eq (.literal 2) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_31" (.div (.localVar "_verity_slice_tmp_30") (.literal 2))],
    .letVar "_verity_slice_tmp_32" (.localVar "_verity_slice_tmp_31"),
    .letVar "_verity_slice_tmp_33" (.add (.literal 1000000000000000000000000000000000000) (.localVar "_verity_slice_tmp_32")),
    .letVar "_verity_slice_tmp_34" (.literal 0),
    .ite (.eq (.localVar "_verity_slice_tmp_29") (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_34" (.div (.localVar "_verity_slice_tmp_33") (.localVar "_verity_slice_tmp_29"))],
    .letVar "_verity_slice_tmp_35" (.localVar "_verity_slice_tmp_34"),
    .letVar "_verity_slice_tmp_36" (.sub (.literal 100000000000) (.literal 1)),
    .letVar "_verity_slice_tmp_37" (.literal 0),
    .ite (.eq (.literal 2) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_37" (.div (.localVar "_verity_slice_tmp_36") (.literal 2))],
    .letVar "_verity_slice_tmp_38" (.localVar "_verity_slice_tmp_37"),
    .letVar "_verity_slice_tmp_39" (.add (.localVar "_verity_slice_tmp_35") (.localVar "_verity_slice_tmp_38")),
    .letVar "_verity_slice_tmp_40" (.literal 0),
    .ite (.eq (.literal 100000000000) (.literal 0)) [.panic (PanicCode.divisionByZero)] [.assignVar "_verity_slice_tmp_40" (.div (.localVar "_verity_slice_tmp_39") (.literal 100000000000))],
    .letVar "_verity_slice_tmp_41" (.localVar "_verity_slice_tmp_40"),
    .letVar "_verity_slice_tmp_42" (.mul (.localVar "_verity_slice_tmp_41") (.literal 100000000000)),
    .returnValues [.localVar "_verity_slice_tmp_42"]]

theorem wExp_body : functionBody tickLib.model "wExp" =
    .letVar "_verity_slice_tmp_0" (.slt (.param "x") (.literal 0)) ::
    .letVar "_verity_slice_tmp_22" (.literal 0) ::
    .ite (.localVar "_verity_slice_tmp_0") wNeg wPos :: wTail := rfl

theorem tickToPrice_body : functionBody tickLib.model "tickToPrice" =
    tHead ++ .ite (.localVar "_verity_slice_tmp_5") tNeg tPos :: tTail := rfl

/-! ## `wExp` -/

/-- The `x >= 0` branch: `uint256(expR) << uint256(q)` on words. -/
def wCore (x : Nat) : Nat :=
  let q := sdivW (addW x 322611214989459870) 693147180559945309
  let r := subW x (mulW q 693147180559945309)
  let s := sdivW (mulW r r) 2000000000000000000
  let t := sdivW (mulW s r) 3000000000000000000
  shlW q (addW (addW (addW 1000000000000000000 r) s) t)

/-- `wExp` on words; `none` is a revert. -/
def wExpW (x : Nat) : Option Nat :=
  if sltW x 0 then
    if sltW (subW 0 x) 0 then none
    else if wCore (subW 0 x) = 0 then none
    else some (divW 1000000000000000000000000000000000000 (wCore (subW 0 x)))
  else some (wCore x)

theorem exec_wPos (o : DenoteOracle) (s : DenoteState) (n : Nat) (hx : lookupValue s.bindings "x" = n) :
    ∃ t, execStmtList o tickLib.model.fields s wPos = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_22" = wCore n := by
  simp only [wPos]
  wsimp [hx]
  exact ⟨_, rfl, by simp only [lookup_bind_same, wCore]⟩

theorem exec_wNeg_fail (o : DenoteOracle) (s : DenoteState) (n : Nat) (hx : lookupValue s.bindings "x" = n)
    (h : sltW (subW 0 n) 0 = true ∨ wCore (subW 0 n) = 0) :
    ∃ d, execStmtList o tickLib.model.fields s wNeg = .revertWithData d := by
  simp only [wNeg]
  rcases h with h | h
  · wsimp [hx, h]; exact ⟨_, rfl⟩
  · by_cases h' : sltW (subW 0 n) 0 = true
    · wsimp [hx, h']; exact ⟨_, rfl⟩
    · simp only [wCore] at h
      wsimp [hx, h', h]; exact ⟨_, rfl⟩

theorem exec_wNeg_ok (o : DenoteOracle) (s : DenoteState) (n : Nat) (hx : lookupValue s.bindings "x" = n)
    (h1 : ¬ sltW (subW 0 n) 0 = true) (h2 : ¬ wCore (subW 0 n) = 0) :
    ∃ t, execStmtList o tickLib.model.fields s wNeg = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_22" =
        divW 1000000000000000000000000000000000000 (wCore (subW 0 n)) := by
  simp only [wNeg]
  simp only [wCore] at h2
  wsimp [hx, h1, h2]
  exact ⟨_, rfl, by simp only [lookup_bind_same, wCore]⟩

theorem exec_wTail (o : DenoteOracle) (s : DenoteState) (v : Nat)
    (hv : lookupValue s.bindings "_verity_slice_tmp_22" = v) :
    ∃ t, execStmtList o tickLib.model.fields s wTail = .stop t ∧ t.observedReturnWords = some [v % 2 ^ 256] := by
  simp only [wTail]
  wsimp [hv]
  exact ⟨_, rfl, rfl⟩

theorem lookup_x (n : Nat) : lookupValue [("x", n)] "x" = n := rfl

theorem result_then (o : DenoteOracle) (s : DenoteState) (a b : List Stmt) :
    result (execStmtList o tickLib.model.fields s (a ++ b)) =
      result (match execStmtList o tickLib.model.fields s a with
        | .continue t => execStmtList o tickLib.model.fields t b | out => out) :=
  congrArg result (exec_append _ _ _ _ _)

theorem run_eq (o : DenoteOracle) (w : Verity.ContractState) (name : String) (args : Env) :
    runFunction o tickLib.model name w args =
      result (execStmtList o tickLib.model.fields { world := w, bindings := args, errors := tickLib.model.errors }
        (functionBody tickLib.model name)) := rfl

/-- The state after `wExp`'s first two statements. -/
def wState (w : Verity.ContractState) (n b : Nat) : DenoteState :=
  { world := w, bindings := bindValue (bindValue [("x", n)] "_verity_slice_tmp_0" b) "_verity_slice_tmp_22" 0,
    errors := tickLib.model.errors }

theorem wExp_start (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) :
    execStmtList o tickLib.model.fields { world := w, bindings := [("x", n)], errors := tickLib.model.errors }
      (functionBody tickLib.model "wExp") =
    if sltW n 0 then execStmtList o tickLib.model.fields (wState w n 1) (wNeg ++ wTail)
    else execStmtList o tickLib.model.fields (wState w n 0) (wPos ++ wTail) := by
  rw [wExp_body]
  simp only [st_let, ev_slt, ev_param, ev_lit, ev_local, Option.bind_some, wn, Nat.reducePow,
    Nat.reduceMod, boolWord, lookup_bind_same, st_ite, bw_ne, lookup_bind_other, ne_eq, String.reduceEq,
    not_false_eq_true]
  rw [lookup_x]
  by_cases h : sltW n 0 = true
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

/-- Running the imported `wExp` on the word `n`. -/
theorem run_wExp (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) :
    runFunction o tickLib.model "wExp" w [("x", n)] = (wExpW n).map fun v => [v % 2 ^ 256] := by
  rw [run_eq, wExp_start]
  by_cases hneg : sltW n 0 = true
  · simp only [hneg, ↓reduceIte, result_then]
    by_cases hf : sltW (subW 0 n) 0 = true ∨ wCore (subW 0 n) = 0
    · obtain ⟨d, hd⟩ := exec_wNeg_fail o (wState w n 1) n rfl hf
      rw [hd]
      rcases hf with hf | hf <;> simp [wExpW, hneg, hf, result]
    · rw [not_or] at hf
      obtain ⟨t, ht, hv⟩ := exec_wNeg_ok o (wState w n 1) n rfl hf.1 hf.2
      obtain ⟨u, hu, hr⟩ := exec_wTail o t _ hv
      rw [ht]
      simp only [hu, hr, result, wExpW, hneg, hf.1, hf.2, ↓reduceIte, Option.map_some,
        Bool.false_eq_true, Nat.reducePow]
  · simp only [hneg, ↓reduceIte, Bool.false_eq_true, result_then]
    obtain ⟨t, ht, hv⟩ := exec_wPos o (wState w n 0) n rfl
    obtain ⟨u, hu, hr⟩ := exec_wTail o t _ hv
    rw [ht]
    simp only [hu, hr, result, wExpW, hneg, ↓reduceIte, Option.map_some, Bool.false_eq_true,
      Nat.reducePow]

/-! ## `tickToPrice` -/

/-- The two `divHalfDownUnchecked` and the final `* PRICE_ROUNDING_STEP`, from `W = wExp(..)`. -/
def tailW (W : Nat) : Option Nat :=
  let d := addW 1000000000000000000 W
  if d = 0 then none
  else some (mulW (divW (addW (divW (addW 1000000000000000000000000000000000000 (divW (subW d 1) 2)) d)
    (divW (subW 100000000000 1) 2)) 100000000000) 100000000000)

/-- `tickToPrice` on words; `none` is a revert. -/
def tickW (tick : Nat) : Option Nat :=
  if tick ≤ 6744 then (wExpW (mulW 4987541511039073 (subW (divW 6744 2) tick))).bind tailW else none

theorem exec_tPos (o : DenoteOracle) (s : DenoteState) (n : Nat)
    (hx : lookupValue s.bindings "_verity_slice_tmp_4" = n) :
    ∃ t, execStmtList o tickLib.model.fields s tPos = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_27" = wCore n := by
  simp only [tPos]
  wsimp [hx]
  exact ⟨_, rfl, by simp only [lookup_bind_same, wCore]⟩

theorem exec_tNeg_fail (o : DenoteOracle) (s : DenoteState) (n : Nat)
    (hx : lookupValue s.bindings "_verity_slice_tmp_4" = n)
    (h : sltW (subW 0 n) 0 = true ∨ wCore (subW 0 n) = 0) :
    ∃ d, execStmtList o tickLib.model.fields s tNeg = .revertWithData d := by
  simp only [tNeg]
  rcases h with h | h
  · wsimp [hx, h]; exact ⟨_, rfl⟩
  · by_cases h' : sltW (subW 0 n) 0 = true
    · wsimp [hx, h']; exact ⟨_, rfl⟩
    · simp only [wCore] at h
      wsimp [hx, h', h]; exact ⟨_, rfl⟩

theorem exec_tNeg_ok (o : DenoteOracle) (s : DenoteState) (n : Nat)
    (hx : lookupValue s.bindings "_verity_slice_tmp_4" = n)
    (h1 : ¬ sltW (subW 0 n) 0 = true) (h2 : ¬ wCore (subW 0 n) = 0) :
    ∃ t, execStmtList o tickLib.model.fields s tNeg = .continue t ∧
      lookupValue t.bindings "_verity_slice_tmp_27" =
        divW 1000000000000000000000000000000000000 (wCore (subW 0 n)) := by
  simp only [tNeg]
  simp only [wCore] at h2
  wsimp [hx, h1, h2]
  exact ⟨_, rfl, by simp only [lookup_bind_same, wCore]⟩

theorem exec_tTail (o : DenoteOracle) (s : DenoteState) (W : Nat)
    (hv : lookupValue s.bindings "_verity_slice_tmp_27" = W) :
    result (execStmtList o tickLib.model.fields s tTail) = (tailW W).map fun v => [v % 2 ^ 256] := by
  simp only [tTail]
  by_cases hd : addW 1000000000000000000 W = 0
  · wsimp [hv, hd, tailW, result]
  · wsimp [hv, hd, tailW, result]

theorem lookup_tick (n : Nat) : lookupValue [("tick", n)] "tick" = n := rfl

/-- The state after `tHead`. -/
def tState (w : Verity.ContractState) (n b : Nat) : DenoteState :=
  { world := w, bindings :=
      bindValue (bindValue (bindValue (bindValue (bindValue (bindValue (bindValue (bindValue [("tick", n)]
        "_verity_slice_tmp_0" 1) "_verity_slice_tmp_1" 0) "_verity_slice_tmp_1" (divW 6744 2))
        "_verity_slice_tmp_2" (divW 6744 2)) "_verity_slice_tmp_3" (subW (divW 6744 2) n))
        "_verity_slice_tmp_4" (mulW 4987541511039073 (subW (divW 6744 2) n)))
        "_verity_slice_tmp_5" b)
        "_verity_slice_tmp_27" 0,
    errors := tickLib.model.errors }

theorem tickToPrice_start (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) (hn : n ≤ 6744) :
    execStmtList o tickLib.model.fields { world := w, bindings := [("tick", n)], errors := tickLib.model.errors }
      (functionBody tickLib.model "tickToPrice") =
    if sltW (mulW 4987541511039073 (subW (divW 6744 2) n)) 0 then
      execStmtList o tickLib.model.fields (tState w n 1) (tNeg ++ tTail)
    else execStmtList o tickLib.model.fields (tState w n 0) (tPos ++ tTail) := by
  rw [tickToPrice_body]
  simp only [tHead, List.cons_append, List.nil_append]
  rw [st_let, ev_le, ev_param, ev_lit]
  simp only [Option.bind_some, wn, Nat.reducePow, Nat.reduceMod, boolWord, lookup_tick, decide_eq_true hn,
    ↓reduceIte]
  rw [st_require_ok _ _ _ _ _ _ _ (by rw [ev_local, lookup_bind_same])]
  wsimp [lookup_tick]
  by_cases h : sltW (mulW 4987541511039073 (subW (divW 6744 2) n)) 0 = true
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem tickToPrice_out (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) (hn : ¬ n ≤ 6744) :
    result (execStmtList o tickLib.model.fields { world := w, bindings := [("tick", n)], errors := tickLib.model.errors }
      (functionBody tickLib.model "tickToPrice")) = none := by
  rw [tickToPrice_body]
  simp only [tHead, List.cons_append, List.nil_append]
  rw [st_let, ev_le, ev_param, ev_lit]
  simp only [Option.bind_some, wn, Nat.reducePow, Nat.reduceMod, boolWord, lookup_tick, decide_eq_false hn,
    ↓reduceIte, Bool.false_eq_true]
  exact st_require_fail _ _ _ _ _ _ (by rw [ev_local, lookup_bind_same])

theorem tState_x (w : Verity.ContractState) (n b : Nat) :
    lookupValue (tState w n b).bindings "_verity_slice_tmp_4" = mulW 4987541511039073 (subW (divW 6744 2) n) := by
  simp only [tState, lookup_bind_same, lookup_bind_other, ne_eq, String.reduceEq, not_false_eq_true]

/-- `tickToPrice` calls `wExp` on `X = LN_ONE_PLUS_DELTA * (MAX_TICK / 2 - tick)`. -/
theorem tickW_eq (n : Nat) (hn : n ≤ 6744) :
    tickW n = (wExpW (mulW 4987541511039073 (subW (divW 6744 2) n))).bind tailW := by
  unfold tickW; rw [if_pos hn]

theorem run_tick_neg (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) (hn : n ≤ 6744)
    (hneg : sltW (mulW 4987541511039073 (subW (divW 6744 2) n)) 0 = true) :
    result (execStmtList o tickLib.model.fields (tState w n 1) (tNeg ++ tTail)) =
      (tickW n).map fun v => [v % 2 ^ 256] := by
  rw [result_then, tickW_eq n hn]
  have hx := tState_x w n 1
  generalize mulW 4987541511039073 (subW (divW 6744 2) n) = X at hx hneg ⊢
  unfold wExpW
  rw [if_pos hneg]
  by_cases hf : sltW (subW 0 X) 0 = true ∨ wCore (subW 0 X) = 0
  · obtain ⟨d, hd⟩ := exec_tNeg_fail o (tState w n 1) _ hx hf
    rw [hd]
    rcases hf with hf | hf
    · rw [if_pos hf]; rfl
    · by_cases h' : sltW (subW 0 X) 0 = true
      · rw [if_pos h']; rfl
      · rw [if_neg h', if_pos hf]; rfl
  · rw [not_or] at hf
    obtain ⟨t, ht, hv⟩ := exec_tNeg_ok o (tState w n 1) _ hx hf.1 hf.2
    rw [ht, if_neg hf.1, if_neg hf.2, Option.bind_some]
    exact exec_tTail o t _ hv

theorem run_tick_pos (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) (hn : n ≤ 6744)
    (hneg : ¬ sltW (mulW 4987541511039073 (subW (divW 6744 2) n)) 0 = true) :
    result (execStmtList o tickLib.model.fields (tState w n 0) (tPos ++ tTail)) =
      (tickW n).map fun v => [v % 2 ^ 256] := by
  rw [result_then, tickW_eq n hn]
  have hx := tState_x w n 0
  generalize mulW 4987541511039073 (subW (divW 6744 2) n) = X at hx hneg ⊢
  unfold wExpW
  rw [if_neg hneg]
  obtain ⟨t, ht, hv⟩ := exec_tPos o (tState w n 0) _ hx
  rw [ht, Option.bind_some]
  exact exec_tTail o t _ hv

/-- Running the imported `tickToPrice` on the word `n`. -/
theorem run_tickToPrice (o : DenoteOracle) (w : Verity.ContractState) (n : Nat) :
    runFunction o tickLib.model "tickToPrice" w [("tick", n)] = (tickW n).map fun v => [v % 2 ^ 256] := by
  rw [run_eq]
  by_cases hn : n ≤ 6744
  · rw [tickToPrice_start o w n hn]
    by_cases hneg : sltW (mulW 4987541511039073 (subW (divW 6744 2) n)) 0 = true
    · rw [if_pos hneg]; exact run_tick_neg o w n hn hneg
    · rw [if_neg hneg]; exact run_tick_pos o w n hn hneg
  · rw [tickToPrice_out o w n hn]
    unfold tickW; rw [if_neg hn]; rfl

end TickLib.Execution
