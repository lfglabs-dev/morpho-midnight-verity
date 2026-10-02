import Midnight.Lemmas.Arith
import Compiler.SolidityImport.Access
import Compiler.SolidityImport.Coverage

/-!
Unfold a successful `updatePositionView` and identify its return words with
`viewResult?`.
-/

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas

namespace Midnight.Lemmas

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem find_filter (l : List (String × Nat)) {name key : String} (h : name ≠ key) :
    (l.filter (fun e => e.1 != name)).find? (fun e => e.1 == key) =
      l.find? (fun e => e.1 == key) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hdrop : (hd.1 != name)
    · have heq : hd.1 = name := by
        cases hb : hd.1 == name
        · simp [bne, hb] at hdrop
        · exact (beq_iff_eq).1 hb
      have hkey : (hd.1 == key) = false := by
        cases hb : hd.1 == key
        · rfl
        · have : hd.1 = key := (beq_iff_eq).1 hb
          exact absurd (heq.symm.trans this) h
      simp [List.filter, hdrop, List.find?, hkey, ih]
    · simp [List.filter, hdrop, List.find?, ih]

theorem lookupValue_bind_eq (env : Env) (name : String) (value : Nat) :
    lookupValue (bindValue env name value) name = value := by
  simp [lookupValue, bindValue, List.find?]

theorem lookupValue_bind_ne {env : Env} {name key : String} {value : Nat}
    (h : name ≠ key) :
    lookupValue (bindValue env name value) key = lookupValue env key := by
  simp only [lookupValue, bindValue, List.find?]
  have hhead : (name == key) = false := by
    simpa [beq_iff_eq] using h
  simp [hhead, find_filter _ h]

theorem lookup_after {env : Env} {name key : String} {value old : Nat}
    (h : lookupValue env key = old) :
    lookupValue (bindValue env name value) key = if name = key then value else old := by
  by_cases hk : name = key
  · simp [hk, lookupValue_bind_eq]
  · simp [hk, lookupValue_bind_ne hk, h]

theorem bindValue_shadow (env : Env) (name : String) (v w : Nat) :
    bindValue (bindValue env name v) name w = bindValue env name w := by
  simp only [bindValue, List.filter]
  have hdrop : (name != name) = false := by simp [bne]
  simp [hdrop, List.filter_filter]

def argEnv (maturity idv userv : Nat) : Env :=
  [("market_maturity", maturity), ("id", idv), ("user", userv)]

theorem lookup_argEnv_maturity (maturity idv userv : Nat) :
    lookupValue (argEnv maturity idv userv) "market_maturity" = maturity := by
  simp [argEnv, lookupValue, List.find?]

theorem lookup_argEnv_id (maturity idv userv : Nat) :
    lookupValue (argEnv maturity idv userv) "id" = idv := by
  simp [argEnv, lookupValue, List.find?]

theorem lookup_argEnv_user (maturity idv userv : Nat) :
    lookupValue (argEnv maturity idv userv) "user" = userv := by
  simp [argEnv, lookupValue, List.find?]

theorem lookup_argEnv_credit (maturity idv userv : Nat) :
    lookupValue (argEnv maturity idv userv) "_credit" = 0 := by
  simp [argEnv, lookupValue, List.find?]

def withBind (st : DenoteState) (name : String) (v : Nat) : DenoteState :=
  { st with bindings := bindValue st.bindings name v }

theorem word_of_lt {n : Nat} (h : n < MOD) : wordNormalize n = n := by
  unfold wordNormalize
  show (Uint256.ofNat n).val = n
  rw [Uint256.val_ofNat]
  unfold MOD at h
  rw [Uint256.modulus, UINT256_MODULUS]
  exact Nat.mod_eq_of_lt h

theorem uint_val {n : Nat} (h : n < MOD) : (Uint256.ofNat n).val = n := by
  rw [Uint256.val_ofNat]
  unfold MOD at h
  rw [Uint256.modulus, UINT256_MODULUS]
  exact Nat.mod_eq_of_lt h

theorem le_U_lt_MOD {n : Nat} (h : n ≤ U) : n < MOD :=
  Nat.lt_of_le_of_lt h U_lt_MOD

theorem zero_lt_mod : (0 : Nat) < MOD := by decide

theorem one_lt_mod : (1 : Nat) < MOD := by decide

theorem U_lt : U < MOD := U_lt_MOD

def body : List Stmt := functionBody midnight.model "updatePositionView"

def iteAt (ss : List Stmt) (i : Nat) : Expr × List Stmt × List Stmt :=
  match ss.drop i with
  | .ite c th el :: _ => (c, th, el)
  | _ => (.literal 0, [], [])

theorem exec_let {oracle : DenoteOracle} {st : DenoteState} {dest : String} {e : Expr}
    {v : Nat} {rest : List Stmt}
    (hv : evalExpr oracle midnight.model.fields st e = some v) :
    execStmtList oracle midnight.model.fields st (.letVar dest e :: rest) =
      execStmtList oracle midnight.model.fields (withBind st dest v) rest := by
  rw [execStmtList.eq_2, execStmt_letVar_arm, hv]
  rfl

theorem exec_assign {oracle : DenoteOracle} {st : DenoteState} {dest : String} {e : Expr}
    {v : Nat} {rest : List Stmt}
    (hv : evalExpr oracle midnight.model.fields st e = some v) :
    execStmtList oracle midnight.model.fields st (.assignVar dest e :: rest) =
      execStmtList oracle midnight.model.fields (withBind st dest v) rest := by
  rw [execStmtList.eq_2, execStmt_assignVar_arm, hv]
  rfl

theorem exec_append (oracle : DenoteOracle) (fields : List Field) (st : DenoteState)
    (xs ys : List Stmt) :
    execStmtList oracle fields st (xs ++ ys) =
      match execStmtList oracle fields st xs with
      | .continue next => execStmtList oracle fields next ys
      | .stop next => .stop next
      | .return v next => .return v next
      | .revert => .revert := by
  induction xs generalizing st with
  | nil => simp [execStmtList.eq_1]
  | cons stmt rest ih =>
    rw [List.cons_append, execStmtList.eq_2, execStmtList.eq_2]
    cases execStmt oracle fields st stmt <;> simp [ih]

theorem eval_literal {oracle : DenoteOracle} {st : DenoteState} {n : Nat} (h : n < MOD) :
    evalExpr oracle midnight.model.fields st (.literal n) = some n := by
  rw [evalExpr_literal_arm, word_of_lt h]

theorem eval_local {oracle : DenoteOracle} {st : DenoteState} {name : String} :
    evalExpr oracle midnight.model.fields st (.localVar name) =
      some (lookupValue st.bindings name) := by
  rw [evalExpr_localVar_arm]

theorem eval_param {oracle : DenoteOracle} {st : DenoteState} {name : String} :
    evalExpr oracle midnight.model.fields st (.param name) =
      some (lookupValue st.bindings name) := by
  rw [evalExpr_param_arm]

theorem eval_timestamp {oracle : DenoteOracle} {st : DenoteState} :
    evalExpr oracle midnight.model.fields st .blockTimestamp =
      some st.world.blockTimestamp.val := by
  rw [evalExpr_blockTimestamp_arm]

theorem eval_local_eq {oracle : DenoteOracle} {st : DenoteState} {name : String} {v : Nat}
    (h : lookupValue st.bindings name = v) :
    evalExpr oracle midnight.model.fields st (.localVar name) = some v := by
  simp [eval_local, h]

theorem eval_param_eq {oracle : DenoteOracle} {st : DenoteState} {name : String} {v : Nat}
    (h : lookupValue st.bindings name = v) :
    evalExpr oracle midnight.model.fields st (.param name) = some v := by
  simp [eval_param, h]

private theorem option_bind_some {α β : Type} (v : α) (k : α → Option β) :
    (some v >>= k) = k v := by
  simp [Option.bind]

theorem eval_lt {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb) :
    evalExpr oracle midnight.model.fields st (.lt a b) =
      some (boolWord (decide (va < vb))) := by
  rw [evalExpr_lt_arm, ha, hb]
  simp [bind, Option.bind, pure]

theorem eval_gt {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb) :
    evalExpr oracle midnight.model.fields st (.gt a b) =
      some (boolWord (decide (vb < va))) := by
  rw [evalExpr_gt_arm, ha, hb]
  simp [bind, Option.bind, pure]

theorem eval_eq {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb) :
    evalExpr oracle midnight.model.fields st (.eq a b) =
      some (boolWord (decide (va = vb))) := by
  rw [evalExpr_eq_arm, ha, hb]
  simp [bind, Option.bind, pure]

theorem eval_sub {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb)
    (hva : va < MOD) (hvb : vb < MOD) (hle : vb ≤ va) :
    evalExpr oracle midnight.model.fields st (.sub a b) = some (va - vb) := by
  rw [evalExpr_sub_arm, ha, hb]
  simp only [bind, Option.bind, pure, Option.some.injEq]
  have hva' : (Uint256.ofNat va).val = va := uint_val hva
  have hvb' : (Uint256.ofNat vb).val = vb := uint_val hvb
  have hle' : (Uint256.ofNat vb).val ≤ (Uint256.ofNat va).val := by
    rw [hva', hvb']; exact hle
  rw [Uint256.sub_eq_of_le hle', hva', hvb']

theorem eval_add {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb)
    (hva : va < MOD) (hvb : vb < MOD) :
    evalExpr oracle midnight.model.fields st (.add a b) = some ((va + vb) % MOD) := by
  rw [evalExpr_add_arm, ha, hb]
  simp only [bind, Option.bind, pure, HAdd.hAdd, Uint256.add, uint_val hva, uint_val hvb,
    Uint256.val_ofNat, Uint256.modulus]
  rw [MOD, UINT256_MODULUS]

theorem eval_mul {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb)
    (hva : va < MOD) (hvb : vb < MOD) :
    evalExpr oracle midnight.model.fields st (.mul a b) = some ((va * vb) % MOD) := by
  rw [evalExpr_mul_arm, ha, hb]
  simp only [bind, Option.bind, pure, HMul.hMul, Uint256.mul, uint_val hva, uint_val hvb,
    Uint256.val_ofNat, Uint256.modulus]
  rw [MOD, UINT256_MODULUS]

theorem eval_div {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (ha : evalExpr oracle midnight.model.fields st a = some va)
    (hb : evalExpr oracle midnight.model.fields st b = some vb)
    (hva : va < MOD) (hvb : vb < MOD) (hne : vb ≠ 0) :
    evalExpr oracle midnight.model.fields st (.div a b) = some (va / vb) := by
  rw [evalExpr_div_arm, ha, hb]
  simp only [bind, Option.bind, pure, Option.some.injEq]
  have hva' : (Uint256.ofNat va).val = va := uint_val hva
  have hvb' : (Uint256.ofNat vb).val = vb := uint_val hvb
  have hquot : va / vb < MOD := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hva
  rw [show ((Uint256.ofNat va) / (Uint256.ofNat vb)) =
      Uint256.div (Uint256.ofNat va) (Uint256.ofNat vb) from rfl]
  simp only [Uint256.div, hva', hvb', hne, ite_false]
  exact uint_val hquot

theorem exec_panic_overflow {oracle : DenoteOracle} {st : DenoteState} {rest : List Stmt} :
    execStmtList oracle midnight.model.fields st (.panic .arithmeticOverflow :: rest) = .revert := by
  rw [execStmtList.eq_2, execStmt_panic_arm]

theorem exec_panic_divzero {oracle : DenoteOracle} {st : DenoteState} {rest : List Stmt} :
    execStmtList oracle midnight.model.fields st (.panic .divisionByZero :: rest) = .revert := by
  rw [execStmtList.eq_2, execStmt_panic_arm]

theorem bne_eq_false {c : Nat} : (c != 0) = false ↔ c = 0 := by
  cases c <;> simp [bne]

theorem bne_eq_true {c : Nat} : (c != 0) = true ↔ c ≠ 0 := by
  cases c <;> simp [bne]

theorem exec_ite {oracle : DenoteOracle} {st : DenoteState} {cond : Expr} {th el rest : List Stmt}
    {c : Nat} (hc : evalExpr oracle midnight.model.fields st cond = some c) :
    execStmtList oracle midnight.model.fields st (.ite cond th el :: rest) =
      execStmtList oracle midnight.model.fields st ((if c = 0 then el else th) ++ rest) := by
  rw [execStmtList.eq_2, execStmt_ite_arm, hc]
  by_cases hz : c = 0
  · have hbit : (c != 0) = false := bne_eq_false.mpr hz
    simp only [hbit]
    simp only [show (false = true) = False by decide, if_false]
    have happ := exec_append oracle midnight.model.fields st el rest
    simp [hz]
    exact happ.symm
  · have hbit : (c != 0) = true := bne_eq_true.mpr hz
    simp only [hbit, if_true]
    have happ := exec_append oracle midnight.model.fields st th rest
    simp [hz]
    exact happ.symm

theorem prod_div_eq_iff {a b : Nat} (ha0 : a ≠ 0) (_ha : a < MOD) (_hb : b < MOD) :
    ((a * b) % MOD) / a = b ↔ a * b < MOD := by
  constructor
  · intro h
    have hmul : a * b ≤ (a * b) % MOD := by
      have := Nat.mul_div_le ((a * b) % MOD) a
      rwa [h] at this
    have hmod : (a * b) % MOD ≤ a * b := Nat.mod_le _ _
    have heq : (a * b) % MOD = a * b := Nat.le_antisymm hmod hmul
    rw [← heq]
    exact Nat.mod_lt _ zero_lt_mod
  · intro h
    rw [Nat.mod_eq_of_lt h]
    exact Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero ha0)

theorem add_mod_lt_iff {a b : Nat} (ha : a < MOD) (hb : b < MOD) :
    (a + b) % MOD < a ↔ MOD ≤ a + b := by
  by_cases h : MOD ≤ a + b
  · have hx : a + b - MOD < a := by omega
    have hmod : (a + b) % MOD = a + b - MOD := by
      have hrepr : a + b = MOD + (a + b - MOD) := by omega
      have hx' : a + b - MOD < MOD := by omega
      rw [hrepr, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hx']
      omega
    rw [hmod]
    exact iff_of_true hx h
  · have hlt : a + b < MOD := Nat.lt_of_not_le h
    rw [Nat.mod_eq_of_lt hlt]
    exact iff_of_false (by omega) h

def csubBlock (dest : String) (lhs rhs : Expr) : List Stmt :=
  [.letVar dest (.literal 0),
    .ite (.lt lhs rhs) [.panic .arithmeticOverflow] [.assignVar dest (.sub lhs rhs)]]

def cmulBlock (dest : String) (a b : Expr) : List Stmt :=
  [.letVar dest (.literal 0),
    .ite (.eq a (.literal 0))
      [.assignVar dest (.mul a b)]
      [.ite (.eq (.div (.mul a b) a) b)
        [.assignVar dest (.mul a b)]
        [.panic .arithmeticOverflow]]]

def cdivBlock (dest : String) (numer divisor : Expr) : List Stmt :=
  [.letVar dest (.literal 0),
    .ite (.eq divisor (.literal 0))
      [.panic .divisionByZero]
      [.assignVar dest (.div numer divisor)]]

def caddBlock (dest : String) (x y : Expr) : List Stmt :=
  [.letVar dest (.literal 0),
    .ite (.lt (.add x y) x)
      [.panic .arithmeticOverflow]
      [.assignVar dest (.add x y)]]

theorem withBind_shadow (st : DenoteState) (name : String) (v w : Nat) :
    withBind (withBind st name v) name w = withBind st name w := by
  simp [withBind, bindValue_shadow]

theorem exec_csubBlock {oracle : DenoteOracle} {st : DenoteState} {dest : String}
    {lhs rhs : Expr} {rest : List Stmt} {a b : Nat}
    (hl : evalExpr oracle midnight.model.fields (withBind st dest 0) lhs = some a)
    (hr : evalExpr oracle midnight.model.fields (withBind st dest 0) rhs = some b)
    (ha : a < MOD) (hb : b < MOD) :
    execStmtList oracle midnight.model.fields st (csubBlock dest lhs rhs ++ rest) =
      match csub? a b with
      | some v => execStmtList oracle midnight.model.fields (withBind st dest v) rest
      | none => .revert := by
  unfold csubBlock
  rw [List.cons_append, List.cons_append, List.nil_append]
  rw [exec_let (eval_literal zero_lt_mod)]
  rw [exec_ite (eval_lt hl hr)]
  by_cases hlt : a < b
  · have hnle : ¬ b ≤ a := Nat.not_le_of_gt hlt
    simp [boolWord, hlt, csub?, hnle, List.cons_append, List.nil_append]
    rw [exec_panic_overflow]
  · have hle : b ≤ a := Nat.not_lt.mp hlt
    simp [boolWord, hlt, csub?, hle, List.cons_append, List.nil_append]
    rw [exec_assign (eval_sub hl hr ha hb hle)]
    rw [withBind_shadow]

theorem exec_cmulBlock {oracle : DenoteOracle} {st : DenoteState} {dest : String}
    {aExpr bExpr : Expr} {rest : List Stmt} {a b : Nat}
    (haE : evalExpr oracle midnight.model.fields (withBind st dest 0) aExpr = some a)
    (hbE : evalExpr oracle midnight.model.fields (withBind st dest 0) bExpr = some b)
    (ha : a < MOD) (hb : b < MOD) :
    execStmtList oracle midnight.model.fields st (cmulBlock dest aExpr bExpr ++ rest) =
      match cmul? a b with
      | some v => execStmtList oracle midnight.model.fields (withBind st dest v) rest
      | none => .revert := by
  unfold cmulBlock
  rw [List.cons_append, List.cons_append, List.nil_append]
  rw [exec_let (eval_literal zero_lt_mod)]
  rw [exec_ite (eval_eq haE (eval_literal zero_lt_mod))]
  by_cases ha0 : a = 0
  · simp [boolWord, ha0, cmul?, Nat.zero_mul, zero_lt_mod, List.cons_append, List.nil_append,
      Nat.zero_mod]
    rw [exec_assign (eval_mul haE hbE ha hb)]
    simp [ha0, Nat.zero_mul, Nat.zero_mod, withBind_shadow]
  · simp [boolWord, ha0]
    have hprod : (a * b) % MOD < MOD := Nat.mod_lt _ zero_lt_mod
    have hmul := eval_mul haE hbE ha hb
    have hdiv := eval_div hmul haE hprod ha ha0
    rw [exec_ite (eval_eq hdiv hbE)]
    by_cases hok : a * b < MOD
    · have hdivEq : ((a * b) % MOD) / a = b := (prod_div_eq_iff ha0 ha hb).2 hok
      simp [boolWord, hdivEq, cmul?, hok, List.cons_append, List.nil_append]
      rw [exec_assign hmul]
      simp [Nat.mod_eq_of_lt hok, withBind_shadow]
    · have hdivNe : ((a * b) % MOD) / a ≠ b := by
        intro h
        exact hok ((prod_div_eq_iff ha0 ha hb).1 h)
      simp [boolWord, hdivNe, cmul?, hok, List.cons_append, List.nil_append]
      rw [exec_panic_overflow]

theorem exec_cdivBlock {oracle : DenoteOracle} {st : DenoteState} {dest : String}
    {numer divisor : Expr} {rest : List Stmt} {a b : Nat}
    (haE : evalExpr oracle midnight.model.fields (withBind st dest 0) numer = some a)
    (hbE : evalExpr oracle midnight.model.fields (withBind st dest 0) divisor = some b)
    (ha : a < MOD) (hb : b < MOD) :
    execStmtList oracle midnight.model.fields st (cdivBlock dest numer divisor ++ rest) =
      match cdiv? a b with
      | some v => execStmtList oracle midnight.model.fields (withBind st dest v) rest
      | none => .revert := by
  unfold cdivBlock
  rw [List.cons_append, List.cons_append, List.nil_append]
  rw [exec_let (eval_literal zero_lt_mod)]
  rw [exec_ite (eval_eq hbE (eval_literal zero_lt_mod))]
  by_cases hb0 : b = 0
  · simp [boolWord, hb0, cdiv?, List.cons_append, List.nil_append]
    rw [exec_panic_divzero]
  · simp [boolWord, hb0, cdiv?, List.cons_append, List.nil_append]
    rw [exec_assign (eval_div haE hbE ha hb hb0)]
    rw [withBind_shadow]

theorem exec_caddBlock {oracle : DenoteOracle} {st : DenoteState} {dest : String}
    {x y : Expr} {rest : List Stmt} {a b : Nat}
    (hx : evalExpr oracle midnight.model.fields (withBind st dest 0) x = some a)
    (hy : evalExpr oracle midnight.model.fields (withBind st dest 0) y = some b)
    (ha : a < MOD) (hb : b < MOD) :
    execStmtList oracle midnight.model.fields st (caddBlock dest x y ++ rest) =
      match cadd? a b with
      | some v => execStmtList oracle midnight.model.fields (withBind st dest v) rest
      | none => .revert := by
  unfold caddBlock
  rw [List.cons_append, List.cons_append, List.nil_append]
  rw [exec_let (eval_literal zero_lt_mod)]
  have hadd := eval_add hx hy ha hb
  rw [exec_ite (eval_lt hadd hx)]
  by_cases hok : a + b < MOD
  · have hnot : ¬ (a + b) % MOD < a := by
      rw [add_mod_lt_iff ha hb]
      exact Nat.not_le.mpr hok
    simp [boolWord, hnot, cadd?, hok, Nat.mod_eq_of_lt hok, List.cons_append, List.nil_append]
    rw [exec_assign hadd]
    simp [Nat.mod_eq_of_lt hok, withBind_shadow]
  · have hlt : (a + b) % MOD < a := (add_mod_lt_iff ha hb).2 (Nat.le_of_not_gt hok)
    simp [boolWord, hlt, cadd?, hok, List.cons_append, List.nil_append]
    rw [exec_panic_overflow]
