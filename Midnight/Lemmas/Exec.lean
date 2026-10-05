import Midnight.Lemmas.Arith
import Midnight.Spec
import Compiler.SolidityImport.Access

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core

attribute [local irreducible] Compiler.CompilationModel.SolidityImport.readMember

namespace Midnight.Lemmas

/-- Bind a local without expanding the rest of the denotation state. -/
def withBind (s : DenoteState) (name : String) (v : Nat) : DenoteState :=
  { s with bindings := bindValue s.bindings name v }

theorem exec_let (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (name : String) (e : Expr) (v : Nat) (rest : List Stmt)
    (h : evalExpr o fs s e = some v) :
    execStmtList o fs s (.letVar name e :: rest) =
      execStmtList o fs (withBind s name v) rest := by
  simp [execStmtList, execStmt, h, withBind]

theorem exec_assign (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (name : String) (e : Expr) (v : Nat) (rest : List Stmt)
    (h : evalExpr o fs s e = some v) :
    execStmtList o fs s (.assignVar name e :: rest) =
      execStmtList o fs (withBind s name v) rest := by
  simp [execStmtList, execStmt, h, withBind]

theorem bindings_withBind (s : DenoteState) (name : String) (v : Nat) :
    (withBind s name v).bindings = bindValue s.bindings name v := rfl

theorem world_withBind (s : DenoteState) (name : String) (v : Nat) :
    (withBind s name v).world = s.world := rfl

theorem exec_append (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (a b : List Stmt) : execStmtList o fs s (a ++ b) =
    match execStmtList o fs s a with
    | .continue t => execStmtList o fs t b
    | out => out := by
  induction a generalizing s with
  | nil => rfl
  | cons stmt rest ih =>
    simp only [List.cons_append, execStmtList]
    cases execStmt o fs s stmt <;> simp_all

theorem match_exec_append (o : DenoteOracle) (fs : List Field) (rest : List Stmt) :
    ∀ x : StmtOutcome,
    (match x with
      | .continue next => execStmtList o fs next rest
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert) =
    (match x with
      | .continue t => execStmtList o fs t rest
      | out => out) := by
  intro x; cases x <;> rfl

theorem exec_ite_some (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (cond : Expr) (yes no rest : List Stmt) (v : Nat)
    (hv : evalExpr o fs s cond = some v) :
    execStmtList o fs s (.ite cond yes no :: rest) =
      execStmtList o fs s ((if v = 0 then no else yes) ++ rest) := by
  have hstmt : execStmt o fs s (.ite cond yes no) =
      execStmtList o fs s (if v = 0 then no else yes) := by
    simp [execStmt, hv]
    by_cases hz : v = 0 <;> simp [hz]
  simp only [execStmtList, hstmt, exec_append]
  exact match_exec_append o fs rest _

theorem exec_return3 (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (a b c : String) :
    execStmtList o fs s [.returnValues [.localVar a, .localVar b, .localVar c]] =
      .stop { s with observedReturnWords := some [
        wordNormalize (lookupValue s.bindings a),
        wordNormalize (lookupValue s.bindings b),
        wordNormalize (lookupValue s.bindings c)] } := by
  rfl

theorem lookup_bind_hit (env : Env) (name : String) (v : Nat) :
    lookupValue (bindValue env name v) name = v := by
  simp [lookupValue, bindValue]

theorem lookup_bind_eq (env : Env) (name key : String) (v : Nat) :
    lookupValue (bindValue env name v) key = if name = key then v else lookupValue env key := by
  by_cases h : name = key
  · simp [lookupValue, bindValue, h]
  · simp [lookupValue, bindValue, h]
    -- filter drops the new name; the previous binding of key is unchanged
    induction env with
    | nil => simp [lookupValue, h]
    | cons e es ih =>
      rcases e with ⟨n, x⟩
      by_cases hn : n = name
      · subst n
        simpa [lookupValue, h] using ih
      · by_cases hk : n = key
        · subst n
          simp [lookupValue, h, hn]
        · simpa [lookupValue, h, hn, hk] using ih

theorem lookup_bind_ne (env : Env) (name key : String) (v : Nat) (h : name ≠ key) :
    lookupValue (bindValue env name v) key = lookupValue env key := by
  simp [lookup_bind_eq, h]

theorem lookup_withBind (s : DenoteState) (name key : String) (v : Nat) :
    lookupValue (withBind s name v).bindings key =
      if name = key then v else lookupValue s.bindings key := by
  rw [bindings_withBind, lookup_bind_eq]

attribute [irreducible] withBind

theorem lookup_init_maturity (m i u : Nat) :
    lookupValue [("market_maturity", m), ("id", i), ("user", u)] "market_maturity" = m := by
  rfl

theorem lookup_init_id (m i u : Nat) :
    lookupValue [("market_maturity", m), ("id", i), ("user", u)] "id" = i := by
  rfl

theorem lookup_init_user (m i u : Nat) :
    lookupValue [("market_maturity", m), ("id", i), ("user", u)] "user" = u := by
  rfl

theorem wordNormalize_small {n : Nat} (h : n < 2 ^ 256) : wordNormalize n = n :=
  ofNat_val_lt h

theorem exec_panic (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (code : Verity.Core.PanicCode) (rest : List Stmt) :
    execStmtList o fs s (.panic code :: rest) = .revert := by
  rfl

theorem boolWord_false : boolWord false = 0 := rfl

theorem boolWord_true : boolWord true = 1 := rfl

theorem readMember_le128 (o : DenoteOracle) (world : Verity.ContractState)
    (field member : String) (keys : List Nat)
    (h : memberWidth midnight.model field member = 128) :
    readMember o midnight.model world field keys member ≤ max128 := by
  have hlt := readMember_lt o midnight.model world field keys member
  rw [h] at hlt
  unfold max128
  omega

theorem wordNormalize_max : wordNormalize max128 = max128 :=
  wordNormalize_small max128_lt_mod

@[simp] theorem wordNormalize_literal_max :
    wordNormalize 340282366920938463463374607431768211455 = max128 := by
  unfold wordNormalize
  rw [ofNat_val_lt (by decide : 340282366920938463463374607431768211455 < 2 ^ 256)]
  rfl

end Midnight.Lemmas

namespace Midnight.Lemmas

open Lean Elab Tactic Meta

elab "expose_cons" : tactic => do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let some (_, lhs, _) := tgt.eq? | do
    throwError "arity {tgt.getAppNumArgs} isEq {tgt.isAppOf ``Eq}"
  let stmts := lhs.getAppArgs.back!
  let w ← whnf stmts
  let w ← if w.isAppOf ``List.cons then pure w else if stmts.isAppOf ``functionBody then reduce stmts else pure w
  unless w.isAppOf ``List.cons do
    throwError "statement list did not reduce to cons"
  let want ← mkEq stmts w
  let hole ← mkFreshExprMVar want
  try
    hole.mvarId!.refl
  catch e =>
    throwError "reduced list is not definitionally equal: {e.toMessageData}"
  let r ← g.rewrite tgt hole false
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)

private def asString : Lean.Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

open Simp in
simproc ↓ reduceLookup (lookupValue (bindValue _ _ _) _) := fun e => do
  let_expr lookupValue b key := e | return .continue
  let_expr bindValue env name value := b | return .continue
  let some ns := asString name | return .continue
  let some ks := asString key | return .continue
  if ns = ks then
    let pr ← mkAppM ``lookup_bind_hit #[env, name, value]
    return .done { expr := value, proof? := some pr }
  else
    let hne ← mkDecideProof (← mkAppM ``Ne #[name, key])
    let pr ← mkAppM ``lookup_bind_ne #[env, name, key, value, hne]
    return .done { expr := ← mkAppM ``lookupValue #[env, key], proof? := some pr }

open Simp in
simproc ↓ strEq (Eq _ _) := fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  let some ls := asString lhs | return .continue
  let some rs := asString rhs | return .continue
  if ls = rs then
    let hp ← mkFreshExprMVar (← mkAppM ``Eq #[lhs, rhs])
    hp.mvarId!.refl
    let pr ← mkAppM ``eq_true #[hp]
    return .done { expr := mkConst ``True, proof? := some pr }
  else
    let hne ← mkDecideProof (← mkAppM ``Ne #[lhs, rhs])
    let pr ← mkAppM ``eq_false #[hne]
    return .done { expr := mkConst ``False, proof? := some pr }

example (m i u c : Nat) :
    lookupValue (bindValue [("market_maturity", m), ("id", i), ("user", u)] "_credit" c) "id" = i := by
  simp only [reduceLookup]
  exact lookup_init_id m i u

/-- Step every leading `let`/`assign` whose expression reduces. Stop at a branch. -/
elab "autos" : tactic => do
  for _ in [0:40] do
    let g0 ← getMainGoal
    let tgt0 ← g0.withContext <| instantiateMVars (← g0.getType)
    let tgt0 := tgt0.consumeMData
    let some (_, lhs0, _) := tgt0.eq? | throwError "autos: not eq"
    let stmts0 := lhs0.getAppArgs.back!
    let head0 ← whnf stmts0
    let head0 ← if head0.isAppOf ``List.cons then pure head0 else if stmts0.isAppOf ``functionBody then reduce stmts0 else pure head0
    unless head0.isAppOf ``List.cons do throwError "autos: empty"
    let ctor0 := (head0.getArg! 1).getAppFn
    unless ctor0.isConstOf ``Compiler.CompilationModel.Stmt.letVar ||
        ctor0.isConstOf ``Compiler.CompilationModel.Stmt.assignVar do
      break
    evalTactic (← `(tactic| expose_cons))
    let g ← getMainGoal
    g.withContext do
      let tgt := (← instantiateMVars (← g.getType)).consumeMData
      let some (_, lhs, _) := tgt.eq? | throwError "autos: not eq"
      let w ← whnf lhs.getAppArgs.back!
      let stmt := w.getArg! 1
      let isLet := stmt.getAppFn.isConstOf ``Compiler.CompilationModel.Stmt.letVar
      let name := stmt.getArg! 0
      let e := stmt.getArg! 1
      let args := lhs.getAppArgs
      let o := args[args.size - 4]!
      let fs := args[args.size - 3]!
      let s := args[args.size - 2]!
      let model := mkConst ``midnight.model
      let (v, hev) ← if e.isAppOfArity ``Compiler.CompilationModel.Expr.structMember2 4 then do
          let field := e.getArg! 0
          let k1 := e.getArg! 1
          let k2 := e.getArg! 2
          let member := e.getArg! 3
          unless k1.isAppOf ``Compiler.CompilationModel.Expr.param &&
              k2.isAppOf ``Compiler.CompilationModel.Expr.param do
            throwError "autos: non-param key"
          let n1 := k1.getArg! 0
          let n2 := k2.getArg! 0
          let flag (p : Lean.Expr) : MetaM Lean.Expr := do
            mkAppM ``Eq #[p, mkConst ``Bool.true]
          let present ← mkAppM ``And #[
            ← flag (← mkAppM ``Option.isSome #[← mkAppM ``findFieldWithResolvedSlot #[fs, field]]),
            ← flag (← mkAppM ``Option.isSome #[← mkAppM ``findMember #[model, field, member]])]
          let hp ← mkDecideProof present
          let hev ← mkAppM ``evalExpr_structMember2_param #[o, model, s, field, n1, n2, member, hp]
          let ty ← inferType hev
          let some (_, _, rhs) := ty.eq? | throwError "autos: member eq"
          let some (_, v) := rhs.app2? ``Option.some | throwError "autos: member some"
          pure (v, hev)
        else do
          let rec compact : Nat → Lean.Expr → MetaM Lean.Expr
            | 0, _ => throwError "autos: expression too deep"
            | fuel + 1, e => do
            let bin (ctor : Name) (op : Name) : MetaM Lean.Expr := do
              let a ← compact fuel (e.getArg! 0)
              let b ← compact fuel (e.getArg! 1)
              let ua ← mkAppM ``Verity.Core.Uint256.ofNat #[a]
              let ub ← mkAppM ``Verity.Core.Uint256.ofNat #[b]
              mkProjection (← mkAppM op #[ua, ub]) `val
            let cmp (ctor : Name) (swap : Bool) : MetaM Lean.Expr := do
              let a ← compact fuel (e.getArg! 0)
              let b ← compact fuel (e.getArg! 1)
              let (l, r) := if swap then (b, a) else (a, b)
              let rel ← if ctor == ``Compiler.CompilationModel.Expr.eq then
                mkAppM ``Eq #[l, r]
              else
                mkAppM ``LT.lt #[l, r]
              let dec ← synthInstance (mkApp (mkConst ``Decidable) rel)
              mkAppM ``boolWord #[← mkAppOptM ``decide #[some rel, some dec]]
            if e.isAppOf ``Compiler.CompilationModel.Expr.literal then
              mkAppM ``wordNormalize #[e.getArg! 0]
            else if e.isAppOf ``Compiler.CompilationModel.Expr.localVar ||
                e.isAppOf ``Compiler.CompilationModel.Expr.param then
              mkAppM ``lookupValue #[← mkAppM ``Compiler.CompilationModel.Denote.DenoteState.bindings #[s], e.getArg! 0]
            else if e.isAppOf ``Compiler.CompilationModel.Expr.blockTimestamp then
              let w ← mkAppM ``Compiler.CompilationModel.Denote.DenoteState.world #[s]
              let ts ← mkAppM ``Verity.ContractState.blockTimestamp #[w]
              mkAppM ``Verity.Core.Uint256.val #[ts]
            else if e.isAppOf ``Compiler.CompilationModel.Expr.lt then cmp ``Compiler.CompilationModel.Expr.lt false
            else if e.isAppOf ``Compiler.CompilationModel.Expr.gt then cmp ``Compiler.CompilationModel.Expr.gt true
            else if e.isAppOf ``Compiler.CompilationModel.Expr.eq then cmp ``Compiler.CompilationModel.Expr.eq false
            else if e.isAppOf ``Compiler.CompilationModel.Expr.sub then bin `sub ``Verity.Core.Uint256.sub
            else if e.isAppOf ``Compiler.CompilationModel.Expr.add then bin `add ``Verity.Core.Uint256.add
            else if e.isAppOf ``Compiler.CompilationModel.Expr.mul then bin `mul ``Verity.Core.Uint256.mul
            else if e.isAppOf ``Compiler.CompilationModel.Expr.div then bin `div ``Verity.Core.Uint256.div
            else if e.isAppOf ``Compiler.CompilationModel.Expr.bitAnd then bin `and ``Verity.Core.Uint256.and
            else if e.isAppOf ``Compiler.CompilationModel.Expr.bitXor then bin `xor ``Verity.Core.Uint256.xor
            else if e.isAppOfArity ``Compiler.CompilationModel.Expr.structMember 3 then
              let field := e.getArg! 0
              let key := e.getArg! 1
              let member := e.getArg! 2
              unless key.isAppOf ``Compiler.CompilationModel.Expr.param do throwError "autos: member key"
              let n := key.getArg! 0
              let flag (p : Lean.Expr) := mkAppM ``Eq #[p, mkConst ``Bool.true]
              let present ← mkAppM ``And #[
                ← flag (← mkAppM ``Option.isSome #[← mkAppM ``findFieldWithResolvedSlot #[fs, field]]),
                ← flag (← mkAppM ``Option.isSome #[← mkAppM ``findMember #[model, field, member]])]
              let hp ← mkDecideProof present
              let hev ← mkAppM ``evalExpr_structMember_param #[o, model, s, field, n, member, hp]
              let ty ← inferType hev
              let some (_, _, rhs) := ty.eq? | throwError "member"
              let some (_, v) := rhs.app2? ``Option.some | throwError "member some"
              pure v
            else
              throwError "autos: unsupported {(e.getAppFn)}"
          let v ← compact 8 e
          let ev ← mkAppM ``Compiler.CompilationModel.Denote.evalExpr #[o, fs, s, e]
          let someV ← mkAppM ``Option.some #[v]
          let hev ← mkFreshExprMVar (← mkEq ev someV)
          try
            hev.mvarId!.refl
          catch err =>
            throwError "autos: compact eval is not definitional: {err.toMessageData}"
          pure (v, hev)
      let lem := if isLet then ``exec_let else ``exec_assign
      let rwlem ← mkAppM lem #[o, fs, s, name, e, v, w.getArg! 2, hev]
      let r ← g.rewrite (← g.getType) rwlem false
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      replaceMainGoal (g' :: r.mvarIds)

elab "split_ite" : tactic => do
  evalTactic (← `(tactic| expose_cons))
  let g ← getMainGoal
  g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, _) := tgt.eq? | throwError "split_ite: not eq"
    let w ← whnf lhs.getAppArgs.back!
    let stmt := w.getArg! 1
    unless stmt.isAppOf ``Compiler.CompilationModel.Stmt.ite do
      throwError "split_ite: not ite"
    let cond := stmt.getArg! 0
    unless cond.isAppOf ``Compiler.CompilationModel.Expr.localVar do
      throwError "split_ite: condition is {cond.getAppFn}"
    let args := lhs.getAppArgs
    let o := args[args.size - 4]!
    let fs := args[args.size - 3]!
    let s := args[args.size - 2]!
    let b ← mkAppM ``Compiler.CompilationModel.Denote.DenoteState.bindings #[s]
    let v ← mkAppM ``lookupValue #[b, cond.getArg! 0]
    let ev ← mkAppM ``Compiler.CompilationModel.Denote.evalExpr #[o, fs, s, cond]
    let hev ← mkFreshExprMVar (← mkEq ev (← mkAppM ``Option.some #[v]))
    hev.mvarId!.refl
    let rest := w.getArg! 2
    let yes := stmt.getArg! 1
    let no := stmt.getArg! 2
    let rwlem ← mkAppM ``exec_ite_some #[o, fs, s, cond, yes, no, rest, v, hev]
    let r ← g.rewrite (← g.getType) rwlem false
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    let p ← mkAppM ``Eq #[v, mkNatLit 0]
    let (g1, g2) ← g'.byCases p `h
    let applyIf (sub : ByCasesSubgoal) (lem : Name) : TacticM Unit := do
      setGoals [sub.mvarId]
      let stx ← sub.mvarId.withContext <| Lean.PrettyPrinter.delab (.fvar sub.fvarId)
      let tac ← if lem == ``if_pos then
        `(tactic| rw [if_pos $stx])
      else
        `(tactic| rw [if_neg $stx])
      evalTactic tac
    applyIf g1 ``if_pos
    let goals1 ← getGoals
    applyIf g2 ``if_neg
    let goals2 ← getGoals
    setGoals (goals1 ++ goals2)

elab "take_branch" hyp:ident pos:num : tactic => do
  evalTactic (← `(tactic| expose_cons))
  let g ← getMainGoal
  g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, _) := tgt.eq? | throwError "take_branch: not eq"
    let w ← whnf lhs.getAppArgs.back!
    let stmt := w.getArg! 1
    unless stmt.isAppOf ``Compiler.CompilationModel.Stmt.ite do throwError "take_branch: not ite"
    let cond := stmt.getArg! 0
    unless cond.isAppOf ``Compiler.CompilationModel.Expr.localVar do
      throwError "take_branch: {cond.getAppFn}"
    let args := lhs.getAppArgs
    let o := args[args.size - 4]!
    let fs := args[args.size - 3]!
    let s := args[args.size - 2]!
    let b ← mkAppM ``Compiler.CompilationModel.Denote.DenoteState.bindings #[s]
    let v ← mkAppM ``lookupValue #[b, cond.getArg! 0]
    let ev ← mkAppM ``Compiler.CompilationModel.Denote.evalExpr #[o, fs, s, cond]
    let hev ← mkFreshExprMVar (← mkEq ev (← mkAppM ``Option.some #[v]))
    hev.mvarId!.refl
    let rwlem ← mkAppM ``exec_ite_some #[o, fs, s, cond, stmt.getArg! 1, stmt.getArg! 2,
      w.getArg! 2, v, hev]
    let r ← g.rewrite (← g.getType) rwlem false
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    let fvar ← getLocalDeclFromUserName hyp.getId
    let dec ← synthInstance (mkApp (mkConst ``Decidable) (← inferType (.fvar fvar.fvarId)))
    let lem := if pos.getNat = 1 then ``if_pos else ``if_neg
    let stx ← Lean.PrettyPrinter.delab (.fvar fvar.fvarId)
    setGoals [g']
    if pos.getNat = 1 then
      evalTactic (← `(tactic| rw [if_pos $stx]))
    else
      evalTactic (← `(tactic| rw [if_neg $stx]))

elab "show_cond" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, _) := tgt.eq? | throwError "show_cond"
    let list := lhs.getAppArgs.back!
    let list ← whnf list
    let cond := (list.getArg! 1).getArg! 0
    let args := lhs.getAppArgs
    let s := args[args.size - 2]!
    let b ← mkAppM ``Compiler.CompilationModel.Denote.DenoteState.bindings #[s]
    let v ← mkAppM ``lookupValue #[b, cond.getArg! 0]
    let stx ← Lean.PrettyPrinter.delab v
    evalTactic (← `(tactic| have hcond : $stx = 0 ∨ $stx = 1 := by
      rw [← hs]
      simp only [lookup_withBind, world_withBind, strEq, if_true, if_false,
        wordNormalize_literal_max, lookup_init_id, lookup_init_user, lookup_init_maturity]))

elab "peek" : tactic => do
  let g ← getMainGoal
  let tgt := (← g.withContext <| instantiateMVars (← g.getType)).consumeMData
  let some (_, lhs, _) := tgt.eq? | throwError "peek: not eq"
  let list := lhs.getAppArgs.back!
  let left := list.getArg! 4
  throwError "left fn {left.getAppFn}"

elab "drive" : tactic => do
  for _ in [0:30] do
    evalTactic (← `(tactic| all_goals autos))
    let before ← getGoals
    evalTactic (← `(tactic| all_goals (try split_ite)))
    let after ← getGoals
    if after == before then
      break
    if after.length > 64 then
      throwError "drive: {after.length} goals"

syntax "step_let " term " := " tacticSeq : tactic
syntax "step_assign " term " := " tacticSeq : tactic

macro_rules
| `(tactic| step_let $v := $prf) =>
  `(tactic| (expose_cons <;> rw [exec_let (v := $v) (h := by $prf)]))
| `(tactic| step_assign $v := $prf) =>
  `(tactic| (expose_cons <;> rw [exec_assign (v := $v) (h := by $prf)]))

end Midnight.Lemmas
