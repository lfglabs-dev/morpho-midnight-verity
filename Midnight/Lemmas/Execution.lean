import Midnight.Lemmas.Arithmetic

/-!
Step 1 of the proof: what a successful call computes (`successful_call`).

The function ends with `return (postSlashCredit - fee, postSlashPendingFee - fee, fee)`,
with checked subtractions. If the call succeeds they did not underflow, so
`newCredit + fee = postSlashCredit` and `newPendingFee + fee = postSlashPendingFee`.
It remains to show that the imported code computes `postSlashCredit` as the
formula of `Arithmetic.lean`, and `postSlashPendingFee ≤ oldPendingFee`.

The body is cut after each Solidity local the proof follows, and each part is
executed by its own lemma:

| part          | ends with                                                            | lemma            |
| ------------- | -------------------------------------------------------------------- | ---------------- |
| `creditCode`  | `uint256 postSlashCredit = _lastLossFactor < max ? _credit.mulDivDown(..) : 0;` | `credit_exact` |
| `pendingCode` | `uint256 postSlashPendingFee = _credit > 0 ? _pendingFee - _pendingFee.mulDivUp(..) : 0;` | `pending_bound` |
| `feeCode`     | `uint128 fee = _lastAccrual < market.maturity ? uint128(..mulDivDown(..)) : 0;` | (not needed) |
| `returnCode`  | `return (uint128(postSlashCredit) - fee, uint128(postSlashPendingFee) - fee, fee);` | `return_values` |

`fee` itself is never computed: any value that lets the subtractions succeed will do.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core Midnight.Spec
namespace Midnight.Lemmas

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-! ## Storage reads

The model reads `position[id][user].member` and `marketState[id].member` with
`readMember`, the function behind the generated `midnight.position.credit`, ... -/

theorem read_position (o : DenoteOracle) (s : DenoteState) (member : String)
    (h : (findMember midnight.model "position" member).isSome := by decide) :
    evalExpr o midnight.model.fields s (.structMember2 "position" (.param "id") (.param "user") member) =
      some (readMember o midnight.model s.world "position"
        [lookupValue s.bindings "id", lookupValue s.bindings "user"] member) :=
  evalExpr_structMember2_param o midnight.model s "position" "id" "user" member ⟨by decide, h⟩

theorem read_market (o : DenoteOracle) (s : DenoteState) (member : String)
    (h : (findMember midnight.model "marketState" member).isSome := by decide) :
    evalExpr o midnight.model.fields s (.structMember "marketState" (.param "id") member) =
      some (readMember o midnight.model s.world "marketState" [lookupValue s.bindings "id"] member) :=
  evalExpr_structMember_param o midnight.model s "marketState" "id" member ⟨by decide, h⟩

theorem uint128_le (x : Verity.Core.UIntN 128) : x.val ≤ max128 := by
  have := x.isLt
  unfold max128
  omega

/-! ## The body, statement by statement -/

def body := functionBody midnight.model "updatePositionView"

def creditCode := (splitAfter "postSlashCredit" body).1
def pendingCode := (splitAfter "postSlashPendingFee" (splitAfter "postSlashCredit" body).2).1
def feeCode := (splitAfter "fee" (splitAfter "postSlashPendingFee" body).2).1
def returnCode := (splitAfter "fee" body).2

theorem body_parts : body = creditCode ++ (pendingCode ++ (feeCode ++ returnCode)) := by rfl

/-- Unfold a part of the body and execute it symbolically at `h`. -/
syntax "run_body " "[" Lean.Parser.Tactic.simpArg,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| run_body [$args,*] $[$loc]?) =>
    `(tactic| simp [body, functionBody, functionBody.go, splitAfter, midnight.model,
        execStmtList, execStmt, evalExpr, lookup_bind_same, lookup_bind_other, boolWord,
        wordNormalize, $args,*] $[$loc]?)

/-- The two checked subtractions of the `return`. -/
theorem return_values (o : DenoteOracle) (s final : DenoteState) (q r : Nat)
    (hq : q ≤ max128) (hr : r ≤ max128)
    (hqs : lookupValue s.bindings "postSlashCredit" = q)
    (hrs : lookupValue s.bindings "postSlashPendingFee" = r)
    (h : execStmtList o midnight.model.fields s returnCode = .stop final) :
    ∃ nc np fee, final.observedReturnWords = some [nc, np, fee] ∧
      nc + fee = q ∧ np + fee = r := by
  generalize hf : lookupValue s.bindings "fee" = f
  have hmax : 340282366920938463463374607431768211455 % Uint256.modulus = 340282366920938463463374607431768211455 := by decide
  have hqcast := mask_eq hq
  have hrcast := mask_eq hr
  change (Uint256.and (Uint256.ofNat q) (Uint256.ofNat 340282366920938463463374607431768211455)).val = q at hqcast
  change (Uint256.and (Uint256.ofNat r) (Uint256.ofNat 340282366920938463463374607431768211455)).val = r at hrcast
  by_cases hfq : f ≤ q
  · have hfmod := word_of_small (le_trans hfq hq)
    change f % Uint256.modulus = f at hfmod
    have hqsub := sub_word (lt_of_le_of_lt hq max128_lt) hfq
    by_cases hfr : f ≤ r
    · have hrsub := sub_word (lt_of_le_of_lt hr max128_lt) hfr
      have hnq := word_of_small (le_trans (Nat.sub_le q f) hq)
      have hnr := word_of_small (le_trans (Nat.sub_le r f) hr)
      change (q - f) % Uint256.modulus = q - f at hnq
      change (r - f) % Uint256.modulus = r - f at hnr
      run_body [returnCode, evalExprList, hqs, hrs, hqcast, hrcast, hf,
        Nat.not_lt.mpr hfq, Nat.not_lt.mpr hfr, hqsub, hrsub, hmax, hfmod, hnq, hnr] at h
      refine ⟨q-f, r-f, f, ?_, Nat.sub_add_cancel hfq, Nat.sub_add_cancel hfr⟩
      rw [← h]
    · run_body [returnCode, hqs, hrs, hf, hqcast, hrcast,
        Nat.not_lt.mpr hfq, Nat.lt_of_not_ge hfr, hqsub, hmax] at h
  · run_body [returnCode, hqs, hf, hqcast, Nat.lt_of_not_ge hfq, hmax] at h

/-- The `_credit > 0` branch of `postSlashPendingFee`, i.e.
`_pendingFee - _pendingFee.mulDivUp(_credit - postSlashCredit, _credit)`.
Inside it, `_verity_slice_tmp_20` is the `mulDivUp` result and
`_verity_slice_tmp_22` the value of the conditional expression. -/
def pendingBranch : List Stmt :=
  match pendingCode.drop 3 with | (Stmt.ite _ yes _) :: _ => yes | _ => []
def pendingPrefix := pendingBranch.take (pendingBranch.length - 2)
def pendingTail := pendingBranch.drop (pendingBranch.length - 2)

theorem pending_branch_bound (o : DenoteOracle) (s next : DenoteState) (p : Nat)
    (hp : p ≤ max128) (hps : lookupValue s.bindings "_pendingFee" = p)
    (h : execStmtList o midnight.model.fields s pendingBranch = .continue next) :
    lookupValue next.bindings "_verity_slice_tmp_22" ≤ p := by
  have parts : pendingBranch = pendingPrefix ++ pendingTail := by rfl
  rw [parts] at h
  obtain ⟨t, ht, h⟩ := split_prefix_continue _ _ _ _ _ _ h
  have frame := list_frame o midnight.model.fields s pendingPrefix ["_pendingFee"] (by decide)
  rw [ht] at frame
  have hpt : lookupValue t.bindings "_pendingFee" = p :=
    (frame.2 "_pendingFee" (by simp)).trans hps
  generalize hz : lookupValue t.bindings "_verity_slice_tmp_20" = z
  by_cases hzle : z ≤ p
  · have hsub := sub_word (lt_of_le_of_lt hp max128_lt) hzle
    run_body [pendingTail, pendingBranch, pendingCode, hpt, hz,
      Nat.not_lt.mpr hzle, hsub] at h
    rw [← h]
    simp
  · run_body [pendingTail, pendingBranch, pendingCode, hpt, hz, Nat.lt_of_not_ge hzle] at h

/-- `postSlashPendingFee <= _pendingFee`. -/
theorem pending_bound (o : DenoteOracle) (s next : DenoteState) (c p : Nat)
    (hp : p ≤ max128)
    (hc : lookupValue s.bindings "_credit" = c)
    (hread : evalExpr o midnight.model.fields s
      (.structMember2 "position" (.param "id") (.param "user") "pendingFee") = some p)
    (h : execStmtList o midnight.model.fields s pendingCode = .continue next) :
    lookupValue next.bindings "postSlashPendingFee" ≤ p := by
  have parts : pendingCode =
    [.letVar "_pendingFee" (.structMember2 "position" (.param "id") (.param "user") "pendingFee"),
     .letVar "_verity_slice_tmp_10" (.gt (.localVar "_credit") (.literal 0)),
     .letVar "_verity_slice_tmp_22" (.literal 0),
     .ite (.localVar "_verity_slice_tmp_10") pendingBranch [.assignVar "_verity_slice_tmp_22" (.literal 0)]] ++
    [.letVar "postSlashPendingFee" (.localVar "_verity_slice_tmp_22")] := by rfl
  rw [parts] at h
  obtain ⟨t, ht, h⟩ := split_prefix_continue _ _ _ _ _ _ h
  simp [execStmt, evalExpr] at h
  rw [exec_let_cons, hread] at ht
  simp only at ht
  simp only [exec_let_cons] at ht
  rw [← h]
  simp only [lookup_bind_same]
  by_cases hpos : 0 < c
  · simp [execStmt, evalExpr, lookup_bind_same, lookup_bind_other, hc, boolWord,
      wordNormalize, hpos] at ht
    exact pending_branch_bound o _ t p hp (by simp) ht
  · simp [execStmt, evalExpr, lookup_bind_same, lookup_bind_other, hc, boolWord,
      wordNormalize, hpos] at ht
    rw [← ht]
    simp

/-- The code computes `postSlashCredit` as the formula of `Arithmetic.lean`: no
overflow, and no division by zero. -/
theorem credit_exact (o : DenoteOracle) (s next : DenoteState) (c ell g : Nat)
    (hc : c ≤ max128) (hl : ell ≤ max128) (hg : g ≤ max128)
    (hcRead : readMember o midnight.model s.world "position"
      [lookupValue s.bindings "id", lookupValue s.bindings "user"] "credit" = c)
    (hlRead : readMember o midnight.model s.world "position"
      [lookupValue s.bindings "id", lookupValue s.bindings "user"] "lastLossFactor" = ell)
    (hgRead : readMember o midnight.model s.world "marketState"
      [lookupValue s.bindings "id"] "lossFactor" = g)
    (h : execStmtList o midnight.model.fields s creditCode = .continue next) :
    lookupValue next.bindings "_credit" = c ∧
    lookupValue next.bindings "postSlashCredit" = postSlashCredit c ell g := by
  have hmax : wordNormalize 340282366920938463463374607431768211455 = max128 := by decide
  have hzero : wordNormalize 0 = 0 := by decide
  have hA : max128-g ≤ max128 := Nat.sub_le _ _
  have hB : max128-ell ≤ max128 := Nat.sub_le _ _
  have hsubA := sub_word max128_lt hg
  have hsubB := sub_word max128_lt hl
  have hprod := mul_word128 hc hA
  have hprodlt : c * (max128-g) < Uint256.modulus :=
    lt_of_le_of_lt (Nat.mul_le_mul hc hA) (by decide)
  have hdivB := div_word hprodlt (lt_of_le_of_lt hB max128_lt)
  have hdivC := div_word hprodlt (lt_of_le_of_lt hc max128_lt)
  conv at h =>
    lhs
    arg 4
    simp (config := { decide := true }) only [creditCode, body, functionBody, functionBody.go,
      splitAfter, midnight.model, ↓reduceIte]
  simp only [execStmtList, execStmt, read_position o _ "credit", read_position o _ "lastLossFactor",
    read_market o _ "lossFactor"] at h
  simp [evalExpr, lookup_bind_same, lookup_bind_other, boolWord,
    hcRead, hlRead, hgRead, hmax, hzero, hsubA] at h
  by_cases hpos : ell < max128
  · have hBne : max128-ell ≠ 0 := by omega
    by_cases hc0 : c = 0
    · simp [hpos, hc0, Nat.not_lt.mpr hg, Nat.not_lt.mpr hl, hBne,
        lookup_bind_same, lookup_bind_other, hsubB] at h
      rw [← h]
      simp [postSlashCredit, hc0, hpos]
    · have hcancel : c * (max128-g) / c = max128-g := by
        rw [Nat.mul_comm c, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)]
      simp [hpos, hc0, Nat.not_lt.mpr hg, Nat.not_lt.mpr hl, hBne,
        lookup_bind_same, lookup_bind_other, hsubB, hprod, hdivB, hdivC, hcancel] at h
      rw [← h]
      simp [postSlashCredit, hpos]
  · simp [hpos] at h
    rw [← h]
    simp [postSlashCredit, hpos]

def initial (w : Verity.ContractState) (maturity : Verity.Core.Uint256)
    (id : Verity.Core.BytesN 32) (user : Verity.Core.Address) : DenoteState :=
  { world := w, bindings := [("market_maturity", maturity.val), ("id", id.val), ("user", user.val)] }

/-- The expressions returned by the final `return`. -/
def returnArgs : List Expr :=
  match body.getLast? with | some (.returnValues args) => args | _ => []

/-- A successful call runs the whole body and returns three words. -/
theorem successful_stop (o : DenoteOracle) (w : Verity.ContractState)
    (maturity : Verity.Core.Uint256) (id : Verity.Core.BytesN 32) (user : Verity.Core.Address)
    (nc np fee : Verity.Core.UIntN 128)
    (h : midnight.updatePositionView o w maturity id user = some (nc, np, fee)) :
    ∃ final r0 r1 r2, execStmtList o midnight.model.fields (initial w maturity id user) body = .stop final ∧
      final.observedReturnWords = some [r0, r1, r2] ∧
      nc = .ofNat 128 r0 ∧ np = .ofNat 128 r1 ∧ fee = .ofNat 128 r2 := by
  unfold midnight.updatePositionView at h
  split at h
  · rename_i r0 r1 r2 hrun
    simp only [Option.some.injEq, Prod.mk.injEq, ofWord_uintN] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [runFunction, toWord_uint256, toWord_bytes32, toWord_address] at hrun
    have parts : body = body.dropLast ++ [.returnValues returnArgs] := by rfl
    have ht := ends_return o midnight.model.fields (initial w maturity id user)
      body.dropLast returnArgs (by decide)
    rw [← parts] at ht
    rcases ht with hr | ⟨final, hf⟩
    · simp only [initial, body] at hr
      simp only [hr] at hrun
      contradiction
    · refine ⟨final, r0, r1, r2, hf, ?_, rfl, rfl, rfl⟩
      simp only [initial, body] at hf
      simpa only [hf] using hrun
  · contradiction

/-- A successful call returns `newCredit + fee = postSlashCredit` and
`newPendingFee + fee ≤ oldPendingFee`. -/
theorem successful_call (o : DenoteOracle) (w : Verity.ContractState)
    (maturity : Verity.Core.Uint256) (id : Verity.Core.BytesN 32) (user : Verity.Core.Address)
    (nc np fee : Verity.Core.UIntN 128)
    (horder : (Spec.old o w id user).lastLossFactor ≤ (Spec.old o w id user).lossFactor)
    (h : midnight.updatePositionView o w maturity id user = some (nc, np, fee)) :
    nc.val + fee.val = postSlashCredit (Spec.old o w id user).credit.val
      (Spec.old o w id user).lastLossFactor.val (Spec.old o w id user).lossFactor.val ∧
    np.val + fee.val ≤ (Spec.old o w id user).pendingFee.val := by
  obtain ⟨final, r0, r1, r2, hfull, hret, rfl, rfl, rfl⟩ := successful_stop o w maturity id user _ _ _ h
  rw [body_parts] at hfull
  obtain ⟨s1, h1, hrest⟩ := split_prefix o midnight.model.fields _ final creditCode _ (by decide) hfull
  obtain ⟨s2, h2, hrest⟩ := split_prefix o midnight.model.fields s1 final pendingCode _ (by decide) hrest
  obtain ⟨s3, h3, h4⟩ := split_prefix o midnight.model.fields s2 final feeCode _ (by decide) hrest
  let i := Spec.old o w id user
  have hc := uint128_le i.credit
  have hp := uint128_le i.pendingFee
  have hl := uint128_le i.lastLossFactor
  have hg := uint128_le i.lossFactor
  have hs := credit_exact o (initial w maturity id user) s1
    i.credit.val i.lastLossFactor.val i.lossFactor.val hc hl hg
    (by simp [initial, lookupValue, i, Spec.old])
    (by simp [initial, lookupValue, i, Spec.old])
    (by simp [initial, lookupValue, i, Spec.old]) h1
  have frame1 := list_frame o midnight.model.fields (initial w maturity id user)
    creditCode ["id", "user"] (by decide)
  rw [h1] at frame1
  have hid : lookupValue s1.bindings "id" = id.val := by
    simpa [initial, lookupValue] using frame1.2 "id" (by simp)
  have huser : lookupValue s1.bindings "user" = user.val := by
    simpa [initial, lookupValue] using frame1.2 "user" (by simp)
  have hpRead : evalExpr o midnight.model.fields s1
      (.structMember2 "position" (.param "id") (.param "user") "pendingFee") = some i.pendingFee.val := by
    rw [read_position _ _ "pendingFee", hid, huser, frame1.1]
    simp [initial, i, Spec.old]
  have hr := pending_bound o s1 s2 i.credit.val i.pendingFee.val hp hs.1 hpRead h2
  have frame2 := list_frame o midnight.model.fields s1 pendingCode ["postSlashCredit"] (by decide)
  rw [h2] at frame2
  have frame3 := list_frame o midnight.model.fields s2 feeCode ["postSlashCredit", "postSlashPendingFee"] (by decide)
  rw [h3] at frame3
  have hq3 : lookupValue s3.bindings "postSlashCredit" =
      postSlashCredit i.credit.val i.lastLossFactor.val i.lossFactor.val := by
    rw [frame3.2 "postSlashCredit" (by simp), frame2.2 "postSlashCredit" (by simp), hs.2]
  have hr3 : lookupValue s3.bindings "postSlashPendingFee" ≤ i.pendingFee.val := by
    rw [frame3.2 "postSlashPendingFee" (by simp)]
    exact hr
  have hpostSlashCredit : postSlashCredit i.credit.val i.lastLossFactor.val i.lossFactor.val ≤ max128 :=
    le_trans (postSlashCredit_le horder) hc
  obtain ⟨nc', np', fee', hret', hq, hr'⟩ := return_values o s3 final
    (postSlashCredit i.credit.val i.lastLossFactor.val i.lossFactor.val)
    (lookupValue s3.bindings "postSlashPendingFee") hpostSlashCredit (le_trans hr3 hp) hq3 rfl h4
  have heq : r0 = nc' ∧ r1 = np' ∧ r2 = fee' := by simpa [hret] using hret'
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have small : ∀ n, n ≤ max128 → (Verity.Core.UIntN.ofNat 128 n).val = n := fun n hn =>
    Nat.mod_eq_of_lt (by unfold max128 at hn; omega)
  rw [small r0 (by omega), small r1 (by omega), small r2 (by omega)]
  exact ⟨hq, le_trans (le_of_eq hr') hr3⟩

end Midnight.Lemmas
