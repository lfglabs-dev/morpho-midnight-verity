import Midnight.Lemmas.Exec

/-!
Identify the imported `updatePositionView` execution with `viewResult?`.
-/

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core
open Midnight.Lemmas

namespace Midnight.Lemmas

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

theorem lookup_wb_ne {st : DenoteState} {name key : String} {v : Nat} (h : name ≠ key) :
    lookupValue (withBind st name v).bindings key = lookupValue st.bindings key := by
  simpa [withBind] using lookupValue_bind_ne h

theorem lookup_wb_eq (st : DenoteState) (name : String) (v : Nat) :
    lookupValue (withBind st name v).bindings name = v := by
  simpa [withBind] using lookupValue_bind_eq st.bindings name v

theorem look {st : DenoteState} {name key : String} {v old : Nat}
    (h : lookupValue st.bindings key = old) (hne : name ≠ key := by decide) :
    lookupValue (withBind st name v).bindings key = old := by
  rw [lookup_wb_ne hne, h]

def start (world : Verity.ContractState) (maturity idv userv : Nat) : DenoteState :=
  { world, bindings := argEnv maturity idv userv }

theorem position_credit_present :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome = true ∧
      (findMember midnight.model "position" "credit").isSome = true := by
  decide

theorem position_pending_present :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome = true ∧
      (findMember midnight.model "position" "pendingFee").isSome = true := by
  decide

theorem position_llf_present :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome = true ∧
      (findMember midnight.model "position" "lastLossFactor").isSome = true := by
  decide

theorem position_accrual_present :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome = true ∧
      (findMember midnight.model "position" "lastAccrual").isSome = true := by
  decide

theorem market_loss_present :
    (findFieldWithResolvedSlot midnight.model.fields "marketState").isSome = true ∧
      (findMember midnight.model "marketState" "lossFactor").isSome = true := by
  decide

theorem eval_mem2 (oracle : DenoteOracle) (st : DenoteState) (member : String)
    (id : BytesN 32) (user : Address)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val)
    (h : (findFieldWithResolvedSlot midnight.model.fields "position").isSome = true ∧
      (findMember midnight.model "position" member).isSome = true) :
    evalExpr oracle midnight.model.fields st
        (.structMember2 "position" (.param "id") (.param "user") member) =
      some (readMember oracle midnight.model st.world "position" [id.val, user.val] member) := by
  rw [evalExpr_structMember2_param (h := by
    refine ⟨?_, ?_⟩
    · simpa using h.1
    · simpa using h.2)]
  simp [hid, huser]

theorem eval_credit (oracle : DenoteOracle) (st : DenoteState) (id : BytesN 32) (user : Address)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val) :
    evalExpr oracle midnight.model.fields st
        (.structMember2 "position" (.param "id") (.param "user") "credit") =
      some (midnight.position.credit oracle st.world id user).val := by
  rw [eval_mem2 oracle st "credit" id user hid huser position_credit_present]
  simp [midnight.position.credit_val]

theorem eval_pending (oracle : DenoteOracle) (st : DenoteState) (id : BytesN 32) (user : Address)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val) :
    evalExpr oracle midnight.model.fields st
        (.structMember2 "position" (.param "id") (.param "user") "pendingFee") =
      some (midnight.position.pendingFee oracle st.world id user).val := by
  rw [eval_mem2 oracle st "pendingFee" id user hid huser position_pending_present]
  simp [midnight.position.pendingFee_val]

theorem eval_llf (oracle : DenoteOracle) (st : DenoteState) (id : BytesN 32) (user : Address)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val) :
    evalExpr oracle midnight.model.fields st
        (.structMember2 "position" (.param "id") (.param "user") "lastLossFactor") =
      some (midnight.position.lastLossFactor oracle st.world id user).val := by
  rw [eval_mem2 oracle st "lastLossFactor" id user hid huser position_llf_present]
  simp [midnight.position.lastLossFactor_val]

theorem eval_accrual (oracle : DenoteOracle) (st : DenoteState) (id : BytesN 32) (user : Address)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val) :
    evalExpr oracle midnight.model.fields st
        (.structMember2 "position" (.param "id") (.param "user") "lastAccrual") =
      some (midnight.position.lastAccrual oracle st.world id user).val := by
  rw [eval_mem2 oracle st "lastAccrual" id user hid huser position_accrual_present]
  simp [midnight.position.lastAccrual_val]

theorem eval_loss (oracle : DenoteOracle) (st : DenoteState) (id : BytesN 32)
    (hid : lookupValue st.bindings "id" = id.val) :
    evalExpr oracle midnight.model.fields st
        (.structMember "marketState" (.param "id") "lossFactor") =
      some (midnight.marketState.lossFactor oracle st.world id).val := by
  rw [evalExpr_structMember_param (h := by
    refine ⟨?_, ?_⟩
    · simpa using market_loss_present.1
    · simpa using market_loss_present.2)]
  simp [hid, midnight.marketState.lossFactor_val]

theorem xor_lt_MOD {a b : Nat} (ha : a < MOD) (hb : b < MOD) : a ^^^ b < MOD := by
  have ha' : a < 2 ^ 256 := by simpa [MOD] using ha
  have hb' : b < 2 ^ 256 := by simpa [MOD] using hb
  have hmod : a ^^^ b = (a ^^^ b) % 2 ^ 256 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < 256
    · simp [hi]
    · have hpow : 2 ^ 256 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)
      have hbit : (a ^^^ b).testBit i = false := by
        rw [Nat.testBit_xor]
        simp [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha' hpow),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb' hpow)]
      simp [hi, hbit]
  have hlt : (a ^^^ b) % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by decide)
  have : a ^^^ b < 2 ^ 256 := by rwa [← hmod] at hlt
  simpa [MOD] using this

theorem eval_xor {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (haE : evalExpr oracle midnight.model.fields st a = some va)
    (hbE : evalExpr oracle midnight.model.fields st b = some vb)
    (ha : va < MOD) (hb : vb < MOD) :
    evalExpr oracle midnight.model.fields st (.bitXor a b) = some (va ^^^ vb) := by
  rw [evalExpr_bitXor_arm, haE, hbE]
  simp only [bind, Option.bind, pure]
  have hva' : (Uint256.ofNat va).val = va := uint_val ha
  have hvb' : (Uint256.ofNat vb).val = vb := uint_val hb
  simp only [Option.some.injEq, Uint256.xor, hva', hvb']
  exact uint_val (xor_lt_MOD ha hb)

theorem eval_and {oracle : DenoteOracle} {st : DenoteState} {a b : Expr} {va vb : Nat}
    (haE : evalExpr oracle midnight.model.fields st a = some va)
    (hbE : evalExpr oracle midnight.model.fields st b = some vb)
    (ha : va < MOD) (hb : vb < MOD) :
    evalExpr oracle midnight.model.fields st (.bitAnd a b) = some (va &&& vb) := by
  rw [evalExpr_bitAnd_arm, haE, hbE]
  simp only [bind, Option.bind, pure]
  have hva' : (Uint256.ofNat va).val = va := uint_val ha
  have hvb' : (Uint256.ofNat vb).val = vb := uint_val hb
  have hland : va &&& vb < MOD := Nat.lt_of_le_of_lt (Nat.and_le_left (n := va) (m := vb)) ha
  simp only [Option.some.injEq, Uint256.and, hva', hvb']
  exact uint_val hland

theorem eval_narrow_local {oracle : DenoteOracle} {st : DenoteState} {name : String} {n : Nat}
    (hn : lookupValue st.bindings name = n) (hlt : n < MOD) :
    evalExpr oracle midnight.model.fields st (.bitAnd (.localVar name) (.literal U)) =
      some (narrow n) := by
  have hU : U < MOD := U_lt
  rw [eval_and (eval_local_eq hn) (eval_literal hU) hlt hU]
  simp [narrow]

/-- `accrualEnd = min(block.timestamp, maturity)` as imported from `UtilsLib.min`. -/
theorem eval_accrualEnd {oracle : DenoteOracle} {st : DenoteState} {ts mat : Nat}
    (hts : st.world.blockTimestamp.val = ts)
    (hmat : lookupValue st.bindings "market_maturity" = mat)
    (htsM : ts < MOD) (hmatM : mat < MOD) :
    evalExpr oracle midnight.model.fields st
      (.bitXor .blockTimestamp
        (.mul (.bitXor .blockTimestamp (.param "market_maturity"))
          (.lt (.param "market_maturity") .blockTimestamp))) =
      some (yulMin ts mat) := by
  subst hts
  have hx :=
    eval_xor (oracle := oracle) (eval_timestamp (oracle := oracle) (st := st))
      (eval_param_eq (oracle := oracle) hmat) htsM hmatM
  have hlt :=
    eval_lt (oracle := oracle) (eval_param_eq (oracle := oracle) hmat)
      (eval_timestamp (oracle := oracle) (st := st))
  have hflag : boolWord (decide (mat < st.world.blockTimestamp.val)) < MOD := by
    by_cases h : mat < st.world.blockTimestamp.val <;> simp [boolWord, h, one_lt_mod, zero_lt_mod]
  have hmul := eval_mul (oracle := oracle) hx hlt (xor_lt_MOD htsM hmatM) hflag
  have hprod : (st.world.blockTimestamp.val ^^^ mat) *
      boolWord (decide (mat < st.world.blockTimestamp.val)) < MOD := by
    by_cases h : mat < st.world.blockTimestamp.val
    · simpa [boolWord, h, Nat.mul_one] using xor_lt_MOD htsM hmatM
    · simp [boolWord, h, Nat.mul_zero, zero_lt_mod]
  have hmulVal : (st.world.blockTimestamp.val ^^^ mat) *
      boolWord (decide (mat < st.world.blockTimestamp.val)) % MOD =
      (st.world.blockTimestamp.val ^^^ mat) *
        boolWord (decide (mat < st.world.blockTimestamp.val)) :=
    Nat.mod_eq_of_lt hprod
  have houter :=
    eval_xor (oracle := oracle) (eval_timestamp (oracle := oracle) (st := st)) hmul htsM
      (by simpa [hmulVal] using hprod)
  rw [hmulVal] at houter
  by_cases hcmp : mat < st.world.blockTimestamp.val
  · simp [hcmp, yulMin, boolWord] at houter ⊢
    exact houter
  · simp [hcmp, yulMin, boolWord] at houter ⊢
    exact houter

theorem body_at (i : Nat) (s : Stmt) (h : body.drop i = s :: body.drop (i + 1) := by rfl) :
    body.drop i = s :: body.drop (i + 1) := h

theorem exec_return3 {oracle : DenoteOracle} {st : DenoteState} {x y z : String}
    {vx vy vz : Nat}
    (hx : lookupValue st.bindings x = vx) (hy : lookupValue st.bindings y = vy)
    (hz : lookupValue st.bindings z = vz)
    (hvx : vx < MOD) (hvy : vy < MOD) (hvz : vz < MOD) :
    execStmtList oracle midnight.model.fields st
        [.returnValues [.localVar x, .localVar y, .localVar z]] =
      .stop { st with observedReturnWords := some [vx, vy, vz] } := by
  rw [execStmtList.eq_2, execStmt_returnValues_arm]
  simp [evalExprList, eval_local_eq hx, eval_local_eq hy, eval_local_eq hz, word_of_lt hvx,
    word_of_lt hvy, word_of_lt hvz, bind, Option.bind, pure]

@[simp] theorem revert_words :
    (match (StmtOutcome.revert : StmtOutcome) with
      | .stop s | .continue s | .return _ s => s.observedReturnWords
      | .revert => none) = (none : Option (List Nat)) := rfl

@[simp] theorem stop_words (st : DenoteState) (ws : List Nat) :
    (match StmtOutcome.stop { st with observedReturnWords := some ws } with
      | .stop s | .continue s | .return _ s => s.observedReturnWords
      | .revert => none) = some ws := rfl

set_option maxHeartbeats 8000000

/-- From `fee` stored in `_verity_slice_tmp_33`, the return narrowing is `returnWords?`. -/
theorem cont_from_fee (oracle : DenoteOracle) (st : DenoteState) (psc pspf fee : Nat)
    (hpsc : lookupValue st.bindings "postSlashCredit" = psc)
    (hpspf : lookupValue st.bindings "postSlashPendingFee" = pspf)
    (htmp33 : lookupValue st.bindings "_verity_slice_tmp_33" = fee)
    (hpscU : psc ≤ U) (hpspfU : pspf ≤ U) (hfeeLe : fee ≤ pspf) :
    (match execStmtList oracle midnight.model.fields st (body.drop 16) with
      | .stop s | .continue s | .return _ s => s.observedReturnWords
      | .revert => none) =
      (returnWords? psc pspf fee).map (fun p => [p.1, p.2.1, p.2.2]) := by
  have hpscM : psc < MOD := le_U_lt_MOD hpscU
  have hpspfM : pspf < MOD := le_U_lt_MOD hpspfU
  have hfeeU : fee ≤ U := Nat.le_trans hfeeLe hpspfU
  have hfeeM : fee < MOD := le_U_lt_MOD hfeeU
  have hnarP : narrow psc = psc := narrow_eq_of_le_U hpscU
  have hnarF : narrow pspf = pspf := narrow_eq_of_le_U hpspfU
  have h16 : body.drop 16 =
      .letVar "fee" (.localVar "_verity_slice_tmp_33") :: body.drop 17 := by rfl
  rw [h16, exec_let (eval_local_eq htmp33)]
  let stF := withBind st "fee" fee
  have hfee : lookupValue stF.bindings "fee" = fee := lookup_wb_eq _ _ _
  have hpsc := look (st := st) (name := "fee") (v := fee) (key := "postSlashCredit") hpsc
  have hpspf := look (st := st) (name := "fee") (v := fee) (key := "postSlashPendingFee") hpspf
  have hwF : stF.world = st.world := by simp [stF, withBind]
  have h17 : body.drop 17 =
      .letVar "_verity_slice_tmp_34"
        (.bitAnd (.localVar "postSlashCredit") (.literal U)) :: body.drop 18 := by rfl
  rw [h17, exec_let (eval_narrow_local hpsc hpscM)]
  let st34 := withBind stF "_verity_slice_tmp_34" (narrow psc)
  have h34 : lookupValue st34.bindings "_verity_slice_tmp_34" = narrow psc := lookup_wb_eq _ _ _
  have hfee : lookupValue st34.bindings "fee" = fee := look hfee
  have hpsc : lookupValue st34.bindings "postSlashCredit" = psc := look hpsc
  have hpspf : lookupValue st34.bindings "postSlashPendingFee" = pspf := look hpspf
  have h18 : body.drop 18 =
      .letVar "_verity_slice_tmp_35" (.localVar "_verity_slice_tmp_34") :: body.drop 19 := by rfl
  rw [h18, exec_let (eval_local_eq h34)]
  let st35 := withBind st34 "_verity_slice_tmp_35" (narrow psc)
  have h35 : lookupValue st35.bindings "_verity_slice_tmp_35" = narrow psc := lookup_wb_eq _ _ _
  have hfee : lookupValue st35.bindings "fee" = fee := look hfee
  have hpspf : lookupValue st35.bindings "postSlashPendingFee" = pspf := look hpspf
  have hnarM : narrow psc < MOD := by rw [hnarP]; exact hpscM
  have h19 : body.drop 19 =
      csubBlock "_verity_slice_tmp_36" (.localVar "_verity_slice_tmp_35") (.localVar "fee") ++
        body.drop 21 := by rfl
  have h35z : lookupValue (withBind st35 "_verity_slice_tmp_36" 0).bindings "_verity_slice_tmp_35" =
      narrow psc := look h35
  have hfeez : lookupValue (withBind st35 "_verity_slice_tmp_36" 0).bindings "fee" = fee := look hfee
  rw [h19, exec_csubBlock (eval_local_eq h35z) (eval_local_eq hfeez) hnarM hfeeM]
  by_cases hle : fee ≤ narrow psc
  · have hc : csub? (narrow psc) fee = some (narrow psc - fee) := by simp [csub?, hle]
    simp only [hc]
    let nc := narrow psc - fee
    let st36 := withBind st35 "_verity_slice_tmp_36" nc
    have h36 : lookupValue st36.bindings "_verity_slice_tmp_36" = nc := lookup_wb_eq _ _ _
    have hfee : lookupValue st36.bindings "fee" = fee := look hfee
    have hpspf : lookupValue st36.bindings "postSlashPendingFee" = pspf := look hpspf
    have h21 : body.drop 21 =
        .letVar "_verity_slice_tmp_37" (.localVar "_verity_slice_tmp_36") :: body.drop 22 := by rfl
    rw [h21, exec_let (eval_local_eq h36)]
    let st37 := withBind st36 "_verity_slice_tmp_37" nc
    have h37 : lookupValue st37.bindings "_verity_slice_tmp_37" = nc := lookup_wb_eq _ _ _
    have hfee : lookupValue st37.bindings "fee" = fee := look hfee
    have hpspf : lookupValue st37.bindings "postSlashPendingFee" = pspf := look hpspf
    have h22 : body.drop 22 =
        .letVar "_verity_slice_tmp_38"
          (.bitAnd (.localVar "postSlashPendingFee") (.literal U)) :: body.drop 23 := by rfl
    rw [h22, exec_let (eval_narrow_local hpspf hpspfM)]
    let st38 := withBind st37 "_verity_slice_tmp_38" (narrow pspf)
    have h38 : lookupValue st38.bindings "_verity_slice_tmp_38" = narrow pspf := lookup_wb_eq _ _ _
    have h37 : lookupValue st38.bindings "_verity_slice_tmp_37" = nc := look h37
    have hfee : lookupValue st38.bindings "fee" = fee := look hfee
    have h23 : body.drop 23 =
        .letVar "_verity_slice_tmp_39" (.localVar "_verity_slice_tmp_38") :: body.drop 24 := by rfl
    rw [h23, exec_let (eval_local_eq h38)]
    let st39 := withBind st38 "_verity_slice_tmp_39" (narrow pspf)
    have h39 : lookupValue st39.bindings "_verity_slice_tmp_39" = narrow pspf := lookup_wb_eq _ _ _
    have h37 : lookupValue st39.bindings "_verity_slice_tmp_37" = nc := look h37
    have hfee : lookupValue st39.bindings "fee" = fee := look hfee
    have hnarFM : narrow pspf < MOD := by rw [hnarF]; exact hpspfM
    have hleF : fee ≤ narrow pspf := by simpa [hnarF] using hfeeLe
    have h24 : body.drop 24 =
        csubBlock "_verity_slice_tmp_40" (.localVar "_verity_slice_tmp_39") (.localVar "fee") ++
          body.drop 26 := by rfl
    have h39z : lookupValue (withBind st39 "_verity_slice_tmp_40" 0).bindings "_verity_slice_tmp_39" =
        narrow pspf := look h39
    have hfeez2 : lookupValue (withBind st39 "_verity_slice_tmp_40" 0).bindings "fee" = fee := look hfee
    rw [h24, exec_csubBlock (eval_local_eq h39z) (eval_local_eq hfeez2) hnarFM hfeeM]
    have hc2 : csub? (narrow pspf) fee = some (narrow pspf - fee) := by simp [csub?, hleF]
    simp only [hc2]
    let npv := narrow pspf - fee
    let st40 := withBind st39 "_verity_slice_tmp_40" npv
    have h40 : lookupValue st40.bindings "_verity_slice_tmp_40" = npv := lookup_wb_eq _ _ _
    have h37 : lookupValue st40.bindings "_verity_slice_tmp_37" = nc := look h37
    have hfee : lookupValue st40.bindings "fee" = fee := look hfee
    have h26 : body.drop 26 =
        .letVar "_verity_slice_tmp_41" (.localVar "_verity_slice_tmp_40") :: body.drop 27 := by rfl
    rw [h26, exec_let (eval_local_eq h40)]
    let st41 := withBind st40 "_verity_slice_tmp_41" npv
    have h41 : lookupValue st41.bindings "_verity_slice_tmp_41" = npv := lookup_wb_eq _ _ _
    have h37 : lookupValue st41.bindings "_verity_slice_tmp_37" = nc := look h37
    have hfee : lookupValue st41.bindings "fee" = fee := look hfee
    have hncM : nc < MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnarM
    have hnpM : npv < MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hnarFM
    have h27 : body.drop 27 =
        [.returnValues
          [.localVar "_verity_slice_tmp_37", .localVar "_verity_slice_tmp_41", .localVar "fee"]] := by
      rfl
    rw [h27, show withBind st40 "_verity_slice_tmp_41" npv = st41 from rfl,
      exec_return3 h37 h41 hfee hncM hnpM hfeeM, stop_words]
    have hle' : fee ≤ psc := by simpa [hnarP] using hle
    have hleF' : fee ≤ pspf := by simpa [hnarF] using hleF
    have hret : returnWords? psc pspf fee = some (psc - fee, pspf - fee, fee) := by
      unfold returnWords?
      have hc1 : csub? psc fee = some (psc - fee) := by simp [csub?, hle']
      have hc2 : csub? pspf fee = some (pspf - fee) := by simp [csub?, hleF']
      simp [hnarP, hnarF, hc1, hc2, bind, pure_bind, Option.bind]
    have hncEq : nc = psc - fee := by simp [nc, hnarP]
    have hnpEq : npv = pspf - fee := by simp [npv, hnarF]
    rw [hret]
    have hmap :
        Option.map (fun p : Nat × Nat × Nat => [p.1, p.2.1, p.2.2])
          (some (psc - fee, pspf - fee, fee)) =
        some [psc - fee, pspf - fee, fee] := rfl
    rw [hmap, ← hncEq, ← hnpEq]
  · have hnle : ¬ fee ≤ narrow psc := hle
    have hnle' : ¬ fee ≤ psc := by simpa [hnarP] using hnle
    have hc : csub? (narrow psc) fee = none := by simp [csub?, hnle]
    simp only [hc, revert_words]
    unfold returnWords?
    rw [hnarP]
    have hc0 : csub? psc fee = none := by simp [csub?, hnle']
    rw [hc0]
    simp [bind, Option.bind, Option.map]

/-- From `postSlashPendingFee` stored in `_verity_slice_tmp_22`, accrual and the
return are `feeWord?` followed by `returnWords?`. -/
theorem cont_after_pspf (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address)
    (mat ts credit llf lf pending lastAccrual psc pspf : Nat) (st : DenoteState)
    (hw : st.world = world)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val)
    (hmat : lookupValue st.bindings "market_maturity" = mat)
    (hpsc : lookupValue st.bindings "postSlashCredit" = psc)
    (htmp22 : lookupValue st.bindings "_verity_slice_tmp_22" = pspf)
    (hcreditU : credit ≤ U) (hpendingU : pending ≤ U) (hlaU : lastAccrual ≤ U)
    (htsM : ts < MOD) (hmatM : mat < MOD)
    (hpscLe : psc ≤ credit) (hpspfLe : pspf ≤ pending)
    (htseq : world.blockTimestamp.val = ts)
    (hlaRead : (midnight.position.lastAccrual oracle world id user).val = lastAccrual)
    (hpce : postSlashCredit? credit llf lf = some psc)
    (hpspfE : postSlashPendingFee? credit pending psc = some pspf) :
    (match execStmtList oracle midnight.model.fields st (body.drop 10) with
      | .stop s | .continue s | .return _ s => s.observedReturnWords
      | .revert => none) =
      (viewResult? credit llf lf pending lastAccrual ts mat).map
        (fun p => [p.1, p.2.1, p.2.2]) := by
  have hview :
      viewResult? credit llf lf pending lastAccrual ts mat =
        (feeWord? pspf (yulMin ts mat) lastAccrual mat).bind
          (fun fee => returnWords? psc pspf fee) := by
    simp [viewResult?, hpce, hpspfE, bind, pure_bind, Option.bind]
  rw [hview]
  have hpscU : psc ≤ U := Nat.le_trans hpscLe hcreditU
  have hpspfU : pspf ≤ U := Nat.le_trans hpspfLe hpendingU
  have hlaM : lastAccrual < MOD := le_U_lt_MOD hlaU
  have hpspfM : pspf < MOD := le_U_lt_MOD hpspfU
  have h10 : body.drop 10 =
      .letVar "postSlashPendingFee" (.localVar "_verity_slice_tmp_22") :: body.drop 11 := by rfl
  rw [h10, exec_let (eval_local_eq htmp22)]
  let stP := withBind st "postSlashPendingFee" pspf
  have hpspf : lookupValue stP.bindings "postSlashPendingFee" = pspf := lookup_wb_eq _ _ _
  have hpsc : lookupValue stP.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue stP.bindings "id" = id.val := look hid
  have huser : lookupValue stP.bindings "user" = user.val := look huser
  have hmat : lookupValue stP.bindings "market_maturity" = mat := look hmat
  have hwP : stP.world = world := by simp [stP, withBind, hw]
  have htsP : stP.world.blockTimestamp.val = ts := by simpa [hwP] using htseq
  have h11 : body.drop 11 =
      .letVar "accrualEnd"
        (.bitXor .blockTimestamp
          (.mul (.bitXor .blockTimestamp (.param "market_maturity"))
            (.lt (.param "market_maturity") .blockTimestamp))) :: body.drop 12 := by rfl
  rw [h11, exec_let (eval_accrualEnd htsP hmat htsM hmatM)]
  let endTs := yulMin ts mat
  let stE := withBind stP "accrualEnd" endTs
  have hend : lookupValue stE.bindings "accrualEnd" = endTs := lookup_wb_eq _ _ _
  have hpspf : lookupValue stE.bindings "postSlashPendingFee" = pspf := look hpspf
  have hpsc : lookupValue stE.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue stE.bindings "id" = id.val := look hid
  have huser : lookupValue stE.bindings "user" = user.val := look huser
  have hmat : lookupValue stE.bindings "market_maturity" = mat := look hmat
  have hwE : stE.world = world := by simp [stE, withBind, hwP]
  have h12 : body.drop 12 =
      .letVar "_lastAccrual"
        (.structMember2 "position" (.param "id") (.param "user") "lastAccrual") ::
        body.drop 13 := by rfl
  have hacc := eval_accrual oracle stE id user hid huser
  rw [hwE, hlaRead] at hacc
  rw [h12, exec_let hacc]
  let stA := withBind stE "_lastAccrual" lastAccrual
  have hla : lookupValue stA.bindings "_lastAccrual" = lastAccrual := lookup_wb_eq _ _ _
  have hend : lookupValue stA.bindings "accrualEnd" = endTs := look hend
  have hpspf : lookupValue stA.bindings "postSlashPendingFee" = pspf := look hpspf
  have hpsc : lookupValue stA.bindings "postSlashCredit" = psc := look hpsc
  have hmat : lookupValue stA.bindings "market_maturity" = mat := look hmat
  have h13 : body.drop 13 =
      .letVar "_verity_slice_tmp_23"
        (.lt (.localVar "_lastAccrual") (.param "market_maturity")) :: body.drop 14 := by rfl
  rw [h13, exec_let (eval_lt (eval_local_eq hla) (eval_param_eq hmat))]
  let flag := boolWord (decide (lastAccrual < mat))
  let stG := withBind stA "_verity_slice_tmp_23" flag
  have hflag : lookupValue stG.bindings "_verity_slice_tmp_23" = flag := lookup_wb_eq _ _ _
  have hla : lookupValue stG.bindings "_lastAccrual" = lastAccrual := look hla
  have hend : lookupValue stG.bindings "accrualEnd" = endTs := look hend
  have hpspf : lookupValue stG.bindings "postSlashPendingFee" = pspf := look hpspf
  have hpsc : lookupValue stG.bindings "postSlashCredit" = psc := look hpsc
  have hmat : lookupValue stG.bindings "market_maturity" = mat := look hmat
  have h14 : body.drop 14 =
      .letVar "_verity_slice_tmp_33" (.literal 0) :: body.drop 15 := by rfl
  rw [h14, exec_let (eval_literal zero_lt_mod)]
  let stZ := withBind stG "_verity_slice_tmp_33" 0
  have hflag : lookupValue stZ.bindings "_verity_slice_tmp_23" = flag := look hflag
  have hla : lookupValue stZ.bindings "_lastAccrual" = lastAccrual := look hla
  have hend : lookupValue stZ.bindings "accrualEnd" = endTs := look hend
  have hpspf : lookupValue stZ.bindings "postSlashPendingFee" = pspf := look hpspf
  have hpsc : lookupValue stZ.bindings "postSlashCredit" = psc := look hpsc
  have hmat : lookupValue stZ.bindings "market_maturity" = mat := look hmat
  have h15 : body.drop 15 =
      .ite (iteAt body 15).1 (iteAt body 15).2.1 (iteAt body 15).2.2 :: body.drop 16 := by rfl
  have hcond : (iteAt body 15).1 = .localVar "_verity_slice_tmp_23" := by rfl
  rw [h15, hcond, exec_ite (eval_local_eq hflag)]
  by_cases hlt : lastAccrual < mat
  · have hflag1 : flag = 1 := by simp [flag, boolWord, hlt]
    simp only [hflag1, show ((1 : Nat) = 0) = False by decide, if_false]
    have hendM : endTs < MOD :=
      Nat.lt_of_le_of_lt (by simpa [endTs] using yulMin_le_left ts mat) htsM
    have hsub1 : (iteAt body 15).2.1 =
        csubBlock "_verity_slice_tmp_24" (.localVar "accrualEnd") (.localVar "_lastAccrual") ++
          (iteAt body 15).2.1.drop 2 := by rfl
    have he0 : lookupValue (withBind stZ "_verity_slice_tmp_24" 0).bindings "accrualEnd" = endTs :=
      look hend
    have hl0 : lookupValue (withBind stZ "_verity_slice_tmp_24" 0).bindings "_lastAccrual" =
        lastAccrual := look hla
    rw [hsub1, List.append_assoc,
      exec_csubBlock (eval_local_eq he0) (eval_local_eq hl0) hendM hlaM]
    by_cases hdtLe : lastAccrual ≤ endTs
    · have hdtS : csub? endTs lastAccrual = some (endTs - lastAccrual) := by simp [csub?, hdtLe]
      simp only [hdtS]
      let dt := endTs - lastAccrual
      let st24 := withBind stZ "_verity_slice_tmp_24" dt
      have hdt : lookupValue st24.bindings "_verity_slice_tmp_24" = dt := lookup_wb_eq _ _ _
      have hla : lookupValue st24.bindings "_lastAccrual" = lastAccrual := look hla
      have hpspf : lookupValue st24.bindings "postSlashPendingFee" = pspf := look hpspf
      have hpsc : lookupValue st24.bindings "postSlashCredit" = psc := look hpsc
      have hmat : lookupValue st24.bindings "market_maturity" = mat := look hmat
      have h26e : (iteAt body 15).2.1.drop 2 =
          .letVar "_verity_slice_tmp_26" (.localVar "_verity_slice_tmp_24") ::
            (iteAt body 15).2.1.drop 3 := by rfl
      rw [h26e, List.cons_append, exec_let (eval_local_eq hdt)]
      let st26 := withBind st24 "_verity_slice_tmp_26" dt
      have hdt : lookupValue st26.bindings "_verity_slice_tmp_26" = dt := lookup_wb_eq _ _ _
      have hla : lookupValue st26.bindings "_lastAccrual" = lastAccrual := look hla
      have hpspf : lookupValue st26.bindings "postSlashPendingFee" = pspf := look hpspf
      have hpsc : lookupValue st26.bindings "postSlashCredit" = psc := look hpsc
      have hmat : lookupValue st26.bindings "market_maturity" = mat := look hmat
      have hdtM : dt < MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hendM
      have hsub2 : (iteAt body 15).2.1.drop 3 =
          csubBlock "_verity_slice_tmp_25" (.param "market_maturity") (.localVar "_lastAccrual") ++
            (iteAt body 15).2.1.drop 5 := by rfl
      have hm0 : lookupValue (withBind st26 "_verity_slice_tmp_25" 0).bindings "market_maturity" =
          mat := look hmat
      have hl1 : lookupValue (withBind st26 "_verity_slice_tmp_25" 0).bindings "_lastAccrual" =
          lastAccrual := look hla
      rw [hsub2, List.append_assoc,
        exec_csubBlock (eval_param_eq hm0) (eval_local_eq hl1) hmatM hlaM]
      have hspanLe : lastAccrual ≤ mat := Nat.le_of_lt hlt
      have hspanS : csub? mat lastAccrual = some (mat - lastAccrual) := by simp [csub?, hspanLe]
      simp only [hspanS]
      let span := mat - lastAccrual
      let st25 := withBind st26 "_verity_slice_tmp_25" span
      have hspan : lookupValue st25.bindings "_verity_slice_tmp_25" = span := lookup_wb_eq _ _ _
      have hdt : lookupValue st25.bindings "_verity_slice_tmp_26" = dt := look hdt
      have hpspf : lookupValue st25.bindings "postSlashPendingFee" = pspf := look hpspf
      have hpsc : lookupValue st25.bindings "postSlashCredit" = psc := look hpsc
      have h27e : (iteAt body 15).2.1.drop 5 =
          .letVar "_verity_slice_tmp_27" (.localVar "_verity_slice_tmp_25") ::
            (iteAt body 15).2.1.drop 6 := by rfl
      rw [h27e, List.cons_append, exec_let (eval_local_eq hspan)]
      let st27 := withBind st25 "_verity_slice_tmp_27" span
      have hspan : lookupValue st27.bindings "_verity_slice_tmp_27" = span := lookup_wb_eq _ _ _
      have hdt : lookupValue st27.bindings "_verity_slice_tmp_26" = dt := look hdt
      have hpspf : lookupValue st27.bindings "postSlashPendingFee" = pspf := look hpspf
      have hpsc : lookupValue st27.bindings "postSlashCredit" = psc := look hpsc
      have hmulb : (iteAt body 15).2.1.drop 6 =
          cmulBlock "_verity_slice_tmp_28" (.localVar "postSlashPendingFee")
            (.localVar "_verity_slice_tmp_26") ++ (iteAt body 15).2.1.drop 8 := by rfl
      have hp0 : lookupValue (withBind st27 "_verity_slice_tmp_28" 0).bindings
          "postSlashPendingFee" = pspf := look hpspf
      have hd0 : lookupValue (withBind st27 "_verity_slice_tmp_28" 0).bindings
          "_verity_slice_tmp_26" = dt := look hdt
      rw [hmulb, List.append_assoc, exec_cmulBlock (eval_local_eq hp0) (eval_local_eq hd0) hpspfM hdtM]
      by_cases hprodLt : pspf * dt < MOD
      · have hcm : cmul? pspf dt = some (pspf * dt) := by simp [cmul?, hprodLt]
        simp only [hcm]
        let prod := pspf * dt
        let st28 := withBind st27 "_verity_slice_tmp_28" prod
        have hprod : lookupValue st28.bindings "_verity_slice_tmp_28" = prod := lookup_wb_eq _ _ _
        have hspan : lookupValue st28.bindings "_verity_slice_tmp_27" = span := look hspan
        have hpsc : lookupValue st28.bindings "postSlashCredit" = psc := look hpsc
        have hpspf : lookupValue st28.bindings "postSlashPendingFee" = pspf := look hpspf
        have h29e : (iteAt body 15).2.1.drop 8 =
            .letVar "_verity_slice_tmp_29" (.localVar "_verity_slice_tmp_28") ::
              (iteAt body 15).2.1.drop 9 := by rfl
        rw [h29e, List.cons_append, exec_let (eval_local_eq hprod)]
        let st29 := withBind st28 "_verity_slice_tmp_29" prod
        have hprod : lookupValue st29.bindings "_verity_slice_tmp_29" = prod := lookup_wb_eq _ _ _
        have hspan : lookupValue st29.bindings "_verity_slice_tmp_27" = span := look hspan
        have hpsc : lookupValue st29.bindings "postSlashCredit" = psc := look hpsc
        have hpspf : lookupValue st29.bindings "postSlashPendingFee" = pspf := look hpspf
        have hprodM : prod < MOD := by simpa [prod] using hprodLt
        have hspanM : span < MOD := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hmatM
        have hspan0 : span ≠ 0 := by
          have : 0 < span := by simpa [span] using Nat.sub_pos_of_lt hlt
          omega
        have hdivb : (iteAt body 15).2.1.drop 9 =
            cdivBlock "_verity_slice_tmp_30" (.localVar "_verity_slice_tmp_29")
              (.localVar "_verity_slice_tmp_27") ++ (iteAt body 15).2.1.drop 11 := by rfl
        have hn0 : lookupValue (withBind st29 "_verity_slice_tmp_30" 0).bindings
            "_verity_slice_tmp_29" = prod := look hprod
        have hs0 : lookupValue (withBind st29 "_verity_slice_tmp_30" 0).bindings
            "_verity_slice_tmp_27" = span := look hspan
        rw [hdivb, List.append_assoc,
          exec_cdivBlock (eval_local_eq hn0) (eval_local_eq hs0) hprodM hspanM]
        have hcd : cdiv? prod span = some (prod / span) := by simp [cdiv?, hspan0]
        simp only [hcd]
        let quot := prod / span
        let st30 := withBind st29 "_verity_slice_tmp_30" quot
        have hquot : lookupValue st30.bindings "_verity_slice_tmp_30" = quot := lookup_wb_eq _ _ _
        have hpsc : lookupValue st30.bindings "postSlashCredit" = psc := look hpsc
        have hpspf : lookupValue st30.bindings "postSlashPendingFee" = pspf := look hpspf
        have hquotM : quot < MOD := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprodM
        have h31e : (iteAt body 15).2.1.drop 11 =
            .letVar "_verity_slice_tmp_31" (.localVar "_verity_slice_tmp_30") ::
              (iteAt body 15).2.1.drop 12 := by rfl
        rw [h31e, List.cons_append, exec_let (eval_local_eq hquot)]
        let st31 := withBind st30 "_verity_slice_tmp_31" quot
        have hquot : lookupValue st31.bindings "_verity_slice_tmp_31" = quot := lookup_wb_eq _ _ _
        have hpsc : lookupValue st31.bindings "postSlashCredit" = psc := look hpsc
        have hpspf : lookupValue st31.bindings "postSlashPendingFee" = pspf := look hpspf
        have h32e : (iteAt body 15).2.1.drop 12 =
            .letVar "_verity_slice_tmp_32"
              (.bitAnd (.localVar "_verity_slice_tmp_31") (.literal U)) ::
              (iteAt body 15).2.1.drop 13 := by rfl
        rw [h32e, List.cons_append, exec_let (eval_narrow_local hquot hquotM)]
        let feeV := narrow quot
        let st32 := withBind st31 "_verity_slice_tmp_32" feeV
        have h32 : lookupValue st32.bindings "_verity_slice_tmp_32" = feeV := lookup_wb_eq _ _ _
        have hpsc : lookupValue st32.bindings "postSlashCredit" = psc := look hpsc
        have hpspf : lookupValue st32.bindings "postSlashPendingFee" = pspf := look hpspf
        have h33e : (iteAt body 15).2.1.drop 13 ++ body.drop 16 =
            .assignVar "_verity_slice_tmp_33" (.localVar "_verity_slice_tmp_32") :: body.drop 16 := by
          rfl
        rw [h33e, exec_assign (eval_local_eq h32)]
        let st33 := withBind st32 "_verity_slice_tmp_33" feeV
        have htmp33 : lookupValue st33.bindings "_verity_slice_tmp_33" = feeV := lookup_wb_eq _ _ _
        have hpsc : lookupValue st33.bindings "postSlashCredit" = psc := look hpsc
        have hpspf : lookupValue st33.bindings "postSlashPendingFee" = pspf := look hpspf
        have hdtY : csub? (yulMin ts mat) lastAccrual = some dt := by simp [hdtS, endTs, dt]
        have hfw : feeWord? pspf (yulMin ts mat) lastAccrual mat = some feeV := by
          unfold feeWord?
          rw [if_pos hlt, hdtY]
          simp only [bind, pure_bind, Option.bind]
          rw [hspanS]
          simp only [bind, pure_bind, Option.bind, span]
          have hcm' : cmul? pspf dt = some prod := by simp [hcm, prod]
          rw [hcm']
          simp only [bind, pure_bind, Option.bind, prod]
          have hcd' : cdiv? prod span = some quot := by simp [hcd, quot]
          rw [hcd']
        have hfeeLe : feeV ≤ pspf := by
          have hendLe : endTs ≤ mat := by simpa [endTs] using yulMin_le_right ts mat
          have hfw' : feeWord? pspf endTs lastAccrual mat = some feeV := by simpa [endTs] using hfw
          exact feeWord_le hendLe hfw'
        rw [show withBind st32 "_verity_slice_tmp_33" feeV = st33 from rfl]
        rw [cont_from_fee oracle st33 psc pspf feeV hpsc hpspf htmp33 hpscU hpspfU hfeeLe]
        rw [hfw]
        simp [bind, pure_bind, Option.bind]
      · have hcm : cmul? pspf dt = none := by simp [cmul?, hprodLt]
        simp only [hcm, revert_words]
        have hdtY : csub? (yulMin ts mat) lastAccrual = some dt := by simp [hdtS, endTs, dt]
        unfold feeWord?
        rw [if_pos hlt, hdtY]
        simp only [bind, pure_bind, Option.bind]
        rw [hspanS]
        simp only [bind, pure_bind, Option.bind, span, hcm, Option.map]
    · have hdtN : csub? endTs lastAccrual = none := by simp [csub?, hdtLe]
      simp only [hdtN, revert_words]
      have hdtY : csub? (yulMin ts mat) lastAccrual = none := by simpa [endTs] using hdtN
      unfold feeWord?
      rw [if_pos hlt, hdtY]
      simp [bind, Option.bind, Option.map]
  · have hflag0 : flag = 0 := by simp [flag, boolWord, hlt]
    simp only [hflag0, if_true]
    have helse : (iteAt body 15).2.2 ++ body.drop 16 =
        .assignVar "_verity_slice_tmp_33" (.literal 0) :: body.drop 16 := by rfl
    rw [helse, exec_assign (eval_literal zero_lt_mod)]
    let st33 := withBind stZ "_verity_slice_tmp_33" 0
    have htmp33 : lookupValue st33.bindings "_verity_slice_tmp_33" = 0 := lookup_wb_eq _ _ _
    have hpsc : lookupValue st33.bindings "postSlashCredit" = psc := look hpsc
    have hpspf : lookupValue st33.bindings "postSlashPendingFee" = pspf := look hpspf
    have hfw : feeWord? pspf (yulMin ts mat) lastAccrual mat = some 0 := by
      unfold feeWord?
      simp [hlt, endTs]
    have hfeeLe : (0 : Nat) ≤ pspf := Nat.zero_le _
    rw [show withBind stZ "_verity_slice_tmp_33" 0 = st33 from rfl]
    rw [cont_from_fee oracle st33 psc pspf 0 hpsc hpspf htmp33 hpscU hpspfU hfeeLe]
    simp [hfw, bind, pure_bind, Option.bind]

/-- `credit > 0` branch: the pending-fee slice always succeeds, then accrual runs. -/
theorem cont_pending_then (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address)
    (mat ts credit llf lf pending lastAccrual psc pspf : Nat) (st : DenoteState)
    (hw : st.world = world)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val)
    (hmat : lookupValue st.bindings "market_maturity" = mat)
    (hcredit : lookupValue st.bindings "_credit" = credit)
    (hpend : lookupValue st.bindings "_pendingFee" = pending)
    (hpsc : lookupValue st.bindings "postSlashCredit" = psc)
    (hcreditU : credit ≤ U) (hpendingU : pending ≤ U) (hlaU : lastAccrual ≤ U)
    (htsM : ts < MOD) (hmatM : mat < MOD)
    (hpscLe : psc ≤ credit) (hpspfLe : pspf ≤ pending) (hpos : 0 < credit)
    (htseq : world.blockTimestamp.val = ts)
    (hlaRead : (midnight.position.lastAccrual oracle world id user).val = lastAccrual)
    (hpce : postSlashCredit? credit llf lf = some psc)
    (hpspfE : postSlashPendingFee? credit pending psc = some pspf) :
    (match execStmtList oracle midnight.model.fields st
        ((iteAt body 9).2.1 ++ body.drop 10) with
      | .stop s | .continue s | .return _ s => s.observedReturnWords
      | .revert => none) =
      (viewResult? credit llf lf pending lastAccrual ts mat).map
        (fun p => [p.1, p.2.1, p.2.2]) := by
  have hcreditM : credit < MOD := le_U_lt_MOD hcreditU
  have hpendingM : pending < MOD := le_U_lt_MOD hpendingU
  have hpscM : psc < MOD := le_U_lt_MOD (Nat.le_trans hpscLe hcreditU)
  have hform := postSlashPendingFee_eq hcreditU hpendingU hpscLe
  rw [hform] at hpspfE
  injection hpspfE with hpspfEq
  have hne0 : credit ≠ 0 := by omega
  let delta := credit - psc
  let prod := pending * delta
  let cm1 := credit - 1
  let sum := prod + cm1
  let quot := sum / credit
  let result := pending - quot
  have hdeltaU : delta ≤ U := by simp [delta]; omega
  have hmulLt : prod < MOD := by simpa [prod, delta] using mul_bound hpendingU hdeltaU
  have hprodLe : prod ≤ U * U := by simpa [prod] using Nat.mul_le_mul hpendingU hdeltaU
  have hsumLt : sum < MOD := by simpa [sum, cm1] using add_bound hprodLe hcreditU
  have hone : 1 ≤ credit := hpos
  have hquotLe : quot ≤ pending := by
    have hle : pending * (credit - psc) + (credit - 1) ≤ pending * credit + (credit - 1) := by
      have : credit - psc ≤ credit := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _
    have hdiv : (pending * credit + (credit - 1)) / credit = pending := ceilDiv_cancel hpos
    have hdivLe : (pending * (credit - psc) + (credit - 1)) / credit ≤
        (pending * credit + (credit - 1)) / credit := Nat.div_le_div_right hle
    have : (pending * (credit - psc) + (credit - 1)) / credit ≤ pending := by
      simpa [hdiv] using hdivLe
    simpa [quot, sum, prod, cm1, delta] using this
  have hres : result = pspf := by
    rw [← hpspfEq]
    simp [result, quot, sum, prod, cm1, delta, hne0]
  have hsub : (iteAt body 9).2.1 =
      csubBlock "_verity_slice_tmp_11" (.localVar "_credit") (.localVar "postSlashCredit") ++
        (iteAt body 9).2.1.drop 2 := by rfl
  have hc0 : lookupValue (withBind st "_verity_slice_tmp_11" 0).bindings "_credit" = credit :=
    look hcredit
  have hp0 : lookupValue (withBind st "_verity_slice_tmp_11" 0).bindings "postSlashCredit" = psc :=
    look hpsc
  rw [hsub, List.append_assoc, exec_csubBlock (eval_local_eq hc0) (eval_local_eq hp0) hcreditM hpscM]
  have hcsub : csub? credit psc = some delta := by simp [csub?, hpscLe, delta]
  simp only [hcsub]
  let st11 := withBind st "_verity_slice_tmp_11" delta
  have hdelta : lookupValue st11.bindings "_verity_slice_tmp_11" = delta := lookup_wb_eq _ _ _
  have hcredit : lookupValue st11.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st11.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st11.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st11.bindings "id" = id.val := look hid
  have huser : lookupValue st11.bindings "user" = user.val := look huser
  have hmat : lookupValue st11.bindings "market_maturity" = mat := look hmat
  have hw : st11.world = world := by simp [st11, withBind, hw]
  have h12e : (iteAt body 9).2.1.drop 2 =
      .letVar "_verity_slice_tmp_12" (.localVar "_verity_slice_tmp_11") ::
        (iteAt body 9).2.1.drop 3 := by rfl
  rw [h12e, List.cons_append, exec_let (eval_local_eq hdelta)]
  let st12 := withBind st11 "_verity_slice_tmp_12" delta
  have hdelta : lookupValue st12.bindings "_verity_slice_tmp_12" = delta := lookup_wb_eq _ _ _
  have hcredit : lookupValue st12.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st12.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st12.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st12.bindings "id" = id.val := look hid
  have huser : lookupValue st12.bindings "user" = user.val := look huser
  have hmat : lookupValue st12.bindings "market_maturity" = mat := look hmat
  have hw : st12.world = world := by simp [st12, withBind, hw]
  have hdeltaM : delta < MOD := le_U_lt_MOD hdeltaU
  have hmulb : (iteAt body 9).2.1.drop 3 =
      cmulBlock "_verity_slice_tmp_13" (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_12") ++
        (iteAt body 9).2.1.drop 5 := by rfl
  have hpe0 : lookupValue (withBind st12 "_verity_slice_tmp_13" 0).bindings "_pendingFee" = pending :=
    look hpend
  have hd0 : lookupValue (withBind st12 "_verity_slice_tmp_13" 0).bindings "_verity_slice_tmp_12" =
      delta := look hdelta
  rw [hmulb, List.append_assoc, exec_cmulBlock (eval_local_eq hpe0) (eval_local_eq hd0) hpendingM hdeltaM]
  have hcm : cmul? pending delta = some prod := by simp [cmul?, hmulLt, prod]
  simp only [hcm]
  let st13 := withBind st12 "_verity_slice_tmp_13" prod
  have hprod : lookupValue st13.bindings "_verity_slice_tmp_13" = prod := lookup_wb_eq _ _ _
  have hcredit : lookupValue st13.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st13.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st13.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st13.bindings "id" = id.val := look hid
  have huser : lookupValue st13.bindings "user" = user.val := look huser
  have hmat : lookupValue st13.bindings "market_maturity" = mat := look hmat
  have hw : st13.world = world := by simp [st13, withBind, hw]
  have h15e : (iteAt body 9).2.1.drop 5 =
      .letVar "_verity_slice_tmp_15" (.localVar "_verity_slice_tmp_13") ::
        (iteAt body 9).2.1.drop 6 := by rfl
  rw [h15e, List.cons_append, exec_let (eval_local_eq hprod)]
  let st15 := withBind st13 "_verity_slice_tmp_15" prod
  have hprod : lookupValue st15.bindings "_verity_slice_tmp_15" = prod := lookup_wb_eq _ _ _
  have hcredit : lookupValue st15.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st15.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st15.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st15.bindings "id" = id.val := look hid
  have huser : lookupValue st15.bindings "user" = user.val := look huser
  have hmat : lookupValue st15.bindings "market_maturity" = mat := look hmat
  have hw : st15.world = world := by simp [st15, withBind, hw]
  have hsub1 : (iteAt body 9).2.1.drop 6 =
      csubBlock "_verity_slice_tmp_14" (.localVar "_credit") (.literal 1) ++
        (iteAt body 9).2.1.drop 8 := by rfl
  have hc1 : lookupValue (withBind st15 "_verity_slice_tmp_14" 0).bindings "_credit" = credit :=
    look hcredit
  rw [hsub1, List.append_assoc,
    exec_csubBlock (eval_local_eq hc1) (eval_literal one_lt_mod) hcreditM one_lt_mod]
  have hcsub1 : csub? credit 1 = some cm1 := by simp [csub?, hone, cm1]
  simp only [hcsub1]
  let st14 := withBind st15 "_verity_slice_tmp_14" cm1
  have hcm1 : lookupValue st14.bindings "_verity_slice_tmp_14" = cm1 := lookup_wb_eq _ _ _
  have hprod : lookupValue st14.bindings "_verity_slice_tmp_15" = prod := look hprod
  have hcredit : lookupValue st14.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st14.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st14.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st14.bindings "id" = id.val := look hid
  have huser : lookupValue st14.bindings "user" = user.val := look huser
  have hmat : lookupValue st14.bindings "market_maturity" = mat := look hmat
  have hw : st14.world = world := by simp [st14, withBind, hw]
  have h16e : (iteAt body 9).2.1.drop 8 =
      .letVar "_verity_slice_tmp_16" (.localVar "_verity_slice_tmp_14") ::
        (iteAt body 9).2.1.drop 9 := by rfl
  rw [h16e, List.cons_append, exec_let (eval_local_eq hcm1)]
  let st16 := withBind st14 "_verity_slice_tmp_16" cm1
  have hcm1 : lookupValue st16.bindings "_verity_slice_tmp_16" = cm1 := lookup_wb_eq _ _ _
  have hprod : lookupValue st16.bindings "_verity_slice_tmp_15" = prod := look hprod
  have hcredit : lookupValue st16.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st16.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st16.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st16.bindings "id" = id.val := look hid
  have huser : lookupValue st16.bindings "user" = user.val := look huser
  have hmat : lookupValue st16.bindings "market_maturity" = mat := look hmat
  have hw : st16.world = world := by simp [st16, withBind, hw]
  have hcm1M : cm1 < MOD := le_U_lt_MOD (by simp [cm1]; omega)
  have hprodM : prod < MOD := hmulLt
  have haddb : (iteAt body 9).2.1.drop 9 =
      caddBlock "_verity_slice_tmp_17" (.localVar "_verity_slice_tmp_15")
        (.localVar "_verity_slice_tmp_16") ++ (iteAt body 9).2.1.drop 11 := by rfl
  have ha0 : lookupValue (withBind st16 "_verity_slice_tmp_17" 0).bindings "_verity_slice_tmp_15" =
      prod := look hprod
  have hb0 : lookupValue (withBind st16 "_verity_slice_tmp_17" 0).bindings "_verity_slice_tmp_16" =
      cm1 := look hcm1
  rw [haddb, List.append_assoc, exec_caddBlock (eval_local_eq ha0) (eval_local_eq hb0) hprodM hcm1M]
  have hca : cadd? prod cm1 = some sum := by simp [cadd?, hsumLt, sum]
  simp only [hca]
  let st17 := withBind st16 "_verity_slice_tmp_17" sum
  have hsum : lookupValue st17.bindings "_verity_slice_tmp_17" = sum := lookup_wb_eq _ _ _
  have hcredit : lookupValue st17.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st17.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st17.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st17.bindings "id" = id.val := look hid
  have huser : lookupValue st17.bindings "user" = user.val := look huser
  have hmat : lookupValue st17.bindings "market_maturity" = mat := look hmat
  have hw : st17.world = world := by simp [st17, withBind, hw]
  have h18e : (iteAt body 9).2.1.drop 11 =
      .letVar "_verity_slice_tmp_18" (.localVar "_verity_slice_tmp_17") ::
        (iteAt body 9).2.1.drop 12 := by rfl
  rw [h18e, List.cons_append, exec_let (eval_local_eq hsum)]
  let st18 := withBind st17 "_verity_slice_tmp_18" sum
  have hsum : lookupValue st18.bindings "_verity_slice_tmp_18" = sum := lookup_wb_eq _ _ _
  have hcredit : lookupValue st18.bindings "_credit" = credit := look hcredit
  have hpend : lookupValue st18.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st18.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st18.bindings "id" = id.val := look hid
  have huser : lookupValue st18.bindings "user" = user.val := look huser
  have hmat : lookupValue st18.bindings "market_maturity" = mat := look hmat
  have hw : st18.world = world := by simp [st18, withBind, hw]
  have hdivb : (iteAt body 9).2.1.drop 12 =
      cdivBlock "_verity_slice_tmp_19" (.localVar "_verity_slice_tmp_18") (.localVar "_credit") ++
        (iteAt body 9).2.1.drop 14 := by rfl
  have hn0 : lookupValue (withBind st18 "_verity_slice_tmp_19" 0).bindings "_verity_slice_tmp_18" =
      sum := look hsum
  have hd1 : lookupValue (withBind st18 "_verity_slice_tmp_19" 0).bindings "_credit" = credit :=
    look hcredit
  rw [hdivb, List.append_assoc, exec_cdivBlock (eval_local_eq hn0) (eval_local_eq hd1) hsumLt hcreditM]
  have hcd : cdiv? sum credit = some quot := by simp [cdiv?, hne0, quot]
  simp only [hcd]
  let st19 := withBind st18 "_verity_slice_tmp_19" quot
  have hquot : lookupValue st19.bindings "_verity_slice_tmp_19" = quot := lookup_wb_eq _ _ _
  have hpend : lookupValue st19.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st19.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st19.bindings "id" = id.val := look hid
  have huser : lookupValue st19.bindings "user" = user.val := look huser
  have hmat : lookupValue st19.bindings "market_maturity" = mat := look hmat
  have hw : st19.world = world := by simp [st19, withBind, hw]
  have h20e : (iteAt body 9).2.1.drop 14 =
      .letVar "_verity_slice_tmp_20" (.localVar "_verity_slice_tmp_19") ::
        (iteAt body 9).2.1.drop 15 := by rfl
  rw [h20e, List.cons_append, exec_let (eval_local_eq hquot)]
  let st20 := withBind st19 "_verity_slice_tmp_20" quot
  have hquot : lookupValue st20.bindings "_verity_slice_tmp_20" = quot := lookup_wb_eq _ _ _
  have hpend : lookupValue st20.bindings "_pendingFee" = pending := look hpend
  have hpsc : lookupValue st20.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st20.bindings "id" = id.val := look hid
  have huser : lookupValue st20.bindings "user" = user.val := look huser
  have hmat : lookupValue st20.bindings "market_maturity" = mat := look hmat
  have hw : st20.world = world := by simp [st20, withBind, hw]
  have hquotM : quot < MOD := le_U_lt_MOD (Nat.le_trans hquotLe hpendingU)
  have hsub2 : (iteAt body 9).2.1.drop 15 =
      csubBlock "_verity_slice_tmp_21" (.localVar "_pendingFee") (.localVar "_verity_slice_tmp_20") ++
        (iteAt body 9).2.1.drop 17 := by rfl
  have hp1 : lookupValue (withBind st20 "_verity_slice_tmp_21" 0).bindings "_pendingFee" = pending :=
    look hpend
  have hq0 : lookupValue (withBind st20 "_verity_slice_tmp_21" 0).bindings "_verity_slice_tmp_20" =
      quot := look hquot
  rw [hsub2, List.append_assoc, exec_csubBlock (eval_local_eq hp1) (eval_local_eq hq0) hpendingM hquotM]
  have hcfin : csub? pending quot = some result := by simp [csub?, hquotLe, result]
  simp only [hcfin]
  let st21 := withBind st20 "_verity_slice_tmp_21" result
  have hresL : lookupValue st21.bindings "_verity_slice_tmp_21" = result := lookup_wb_eq _ _ _
  have hpsc : lookupValue st21.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st21.bindings "id" = id.val := look hid
  have huser : lookupValue st21.bindings "user" = user.val := look huser
  have hmat : lookupValue st21.bindings "market_maturity" = mat := look hmat
  have hw : st21.world = world := by simp [st21, withBind, hw]
  have h22e : (iteAt body 9).2.1.drop 17 ++ body.drop 10 =
      .assignVar "_verity_slice_tmp_22" (.localVar "_verity_slice_tmp_21") :: body.drop 10 := by rfl
  rw [h22e, exec_assign (eval_local_eq hresL)]
  let st22 := withBind st21 "_verity_slice_tmp_22" result
  have htmp22 : lookupValue st22.bindings "_verity_slice_tmp_22" = pspf :=
    (lookup_wb_eq st21 "_verity_slice_tmp_22" result).trans hres
  have hpsc : lookupValue st22.bindings "postSlashCredit" = psc := look hpsc
  have hid : lookupValue st22.bindings "id" = id.val := look hid
  have huser : lookupValue st22.bindings "user" = user.val := look huser
  have hmat : lookupValue st22.bindings "market_maturity" = mat := look hmat
  have hw : st22.world = world := by simp [st22, withBind, hw]
  rw [show withBind st21 "_verity_slice_tmp_22" result = st22 from rfl]
  exact cont_after_pspf oracle world id user mat ts credit llf lf pending lastAccrual psc pspf st22
    hw hid huser hmat hpsc htmp22 hcreditU hpendingU hlaU htsM hmatM hpscLe hpspfLe
    htseq hlaRead hpce (by simpa [hpspfEq] using hform)

/-- From `postSlashCredit` stored in `_verity_slice_tmp_9`, the rest of the body
is `viewResult?`. -/
theorem cont_from_tmp9 (oracle : DenoteOracle) (world : Verity.ContractState)
    (id : BytesN 32) (user : Address)
    (mat ts credit llf lf pending lastAccrual psc : Nat) (st : DenoteState)
    (hw : st.world = world)
    (hid : lookupValue st.bindings "id" = id.val)
    (huser : lookupValue st.bindings "user" = user.val)
    (hmat : lookupValue st.bindings "market_maturity" = mat)
    (hcredit : lookupValue st.bindings "_credit" = credit)
    (htmp9 : lookupValue st.bindings "_verity_slice_tmp_9" = psc)
    (hcreditU : credit ≤ U) (hllfU : llf ≤ U) (hlfU : lf ≤ U) (hpendingU : pending ≤ U)
    (hlaU : lastAccrual ≤ U) (htsM : ts < MOD) (hmatM : mat < MOD)
    (hord : llf ≤ lf) (htseq : world.blockTimestamp.val = ts)
    (hpendingRead : (midnight.position.pendingFee oracle world id user).val = pending)
    (hlaRead : (midnight.position.lastAccrual oracle world id user).val = lastAccrual)
    (hpscEq : psc = if llf < U then (credit * (U - lf)) / (U - llf) else 0) :
    (match execStmtList oracle midnight.model.fields st (body.drop 5) with
      | .stop s | .continue s | .return _ s => s.observedReturnWords
      | .revert => none) =
      (viewResult? credit llf lf pending lastAccrual ts mat).map (fun p => [p.1, p.2.1, p.2.2]) := by
  have hcreditM : credit < MOD := le_U_lt_MOD hcreditU
  have hllfM : llf < MOD := le_U_lt_MOD hllfU
  have hpendingM : pending < MOD := le_U_lt_MOD hpendingU
  have hlaM : lastAccrual < MOD := le_U_lt_MOD hlaU
  have hpce : postSlashCredit? credit llf lf = some psc := by
    rw [postSlashCredit_eq hcreditU hllfU hlfU, hpscEq]
  have hpscLe : psc ≤ credit := postSlashCredit_le hcreditU hllfU hlfU hord hpce
  have hpscM : psc < MOD := le_U_lt_MOD (Nat.le_trans hpscLe hcreditU)
  let pspf := if credit = 0 then 0 else
    pending - (pending * (credit - psc) + (credit - 1)) / credit
  have hpspfE : postSlashPendingFee? credit pending psc = some pspf := by
    rw [postSlashPendingFee_eq hcreditU hpendingU hpscLe]
  have hpspfLe : pspf ≤ pending := postSlashPendingFee_le hpspfE
  have hpspfM : pspf < MOD := le_U_lt_MOD (Nat.le_trans hpspfLe hpendingU)
  -- Copy postSlashCredit and read pendingFee.
  have h5 : body.drop 5 = .letVar "postSlashCredit" (.localVar "_verity_slice_tmp_9") :: body.drop 6 := by rfl
  rw [h5, exec_let (eval_local_eq htmp9)]
  let stP := withBind st "postSlashCredit" psc
  have hpsc : lookupValue stP.bindings "postSlashCredit" = psc := lookup_wb_eq _ _ _
  have hidP : lookupValue stP.bindings "id" = id.val := look hid
  have huserP : lookupValue stP.bindings "user" = user.val := look huser
  have hmatP : lookupValue stP.bindings "market_maturity" = mat := look hmat
  have hcreditP : lookupValue stP.bindings "_credit" = credit := look hcredit
  have hwP : stP.world = world := by simp [stP, withBind, hw]
  have h6 : body.drop 6 = .letVar "_pendingFee"
      (.structMember2 "position" (.param "id") (.param "user") "pendingFee") :: body.drop 7 := by rfl
  have hpend := eval_pending oracle stP id user hidP huserP
  rw [hwP, hpendingRead] at hpend
  rw [h6, exec_let hpend]
  let stF := withBind stP "_pendingFee" pending
  have hpendF : lookupValue stF.bindings "_pendingFee" = pending := lookup_wb_eq _ _ _
  have hcreditF : lookupValue stF.bindings "_credit" = credit := look hcreditP
  have hpscF : lookupValue stF.bindings "postSlashCredit" = psc := look hpsc
  have hidF : lookupValue stF.bindings "id" = id.val := look hidP
  have huserF : lookupValue stF.bindings "user" = user.val := look huserP
  have hmatF : lookupValue stF.bindings "market_maturity" = mat := look hmatP
  have h7 : body.drop 7 = .letVar "_verity_slice_tmp_10"
      (.gt (.localVar "_credit") (.literal 0)) :: body.drop 8 := by rfl
  rw [h7, exec_let (eval_gt (eval_local_eq hcreditF) (eval_literal zero_lt_mod))]
  let flag := boolWord (decide (0 < credit))
  let stG := withBind stF "_verity_slice_tmp_10" flag
  have hflag : lookupValue stG.bindings "_verity_slice_tmp_10" = flag := lookup_wb_eq _ _ _
  have hcreditG : lookupValue stG.bindings "_credit" = credit := look hcreditF
  have hpendG : lookupValue stG.bindings "_pendingFee" = pending := look hpendF
  have hpscG : lookupValue stG.bindings "postSlashCredit" = psc := look hpscF
  have hidG : lookupValue stG.bindings "id" = id.val := look hidF
  have huserG : lookupValue stG.bindings "user" = user.val := look huserF
  have hmatG : lookupValue stG.bindings "market_maturity" = mat := look hmatF
  have h8 : body.drop 8 = .letVar "_verity_slice_tmp_22" (.literal 0) :: body.drop 9 := by rfl
  rw [h8, exec_let (eval_literal zero_lt_mod)]
  let stZ := withBind stG "_verity_slice_tmp_22" 0
  have hcreditZ : lookupValue stZ.bindings "_credit" = credit := look hcreditG
  have hpendZ : lookupValue stZ.bindings "_pendingFee" = pending := look hpendG
  have hpscZ : lookupValue stZ.bindings "postSlashCredit" = psc := look hpscG
  have hidZ : lookupValue stZ.bindings "id" = id.val := look hidG
  have huserZ : lookupValue stZ.bindings "user" = user.val := look huserG
  have hmatZ : lookupValue stZ.bindings "market_maturity" = mat := look hmatG
  have hflagZ : lookupValue stZ.bindings "_verity_slice_tmp_10" = flag := look hflag
  have hwZ : stZ.world = world := by simp [stZ, stG, stF, stP, withBind, hw]
  have h9 : body.drop 9 =
      .ite (iteAt body 9).1 (iteAt body 9).2.1 (iteAt body 9).2.2 :: body.drop 10 := by rfl
  have hcond : (iteAt body 9).1 = .localVar "_verity_slice_tmp_10" := by rfl
  rw [h9, hcond, exec_ite (eval_local_eq hflagZ)]
  -- Pending-fee branch. `credit > 0` selects the arithmetic; otherwise the fee is 0.
  by_cases hpos : 0 < credit
  · have hflag1 : flag = 1 := by simp [flag, boolWord, hpos]
    simp only [hflag1, show ((1 : Nat) = 0) = False by decide, if_false]
    exact cont_pending_then oracle world id user mat ts credit llf lf pending lastAccrual psc pspf stZ
      hwZ hidZ huserZ hmatZ hcreditZ hpendZ hpscZ hcreditU hpendingU hlaU htsM hmatM hpscLe hpspfLe
      hpos htseq hlaRead hpce hpspfE
  · have hflag0 : flag = 0 := by simp [flag, boolWord, hpos]
    simp only [hflag0, if_true]
    have helse : (iteAt body 9).2.2 ++ body.drop 10 =
        .assignVar "_verity_slice_tmp_22" (.literal 0) :: body.drop 10 := by rfl
    rw [helse, exec_assign (eval_literal zero_lt_mod)]
    let st22 := withBind stZ "_verity_slice_tmp_22" 0
    have hcred0 : credit = 0 := by omega
    have hpspf0 : pspf = 0 := by simp [pspf, hcred0]
    have htmp22 : lookupValue st22.bindings "_verity_slice_tmp_22" = pspf := by
      simpa [hpspf0] using lookup_wb_eq stZ "_verity_slice_tmp_22" 0
    have hpsc22 : lookupValue st22.bindings "postSlashCredit" = psc := look hpscZ
    have hid22 : lookupValue st22.bindings "id" = id.val := look hidZ
    have huser22 : lookupValue st22.bindings "user" = user.val := look huserZ
    have hmat22 : lookupValue st22.bindings "market_maturity" = mat := look hmatZ
    have hw22 : st22.world = world := by simp [st22, withBind, hwZ]
    rw [show withBind stZ "_verity_slice_tmp_22" 0 = st22 from rfl]
    exact cont_after_pspf oracle world id user mat ts credit llf lf pending lastAccrual psc pspf st22
      hw22 hid22 huser22 hmat22 hpsc22 htmp22 hcreditU hpendingU hlaU htsM hmatM hpscLe hpspfLe
      htseq hlaRead hpce hpspfE

set_option maxHeartbeats 8000000

/-- Successful or reverting, the imported body returns the words of `viewResult?`. -/
theorem exec_view (oracle : DenoteOracle) (world : Verity.ContractState)
    (maturity : Uint256) (id : BytesN 32) (user : Address)
    (hord : (midnight.position.lastLossFactor oracle world id user).val ≤
      (midnight.marketState.lossFactor oracle world id).val) :
    runFunction oracle midnight.model "updatePositionView" world
      [("market_maturity", maturity.val), ("id", id.val), ("user", user.val)] =
      (viewResult?
        (midnight.position.credit oracle world id user).val
        (midnight.position.lastLossFactor oracle world id user).val
        (midnight.marketState.lossFactor oracle world id).val
        (midnight.position.pendingFee oracle world id user).val
        (midnight.position.lastAccrual oracle world id user).val
        world.blockTimestamp.val maturity.val).map (fun p => [p.1, p.2.1, p.2.2]) := by
  -- Storage words are uint128, timestamps are words.
  let credit := (midnight.position.credit oracle world id user).val
  let llf := (midnight.position.lastLossFactor oracle world id user).val
  let lf := (midnight.marketState.lossFactor oracle world id).val
  let pending := (midnight.position.pendingFee oracle world id user).val
  let lastAccrual := (midnight.position.lastAccrual oracle world id user).val
  let ts := world.blockTimestamp.val
  let mat := maturity.val
  have hcreditU : credit ≤ U := uint128_le_U (midnight.position.credit oracle world id user)
  have hllfU : llf ≤ U := uint128_le_U (midnight.position.lastLossFactor oracle world id user)
  have hlfU : lf ≤ U := uint128_le_U (midnight.marketState.lossFactor oracle world id)
  have hpendingU : pending ≤ U := uint128_le_U (midnight.position.pendingFee oracle world id user)
  have hlaU : lastAccrual ≤ U := uint128_le_U (midnight.position.lastAccrual oracle world id user)
  have htsM : ts < MOD := by
    simpa [ts, MOD, Uint256.modulus, UINT256_MODULUS] using world.blockTimestamp.isLt
  have hmatM : mat < MOD := by
    simpa [mat, MOD, Uint256.modulus, UINT256_MODULUS] using maturity.isLt
  have hcreditM : credit < MOD := le_U_lt_MOD hcreditU
  have hllfM : llf < MOD := le_U_lt_MOD hllfU
  have hlfM : lf < MOD := le_U_lt_MOD hlfU
  have hpendingM : pending < MOD := le_U_lt_MOD hpendingU
  have hlaM : lastAccrual < MOD := le_U_lt_MOD hlaU
  have hord' : llf ≤ lf := hord
  -- Unfold the call down to the statement list.
  unfold runFunction
  have hbody : functionBody midnight.model "updatePositionView" = body := rfl
  rw [hbody]
  -- The initial state is `start`.
  have hstart : ({ world, bindings := [("market_maturity", mat), ("id", id.val), ("user", user.val)] } : DenoteState) =
      start world mat id.val user.val := by
    simp [start, argEnv, mat]
  rw [hstart]
  let st0 := start world mat id.val user.val
  have hid0 : lookupValue st0.bindings "id" = id.val := lookup_argEnv_id _ _ _
  have huser0 : lookupValue st0.bindings "user" = user.val := lookup_argEnv_user _ _ _
  have hmat0 : lookupValue st0.bindings "market_maturity" = mat := lookup_argEnv_maturity _ _ _
  -- credit, lastLossFactor, the branch bit, and a zero accumulator.
  have hw0 : st0.world = world := by simp [st0, start]
  have h0 : body = .letVar "_credit"
      (.structMember2 "position" (.param "id") (.param "user") "credit") :: body.drop 1 := by rfl
  have hcE := eval_credit oracle st0 id user hid0 huser0
  rw [hw0] at hcE
  rw [h0, exec_let hcE]
  let st1 := withBind st0 "_credit" credit
  have hid1 : lookupValue st1.bindings "id" = id.val := look hid0
  have huser1 : lookupValue st1.bindings "user" = user.val := look huser0
  have hmat1 : lookupValue st1.bindings "market_maturity" = mat := look hmat0
  have hcredit1 : lookupValue st1.bindings "_credit" = credit := lookup_wb_eq _ _ _
  have hw1 : st1.world = world := by simp [st1, withBind, hw0]
  have h1 : body.drop 1 = .letVar "_lastLossFactor"
      (.structMember2 "position" (.param "id") (.param "user") "lastLossFactor") :: body.drop 2 := by rfl
  have hllE := eval_llf oracle st1 id user hid1 huser1
  rw [hw1] at hllE
  rw [h1, exec_let hllE]
  let st2 := withBind st1 "_lastLossFactor" llf
  have hid2 : lookupValue st2.bindings "id" = id.val := look hid1
  have huser2 : lookupValue st2.bindings "user" = user.val := look huser1
  have hmat2 : lookupValue st2.bindings "market_maturity" = mat := look hmat1
  have hcredit2 : lookupValue st2.bindings "_credit" = credit := look hcredit1
  have hllf2 : lookupValue st2.bindings "_lastLossFactor" = llf := lookup_wb_eq _ _ _
  have h2 : body.drop 2 = .letVar "_verity_slice_tmp_0"
      (.lt (.localVar "_lastLossFactor") (.literal U)) :: body.drop 3 := by rfl
  rw [h2, exec_let (eval_lt (eval_local_eq hllf2) (eval_literal U_lt))]
  let bit := boolWord (decide (llf < U))
  let st3 := withBind st2 "_verity_slice_tmp_0" bit
  have hid3 : lookupValue st3.bindings "id" = id.val := look hid2
  have huser3 : lookupValue st3.bindings "user" = user.val := look huser2
  have hmat3 : lookupValue st3.bindings "market_maturity" = mat := look hmat2
  have hcredit3 : lookupValue st3.bindings "_credit" = credit := look hcredit2
  have hllf3 : lookupValue st3.bindings "_lastLossFactor" = llf := look hllf2
  have hbit3 : lookupValue st3.bindings "_verity_slice_tmp_0" = bit := lookup_wb_eq _ _ _
  have h3 : body.drop 3 = .letVar "_verity_slice_tmp_9" (.literal 0) :: body.drop 4 := by rfl
  rw [h3, exec_let (eval_literal zero_lt_mod)]
  let st4 := withBind st3 "_verity_slice_tmp_9" 0
  have hid4 : lookupValue st4.bindings "id" = id.val := look hid3
  have hcredit4 : lookupValue st4.bindings "_credit" = credit := look hcredit3
  have hllf4 : lookupValue st4.bindings "_lastLossFactor" = llf := look hllf3
  have hbit4 : lookupValue st4.bindings "_verity_slice_tmp_0" = bit := look hbit3
  have hmat4 : lookupValue st4.bindings "market_maturity" = mat := look hmat3
  have huser4 : lookupValue st4.bindings "user" = user.val := look huser3
  have h4 : body.drop 4 =
      .ite (iteAt body 4).1 (iteAt body 4).2.1 (iteAt body 4).2.2 :: body.drop 5 := by rfl
  have hcond : (iteAt body 4).1 = .localVar "_verity_slice_tmp_0" := by rfl
  rw [h4, hcond, exec_ite (eval_local_eq hbit4)]
  -- Both branches store `postSlashCredit` in tmp9, then statement 5 copies it.
  let psc := if llf < U then (credit * (U - lf)) / (U - llf) else 0
  have hpce : postSlashCredit? credit llf lf = some psc := by
    rw [postSlashCredit_eq hcreditU hllfU hlfU]
  by_cases hlt : llf < U
  · have hbit1 : bit = 1 := by simp [bit, boolWord, hlt]
    simp only [hbit1, show ((1 : Nat) = 0) = False by decide, if_false]
    -- then-branch
    have hth : (iteAt body 4).2.1 ++ body.drop 5 =
        .letVar "_verity_slice_tmp_1" (.structMember "marketState" (.param "id") "lossFactor") ::
        ((iteAt body 4).2.1.drop 1 ++ body.drop 5) := by rfl
    have hw4 : st4.world = world := by simp [st4, st3, st2, st1, withBind, hw0]
    have hloss := eval_loss oracle st4 id hid4
    rw [hw4] at hloss
    rw [hth, exec_let hloss]
    let stL := withBind st4 "_verity_slice_tmp_1" lf
    have hlfL : lookupValue stL.bindings "_verity_slice_tmp_1" = lf := lookup_wb_eq _ _ _
    have hcreditL : lookupValue stL.bindings "_credit" = credit := look hcredit4
    have hllfL : lookupValue stL.bindings "_lastLossFactor" = llf := look hllf4
    have hidL : lookupValue stL.bindings "id" = id.val := look hid4
    have huserL : lookupValue stL.bindings "user" = user.val := look huser4
    have hmatL : lookupValue stL.bindings "market_maturity" = mat := look hmat4
    have hsub1 : (iteAt body 4).2.1.drop 1 =
        csubBlock "_verity_slice_tmp_2" (.literal U) (.localVar "_verity_slice_tmp_1") ++
          (iteAt body 4).2.1.drop 3 := by rfl
    have hlf0 : lookupValue (withBind stL "_verity_slice_tmp_2" 0).bindings "_verity_slice_tmp_1" = lf :=
      look hlfL
    rw [hsub1, List.append_assoc, exec_csubBlock (eval_literal U_lt) (eval_local_eq hlf0) U_lt hlfM]
    have hc1 : csub? U lf = some (U - lf) := by simp [csub?, hlfU]
    simp only [hc1]
    let stM := withBind stL "_verity_slice_tmp_2" (U - lf)
    have hmfM : lookupValue stM.bindings "_verity_slice_tmp_2" = U - lf := lookup_wb_eq _ _ _
    have hcreditLook : lookupValue stM.bindings "_credit" = credit := look hcreditL
    have hllfM2 : lookupValue stM.bindings "_lastLossFactor" = llf := look hllfL
    have h3' : (iteAt body 4).2.1.drop 3 =
        .letVar "_verity_slice_tmp_4" (.localVar "_verity_slice_tmp_2") ::
          (iteAt body 4).2.1.drop 4 := by rfl
    rw [h3', List.cons_append, exec_let (eval_local_eq hmfM)]
    let st4' := withBind stM "_verity_slice_tmp_4" (U - lf)
    have htmp4 : lookupValue st4'.bindings "_verity_slice_tmp_4" = U - lf := lookup_wb_eq _ _ _
    have hllf4' : lookupValue st4'.bindings "_lastLossFactor" = llf := look hllfM2
    have hcredit4' : lookupValue st4'.bindings "_credit" = credit := look hcreditLook
    have hsub2 : (iteAt body 4).2.1.drop 4 =
        csubBlock "_verity_slice_tmp_3" (.literal U) (.localVar "_lastLossFactor") ++
          (iteAt body 4).2.1.drop 6 := by rfl
    have hll0 : lookupValue (withBind st4' "_verity_slice_tmp_3" 0).bindings "_lastLossFactor" = llf :=
      look hllf4'
    rw [hsub2, List.append_assoc, exec_csubBlock (eval_literal U_lt) (eval_local_eq hll0) U_lt hllfM]
    have hc2 : csub? U llf = some (U - llf) := by simp [csub?, hllfU]
    simp only [hc2]
    let stD := withBind st4' "_verity_slice_tmp_3" (U - llf)
    have htmp3 : lookupValue stD.bindings "_verity_slice_tmp_3" = U - llf := lookup_wb_eq _ _ _
    have htmp4d : lookupValue stD.bindings "_verity_slice_tmp_4" = U - lf := look htmp4
    have hcreditD : lookupValue stD.bindings "_credit" = credit := look hcredit4'
    have h6 : (iteAt body 4).2.1.drop 6 =
        .letVar "_verity_slice_tmp_5" (.localVar "_verity_slice_tmp_3") ::
          (iteAt body 4).2.1.drop 7 := by rfl
    rw [h6, List.cons_append, exec_let (eval_local_eq htmp3)]
    let st5 := withBind stD "_verity_slice_tmp_5" (U - llf)
    have htmp5 : lookupValue st5.bindings "_verity_slice_tmp_5" = U - llf := lookup_wb_eq _ _ _
    have htmp4s : lookupValue st5.bindings "_verity_slice_tmp_4" = U - lf := look htmp4d
    have hcreditS : lookupValue st5.bindings "_credit" = credit := look hcreditD
    have hmulb : (iteAt body 4).2.1.drop 7 =
        cmulBlock "_verity_slice_tmp_6" (.localVar "_credit") (.localVar "_verity_slice_tmp_4") ++
          (iteAt body 4).2.1.drop 9 := by rfl
    have hcz : lookupValue (withBind st5 "_verity_slice_tmp_6" 0).bindings "_credit" = credit := look hcreditS
    have hmz : lookupValue (withBind st5 "_verity_slice_tmp_6" 0).bindings "_verity_slice_tmp_4" = U - lf :=
      look htmp4s
    have hmfLt : U - lf < MOD := le_U_lt_MOD (by omega)
    rw [hmulb, List.append_assoc, exec_cmulBlock (eval_local_eq hcz) (eval_local_eq hmz) hcreditM hmfLt]
    have hprod : credit * (U - lf) < MOD := mul_bound hcreditU (by omega)
    have hcm : cmul? credit (U - lf) = some (credit * (U - lf)) := by simp [cmul?, hprod]
    simp only [hcm]
    let stP := withBind st5 "_verity_slice_tmp_6" (credit * (U - lf))
    have htmp6 : lookupValue stP.bindings "_verity_slice_tmp_6" = credit * (U - lf) := lookup_wb_eq _ _ _
    have htmp5p : lookupValue stP.bindings "_verity_slice_tmp_5" = U - llf := look htmp5
    have h9 : (iteAt body 4).2.1.drop 9 =
        .letVar "_verity_slice_tmp_7" (.localVar "_verity_slice_tmp_6") ::
          (iteAt body 4).2.1.drop 10 := by rfl
    rw [h9, List.cons_append, exec_let (eval_local_eq htmp6)]
    let st7 := withBind stP "_verity_slice_tmp_7" (credit * (U - lf))
    have htmp7 : lookupValue st7.bindings "_verity_slice_tmp_7" = credit * (U - lf) := lookup_wb_eq _ _ _
    have htmp5q : lookupValue st7.bindings "_verity_slice_tmp_5" = U - llf := look htmp5p
    have hdivb : (iteAt body 4).2.1.drop 10 =
        cdivBlock "_verity_slice_tmp_8" (.localVar "_verity_slice_tmp_7") (.localVar "_verity_slice_tmp_5") ++
          (iteAt body 4).2.1.drop 12 := by rfl
    have hn0 : lookupValue (withBind st7 "_verity_slice_tmp_8" 0).bindings "_verity_slice_tmp_7" =
        credit * (U - lf) := look htmp7
    have hd0 : lookupValue (withBind st7 "_verity_slice_tmp_8" 0).bindings "_verity_slice_tmp_5" = U - llf :=
      look htmp5q
    have hdivN : U - llf ≠ 0 := by omega
    have hdivM : U - llf < MOD := le_U_lt_MOD (by omega)
    have hprodM : credit * (U - lf) < MOD := hprod
    rw [hdivb, List.append_assoc, exec_cdivBlock (eval_local_eq hn0) (eval_local_eq hd0) hprodM hdivM]
    have hcd : cdiv? (credit * (U - lf)) (U - llf) = some ((credit * (U - lf)) / (U - llf)) := by
      simp [cdiv?, hdivN]
    simp only [hcd]
    let quot := (credit * (U - lf)) / (U - llf)
    let stQ := withBind st7 "_verity_slice_tmp_8" quot
    have htmp8 : lookupValue stQ.bindings "_verity_slice_tmp_8" = quot := lookup_wb_eq _ _ _
    have h12 : (iteAt body 4).2.1.drop 12 ++ body.drop 5 =
        .assignVar "_verity_slice_tmp_9" (.localVar "_verity_slice_tmp_8") :: body.drop 5 := by rfl
    rw [h12, exec_assign (eval_local_eq htmp8)]
    let st9 := withBind stQ "_verity_slice_tmp_9" quot
    have htmp9 : lookupValue st9.bindings "_verity_slice_tmp_9" = quot := lookup_wb_eq _ _ _
    have hpscQ : psc = quot := by simp [psc, hlt, quot]
    have hid9 : lookupValue st9.bindings "id" = id.val := by
      simp only [st9, stQ, st7, stP, st5, stD, st4', stM, stL, withBind]
      repeat rw [lookupValue_bind_ne (by decide)]
      exact hid4
    have huser9 : lookupValue st9.bindings "user" = user.val := by
      simp only [st9, stQ, st7, stP, st5, stD, st4', stM, stL, withBind]
      repeat rw [lookupValue_bind_ne (by decide)]
      exact huser4
    have hmat9 : lookupValue st9.bindings "market_maturity" = mat := by
      simp only [st9, stQ, st7, stP, st5, stD, st4', stM, stL, withBind]
      repeat rw [lookupValue_bind_ne (by decide)]
      exact hmat4
    have hcredit9 : lookupValue st9.bindings "_credit" = credit := by
      simp only [st9, stQ, st7, stP, st5, stD, st4', stM, stL, withBind]
      repeat rw [lookupValue_bind_ne (by decide)]
      exact hcredit4
    have hw9 : st9.world = world := by
      simpa [st9, stQ, st7, stP, st5, stD, st4', stM, stL, withBind] using hw4
    have hformula : quot = if llf < U then (credit * (U - lf)) / (U - llf) else 0 := by
      simp [hlt, quot]
    rw [show withBind stQ "_verity_slice_tmp_9" quot = st9 from rfl]
    have hfinish :=
      cont_from_tmp9 oracle world id user mat ts credit llf lf pending lastAccrual quot st9
        hw9 hid9 huser9 hmat9 hcredit9 htmp9 hcreditU hllfU hlfU hpendingU hlaU htsM hmatM hord'
        rfl rfl rfl hformula
    exact hfinish
  · have hbit0 : bit = 0 := by
      simp [bit, boolWord, hlt]
    simp only [hbit0, if_true]
    have helse : (iteAt body 4).2.2 ++ body.drop 5 =
        .assignVar "_verity_slice_tmp_9" (.literal 0) :: body.drop 5 := by rfl
    rw [helse, exec_assign (eval_literal zero_lt_mod)]
    let st9 := withBind st4 "_verity_slice_tmp_9" 0
    have htmp9 : lookupValue st9.bindings "_verity_slice_tmp_9" = 0 := lookup_wb_eq _ _ _
    have hpsc0 : psc = 0 := by simp [psc, hlt]
    have hid9 : lookupValue st9.bindings "id" = id.val := look hid4
    have huser9 : lookupValue st9.bindings "user" = user.val := look huser4
    have hmat9 : lookupValue st9.bindings "market_maturity" = mat := look hmat4
    have hcredit9 : lookupValue st9.bindings "_credit" = credit := look hcredit4
    have hw9 : st9.world = world := by simp [st9, st4, st3, st2, st1, withBind, hw0]
    have hformula : (0 : Nat) = if llf < U then (credit * (U - lf)) / (U - llf) else 0 := by
      simp [hlt]
    rw [show withBind st4 "_verity_slice_tmp_9" 0 = st9 from rfl]
    have hfinish :=
      cont_from_tmp9 oracle world id user mat ts credit llf lf pending lastAccrual 0 st9
        hw9 hid9 huser9 hmat9 hcredit9 htmp9 hcreditU hllfU hlfU hpendingU hlaU htsM hmatM hord'
        rfl rfl rfl hformula
    exact hfinish

end Midnight.Lemmas
