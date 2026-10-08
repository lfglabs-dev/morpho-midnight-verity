import Midnight.Spec
import Compiler.SolidityImport.Proofs
import Compiler.SolidityImport.Access

/-!
Shared setup for the `updatePositionViewProperties` proof: body slices and
`splitAfter` append facts.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
open Verity.Core

namespace Midnight.Lemmas

export SolidityImport (max128 max128_lt word_of_small sub_word mul_word128 div_word mask_eq
  mask_le mask_bounded splitAfter split_prefix split_prefix_continue list_frame ends_return
  prefixList exec_append exec_let_cons lookup_bind_same lookup_bind_other
  evalExpr_structMember2_param evalExpr_structMember_param functionBody runFunction
  readMember ofNat_val)

theorem splitAfter_append (name : String) (ss : List Stmt) :
    (splitAfter name ss).1 ++ (splitAfter name ss).2 = ss := by
  induction ss with
  | nil => rfl
  | cons stmt rest ih =>
    cases stmt with
    | letVar n e =>
      simp only [splitAfter]
      split <;> simp [ih]
    | _ =>
      simp only [splitAfter, List.cons_append, ih]

def endsWithReturnValues : List Stmt → Bool
  | [] => false
  | [.returnValues _] => true
  | [_] => false
  | _ :: rest => endsWithReturnValues rest

def returnArgsOf : List Stmt → List Expr
  | [] => []
  | [.returnValues args] => args
  | [_] => []
  | _ :: rest => returnArgsOf rest

def dropLastStmt : List Stmt → List Stmt
  | [] => []
  | [_] => []
  | s :: rest => s :: dropLastStmt rest

theorem endsWithReturnValues_split (ss : List Stmt) (h : endsWithReturnValues ss = true) :
    ss = dropLastStmt ss ++ [.returnValues (returnArgsOf ss)] := by
  induction ss with
  | nil => simp [endsWithReturnValues] at h
  | cons s rest ih =>
    cases rest with
    | nil =>
      cases s with
      | returnValues args => simp [dropLastStmt, returnArgsOf]
      | _ => simp [endsWithReturnValues] at h
    | cons t rest' =>
      have h' : endsWithReturnValues (t :: rest') = true := by
        simpa [endsWithReturnValues] using h
      have ih' := ih h'
      change s :: t :: rest' =
        dropLastStmt (s :: t :: rest') ++ [Stmt.returnValues (returnArgsOf (s :: t :: rest'))]
      simp only [dropLastStmt, returnArgsOf]
      refine Eq.trans (congrArg (s :: ·) ih') ?_
      simp only [List.cons_append]

def body : List Stmt := functionBody midnight.model "updatePositionView"

def preCredit : List Stmt := (splitAfter "postSlashCredit" body).1
def restAfterCredit : List Stmt := (splitAfter "postSlashCredit" body).2
def midPending : List Stmt := (splitAfter "postSlashPendingFee" restAfterCredit).1
def restAfterPending : List Stmt := (splitAfter "postSlashPendingFee" restAfterCredit).2
def midFee : List Stmt := (splitAfter "fee" restAfterPending).1
def postFee : List Stmt := (splitAfter "fee" restAfterPending).2
def postFeePre : List Stmt := dropLastStmt postFee
def retArgs : List Expr := returnArgsOf postFee

theorem body_eq_parts :
    body = preCredit ++ midPending ++ midFee ++ postFee := by
  have h1 : preCredit ++ restAfterCredit = body :=
    splitAfter_append "postSlashCredit" body
  have h2 : midPending ++ restAfterPending = restAfterCredit :=
    splitAfter_append "postSlashPendingFee" restAfterCredit
  have h3 : midFee ++ postFee = restAfterPending :=
    splitAfter_append "fee" restAfterPending
  rw [← h1, ← h2, ← h3]
  simp only [List.append_assoc]

theorem postFee_ends : endsWithReturnValues postFee = true := by decide

theorem postFee_eq_pre_return :
    postFee = postFeePre ++ [.returnValues retArgs] :=
  endsWithReturnValues_split postFee postFee_ends

theorem body_eq_parts_return :
    body = preCredit ++ midPending ++ midFee ++ postFeePre ++ [.returnValues retArgs] := by
  rw [body_eq_parts, postFee_eq_pre_return]
  change preCredit ++ midPending ++ (midFee ++ (postFeePre ++ [Stmt.returnValues retArgs])) =
    (((preCredit ++ midPending) ++ midFee) ++ postFeePre) ++ [Stmt.returnValues retArgs]
  simp only [List.append_assoc]

theorem preCredit_prefix : prefixList [] preCredit = true := by decide
theorem midPending_prefix : prefixList [] midPending = true := by decide
theorem midFee_prefix : prefixList [] midFee = true := by decide
theorem midFee_frames_postSlash :
    prefixList ["postSlashCredit", "postSlashPendingFee"] midFee = true := by decide
theorem midFee_frames_inputs :
    prefixList
      ["postSlashCredit", "postSlashPendingFee", "_credit", "_pendingFee", "_lastLossFactor"]
      midFee = true := by decide
theorem postFeePre_prefix : prefixList [] postFeePre = true := by decide
theorem full_pre_return_prefix :
    prefixList [] (preCredit ++ midPending ++ midFee ++ postFeePre) = true := by decide

/-- Initial bindings of a call to `updatePositionView`. -/
def callBindings (obligationMaturity : Uint256) (id : BytesN 32) (user : Address) : Env :=
  [("market_maturity", Word.toWord obligationMaturity),
   ("id", Word.toWord id),
   ("user", Word.toWord user)]

theorem position_credit_ready :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome ∧
      (findMember midnight.model "position" "credit").isSome := by decide

theorem position_lastLossFactor_ready :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome ∧
      (findMember midnight.model "position" "lastLossFactor").isSome := by decide

theorem position_pendingFee_ready :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome ∧
      (findMember midnight.model "position" "pendingFee").isSome := by decide

theorem position_lastAccrual_ready :
    (findFieldWithResolvedSlot midnight.model.fields "position").isSome ∧
      (findMember midnight.model "position" "lastAccrual").isSome := by decide

theorem marketState_lossFactor_ready :
    (findFieldWithResolvedSlot midnight.model.fields "marketState").isSome ∧
      (findMember midnight.model "marketState" "lossFactor").isSome := by decide

end Midnight.Lemmas
