import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.InterpretationMono
import Etst.Subtyping.Utils.ExprConstsVarsSat

namespace Etst


namespace Expr
  def lift
    (expr: Expr E)
    (depth := 0)
    (liftBy := 1)
  :=
    match expr with
    | const info x => const info x
    | var x => var (if x < depth then x else x + liftBy)
    | null => null
    | pair l r => pair (l.lift depth liftBy) (r.lift depth liftBy)
    | ir l r => ir (l.lift depth liftBy) (r.lift depth liftBy)
    | condFull body => condFull (body.lift depth liftBy)
    | compl body => compl (body.lift depth liftBy)
    | arbIr body => arbIr (body.lift (depth + 1) liftBy)
  
  def lift_var_lt
    (x: Nat)
    (lt: x < depth)
    (liftBy: Nat)
  :
    (var (E := E) x).lift depth liftBy = var x
  :=
    show var _ = _ from if_pos lt ▸ rfl
  
  def lift_var_ge
    (x: Nat)
    (ge: x >= depth)
    (liftBy: Nat)
  :
    (var (E := E) x).lift depth liftBy = var (x + liftBy)
  :=
    show var _ = _ from if_neg (not_lt.mpr ge) ▸ rfl
  
  def lift_zero_eq
    (expr: Expr E)
    (depth: Nat)
  :
    expr.lift depth 0 = expr
  :=
    match expr with
    | const _ _ => rfl
    | var x =>
        if h: x < depth then
          (lift_var_lt x h 0).symm ▸ rfl
        else
          (lift_var_ge x (not_lt.mp h) 0).symm ▸ rfl
    | null => rfl
    | pair l r =>
      congrArg₂
        pair
        (l.lift_zero_eq depth)
        (r.lift_zero_eq depth)
    | ir l r =>
      congrArg₂
        ir
        (l.lift_zero_eq depth)
        (r.lift_zero_eq depth)
    | condFull body => congrArg condFull (body.lift_zero_eq depth)
    | compl body => congrArg compl (body.lift_zero_eq depth)
    | arbIr body => congrArg arbIr (body.lift_zero_eq depth.succ)
end Expr

namespace SingleLaneExpr
  def intp2_lift_eq_depth
    (expr: SingleLaneExpr)
    (bv bvDepth bvLiftBy: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 (bvDepth ++ bv) b c)
      (SingleLaneExpr.intp2
        (expr.lift bvDepth.length bvLiftBy.length)
        (bvDepth ++ bvLiftBy ++ bv)
        b
        c)
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => by
      show SingleLaneExpr.intp2Var (bvDepth ++ bv) x = SingleLaneExpr.intp2Var (bvDepth ++ bvLiftBy ++ bv) (if x < bvDepth.length then x else x + bvLiftBy.length)
      unfold SingleLaneExpr.intp2Var
      rw [List.append_assoc]
      split_ifs with h1
      · rw [List.getElem?_append_left h1]
        rw [List.getElem?_append_left h1]
      · rw [List.getElem?_append_right (Nat.le_of_not_lt h1)]
        rw [List.getElem?_append_right (Nat.le_trans (Nat.le_of_not_lt h1) (Nat.le_add_right _ _))]
        rw [List.getElem?_append_right]
        · congr 1
          rw [Nat.sub_sub]
          rw [Nat.add_sub_add_right]
        · rw [Nat.le_sub_iff_add_le (Nat.le_trans (Nat.le_of_not_lt h1) (Nat.le_add_right _ _))]
          rw [Nat.add_comm bvLiftBy.length bvDepth.length]
          exact Nat.add_le_add_right (Nat.le_of_not_lt h1) bvLiftBy.length
    | .null => rfl
    | .pair l r =>
      eq_intp2_pair_of_eq
        (intp2_lift_eq_depth l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_depth r bv bvDepth bvLiftBy b c)
    | .ir l r =>
      eq_intp2_ir_of_eq
        (intp2_lift_eq_depth l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_depth r bv bvDepth bvLiftBy b c)
    | .condFull body =>
      eq_intp2_condFull_of_eq
        (intp2_lift_eq_depth body bv bvDepth bvLiftBy b c)
    | .compl body =>
      eq_intp2_compl_of_eq
        (intp2_lift_eq_depth body bv bvDepth bvLiftBy c b)
    | .arbIr body =>
      eq_intp2_arbIr_of_eq fun d =>
        intp2_lift_eq_depth body bv (d :: bvDepth) bvLiftBy b c
  
  def intp2_lift_eq
    (expr: SingleLaneExpr)
    (bv bvLiftBy: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 bv b c)
      (SingleLaneExpr.intp2
        (expr.lift 0 bvLiftBy.length)
        (bvLiftBy ++ bv)
        b
        c)
  :=
    intp2_lift_eq_depth expr bv [] bvLiftBy b c
  
end SingleLaneExpr


def liftVarMap
  (varMap: Nat → Expr E)
:
  Nat → Expr E
| 0 => .var 0
| n + 1 => (varMap n).lift

def Expr.replaceVars {E}
  (varMap: Nat → Expr E)
:
  Expr E → Expr E
| .const e x => .const e x
| .var x => varMap x
| .null => .null
| .pair left rite =>
  .pair (replaceVars varMap left) (replaceVars varMap rite)
| .ir left rite =>
  .ir (replaceVars varMap left) (replaceVars varMap rite)
| .condFull body =>
  .condFull (replaceVars varMap body)
| .compl body =>
  .compl (replaceVars varMap body)
| .arbIr body =>
  .arbIr (replaceVars (liftVarMap varMap) body)

def Expr.replaceVarsNat {E}
  (varMap: Nat → Nat)
:
  Expr E → Expr E
:=
  replaceVars (fun x => .var (varMap x))

namespace SingleLaneExpr
  def intp2_replaceVars_eq2
    (bvMap: Nat → SingleLaneExpr)
    {expr: SingleLaneExpr}
    {b c: Valuation Pair}
    {bvLeft bvRite}
    (bvEq:
      ∀ x ∈ expr.UsesFreeVar,
        intp2Var bvLeft x = (bvMap x).intp2 bvRite b c)
    (bvEqCpl:
      ∀ x ∈ expr.UsesFreeVar,
        intp2Var bvLeft x = (bvMap x).intp2 bvRite c b)
  :
    Eq
      (expr.intp2 bvLeft b c)
      (intp2 (expr.replaceVars bvMap) bvRite b c)
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => bvEq x rfl
    | .null => rfl
    | .pair _ _ =>
      eq_intp2_pair_of_eq
        (intp2_replaceVars_eq2
          bvMap
          (fun x h => bvEq x (Or.inl h))
          (fun x h => bvEqCpl x (Or.inl h)))
        (intp2_replaceVars_eq2
          bvMap
          (fun x h => bvEq x (Or.inr h))
          (fun x h => bvEqCpl x (Or.inr h)))
    | .ir _ _ =>
      eq_intp2_ir_of_eq
        (intp2_replaceVars_eq2
          bvMap
          (fun x h => bvEq x (Or.inl h))
          (fun x h => bvEqCpl x (Or.inl h)))
        (intp2_replaceVars_eq2
          bvMap
          (fun x h => bvEq x (Or.inr h))
          (fun x h => bvEqCpl x (Or.inr h)))
    | .condFull body =>
      eq_intp2_condFull_of_eq
        (intp2_replaceVars_eq2 (expr := body) bvMap bvEq bvEqCpl)
    | .compl body =>
      eq_intp2_compl_of_eq
        (intp2_replaceVars_eq2 (expr := body) bvMap bvEqCpl bvEq)
    | .arbIr body =>
      let bvMap': Nat → SingleLaneExpr := liftVarMap bvMap
      let bvEqLifted {b c}
        (hyp:
          ∀ x ∈ (arbIr body).UsesFreeVar,
            intp2Var bvLeft x = (bvMap x).intp2 bvRite b c)
        (d: Pair)
        (x: Nat)
        (h: x ∈ body.UsesFreeVar)
      :
        intp2Var (d :: bvLeft) x = (bvMap' x).intp2 (d :: bvRite) b c
      :=
        match x with
        | 0 => rfl
        | x + 1 =>
          intp2_lift_eq (bvMap x) bvRite [d] b c ▸ hyp x h
      
      eq_intp2_arbIr_of_eq fun d =>
        intp2_replaceVars_eq2
          bvMap'
          (bvEqLifted bvEq d)
          (bvEqLifted bvEqCpl d)
  
  def intp2_replaceVars_eq
    (bvMap: Nat → SingleLaneExpr)
    {expr: SingleLaneExpr}
    {bvLeft bvRite v}
    (bvEq:
      ∀ x ∈ expr.UsesFreeVar,
        intp2Var bvLeft x = (bvMap x).intp2 bvRite v v)
  :
    Eq
      (expr.intp2 bvLeft v v)
      (intp2 (expr.replaceVars bvMap) bvRite v v)
  :=
    intp2_replaceVars_eq2 bvMap bvEq bvEq
  
  def intp2_replaceVarsNat_eq
    (bvMap: Nat → Nat)
    {expr: SingleLaneExpr}
    {b c: Valuation Pair}
    {bvLeft bvRite}
    (bvEq: ∀ x ∈ expr.UsesFreeVar, bvLeft[x]? = bvRite[bvMap x]?)
  :
    Eq
      (expr.intp2 bvLeft b c)
      (intp2 (expr.replaceVarsNat bvMap) bvRite b c)
  :=
    (fun ab a => ab a a)
      (intp2_replaceVars_eq2 (fun x => .var (bvMap x)))
      (fun x hx =>
        congrArg
          (fun | none => (∅: Set Pair) | some d => {d})
          (bvEq x hx))
  
end SingleLaneExpr
