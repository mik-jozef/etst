import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.InterpretationMono

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
  
  def lift_eq_zero
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
        (l.lift_eq_zero depth)
        (r.lift_eq_zero depth)
    | ir l r =>
      congrArg₂
        ir
        (l.lift_eq_zero depth)
        (r.lift_eq_zero depth)
    | condFull body => congrArg condFull (body.lift_eq_zero depth)
    | compl body => congrArg compl (body.lift_eq_zero depth)
    | arbIr body => congrArg arbIr (body.lift_eq_zero depth.succ)
end Expr

namespace SingleLaneExpr
  def intp2_lift_eq_helper
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
        (intp2_lift_eq_helper l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_helper r bv bvDepth bvLiftBy b c)
    | .ir l r =>
      eq_intp2_ir_of_eq
        (intp2_lift_eq_helper l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_helper r bv bvDepth bvLiftBy b c)
    | .condFull body =>
      eq_intp2_condFull_of_eq
        (intp2_lift_eq_helper body bv bvDepth bvLiftBy b c)
    | .compl body =>
      eq_intp2_compl_of_eq
        (intp2_lift_eq_helper body bv bvDepth bvLiftBy c b)
    | .arbIr body =>
      eq_intp2_arbIr_of_eq fun d =>
        intp2_lift_eq_helper body bv (d :: bvDepth) bvLiftBy b c
  
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
    intp2_lift_eq_helper expr bv [] bvLiftBy b c
  
end SingleLaneExpr
