import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.InterpretationMono

namespace Etst


namespace Expr
  def lift
    (expr: Expr E)
    (depth liftBy: Nat)
  :=
    match expr with
    | var lane x => var lane x
    | bvar x => bvar (if x < depth then x else x + liftBy)
    | null => null
    | pair l r => pair (l.lift depth liftBy) (r.lift depth liftBy)
    | un l r => un (l.lift depth liftBy) (r.lift depth liftBy)
    | ir l r => ir (l.lift depth liftBy) (r.lift depth liftBy)
    | condSome body => condSome (body.lift depth liftBy)
    | condFull body => condFull (body.lift depth liftBy)
    | compl body => compl (body.lift depth liftBy)
    | arbUn body => arbUn (body.lift (depth + 1) liftBy)
    | arbIr body => arbIr (body.lift (depth + 1) liftBy)
  
  def lift_bvar_lt
    (x: Nat)
    (lt: x < depth)
    (liftBy: Nat)
  :
    (bvar (E := E) x).lift depth liftBy = bvar x
  :=
    show bvar _ = _ from if_pos lt ▸ rfl
  
  def lift_bvar_ge
    (x: Nat)
    (ge: x >= depth)
    (liftBy: Nat)
  :
    (bvar (E := E) x).lift depth liftBy = bvar (x + liftBy)
  :=
    show bvar _ = _ from if_neg (not_lt.mpr ge) ▸ rfl
  
  def lift_eq_zero
    (expr: Expr E)
    (depth: Nat)
  :
    expr.lift depth 0 = expr
  :=
    match expr with
    | var _ _ => rfl
    | bvar x =>
        if h: x < depth then
          (lift_bvar_lt x h 0).symm ▸ rfl
        else
          (lift_bvar_ge x (not_lt.mp h) 0).symm ▸ rfl
    | null => rfl
    | pair l r =>
      congrArg₂
        pair
        (l.lift_eq_zero depth)
        (r.lift_eq_zero depth)
    | un l r =>
      congrArg₂
        un
        (l.lift_eq_zero depth)
        (r.lift_eq_zero depth)
    | ir l r =>
      congrArg₂
        ir
        (l.lift_eq_zero depth)
        (r.lift_eq_zero depth)
    | condSome body => congrArg condSome (body.lift_eq_zero depth)
    | condFull body => congrArg condFull (body.lift_eq_zero depth)
    | compl body => congrArg compl (body.lift_eq_zero depth)
    | arbUn body => congrArg arbUn (body.lift_eq_zero depth.succ)
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
    | .var _ _ => rfl
    | .bvar x =>
      show _ = intp2 (.bvar _) _ _ _ from
      if hD: x < bvDepth.length then
        let ltBv2 l: x < (bvDepth ++ l).length :=
          List.length_append ▸
          hD.trans_le (Nat.le_add_right _ _)
        let ltBv3: x < (bvDepth ++ bvLiftBy ++ bv).length :=
          List.append_assoc _ _ _ ▸
          List.length_append ▸
          hD.trans_le (Nat.le_add_right _ _)
        let eqAtX :=
          List.getElem_append_left hD ▸
          List.getElem_append_left (ltBv2 bvLiftBy) ▸
          (List.getElem_append_left hD).symm ▸
          rfl
        if_pos hD ▸
        interp_bvar_eq_of_lt (ltBv2 bv) ▸
        interp_bvar_eq_of_lt ltBv3 ▸
        Set.singleton_eq_singleton_iff.mpr eqAtX
      else if hDB: x < ((bvDepth ++ bv).length) then
        let ltBv3: x + bvLiftBy.length < (bvDepth ++ bvLiftBy ++ bv).length := by
          rw [List.length_append]
          rw [List.length_append]
          rw [Nat.add_assoc _ _ _]
          rw [Nat.add_comm bvLiftBy.length _]
          rw [←Nat.add_assoc _ _ _]
          rw [←List.length_append]
          exact Nat.add_lt_add_right hDB bvLiftBy.length
        let leXLift: (bvDepth ++ bvLiftBy).length ≤ x + bvLiftBy.length :=
          List.length_append ▸
          Nat.add_le_add_right (le_of_not_gt hD) _
        let eqIndex:
          x - bvDepth.length = x + bvLiftBy.length - (bvDepth ++ bvLiftBy).length
        :=
          List.length_append ▸
          Nat.add_sub_add_right x bvLiftBy.length bvDepth.length ▸
          rfl
        let eqAtX :=
          List.getElem_append_right (le_of_not_gt hD) ▸
          List.getElem_append_right (as := bvDepth ++ bvLiftBy) leXLift ▸
          show List.get _ _ = _ from
          congr rfl (Fin.eq_of_val_eq eqIndex)
        if_neg hD ▸
        interp_bvar_eq_of_lt hDB ▸
        interp_bvar_eq_of_lt ltBv3 ▸
        Set.singleton_eq_singleton_iff.mpr eqAtX
      else
        let eq:
          ¬x + bvLiftBy.length < (bvDepth ++ bvLiftBy ++ bv).length
        :=
          List.length_append ▸
          List.length_append.symm ▸
          Nat.add_assoc _ _ _ ▸
          Nat.add_comm bvLiftBy.length bv.length ▸
          Nat.add_assoc _ _ _ ▸
          Nat.not_lt.mpr
            (add_le_add_right
              (le_of_not_gt (List.length_append ▸ hDB))
              bvLiftBy.length)
        if_neg hD ▸
        interp_bvar_eq_empty hDB ▸
        interp_bvar_eq_empty eq ▸
        rfl
    | .null => rfl
    | .pair l r =>
      eq_intp2_pair_of_eq
        (intp2_lift_eq_helper l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_helper r bv bvDepth bvLiftBy b c)
    | .un l r =>
      eq_intp2_un_of_eq
        (intp2_lift_eq_helper l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_helper r bv bvDepth bvLiftBy b c)
    | .ir l r =>
      eq_intp2_ir_of_eq
        (intp2_lift_eq_helper l bv bvDepth bvLiftBy b c)
        (intp2_lift_eq_helper r bv bvDepth bvLiftBy b c)
        | .condSome body =>
      eq_intp2_condSome_of_eq
        (intp2_lift_eq_helper body bv bvDepth bvLiftBy b c)
        | .condFull body =>
      eq_intp2_condFull_of_eq
        (intp2_lift_eq_helper body bv bvDepth bvLiftBy b c)
        | .compl body =>
      eq_compl_of_eq -- TODO normalize the name
        b c
        (intp2_lift_eq_helper body bv bvDepth bvLiftBy b b)
        | .arbUn body =>
      eq_arbUn_of_eq fun d =>
        intp2_lift_eq_helper body bv (d :: bvDepth) bvLiftBy b c
        | .arbIr body =>
      eq_arbIr_of_eq fun d =>
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
