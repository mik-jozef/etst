import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.RulesOfInference

namespace Etst


namespace Expr
  def clearBvars (max := 0): Expr E sig → Expr E sig
    | .var info x => .var info x
    | .bvar x => if x < max then .bvar x else .none
    | .op o args => .op o (fun p => (args p).clearBvars max)
    | .compl e => .compl (e.clearBvars max)
    | .arbUn body => .arbUn (body.clearBvars (max + 1))
    | .arbIr body => .arbIr (body.clearBvars (max + 1))
  
  def clearBvars_eq_bvar
    {max: Nat}
    (lt: x < max)
  :
    clearBvars (E := E) (sig := sig) max (.bvar x) = .bvar x
  :=
    if_pos lt
  
  def clearBvars_eq_none
    {max: Nat}
    (nlt: ¬ x < max)
  :
    clearBvars (E := E) (sig := sig) max (.bvar x) = none
  :=
    if_neg nlt
  
  def clearBvars_none_eq_none
  :
    clearBvars (E := E) (sig := sig) n none = none
  :=
    show (if 0 < n + 1 then bvar 0 else none).arbUn.compl = none from
    if_pos (Nat.zero_lt_succ n) ▸ rfl
  
  def clearBvars_idempotent (expr: Expr E sig):
    (expr.clearBvars n).clearBvars n = expr.clearBvars n
  :=
    match expr with
    | .var _ _ => rfl
    | .bvar x =>
      if h: x < n then by
        rw [clearBvars_eq_bvar h, clearBvars_eq_bvar h]
      else by
        rw [clearBvars_eq_none h]
        exact clearBvars_none_eq_none
    | .op o args =>
      congrArg
        (Expr.op o)
        (funext fun param => (args param).clearBvars_idempotent)
    | .compl body =>
      congrArg Expr.compl body.clearBvars_idempotent
    | .arbUn body =>
      congrArg Expr.arbUn (body.clearBvars_idempotent)
    | .arbIr body =>
      congrArg Expr.arbIr (body.clearBvars_idempotent)
  
  def IsClean (expr: Expr E sig): Prop :=
    expr = expr.clearBvars
  
  def clearBvars_isClean (expr: Expr E sig):
    IsClean expr.clearBvars
  :=
    (clearBvars_idempotent expr).symm
  
end Expr

namespace SingleLaneExpr
  open Expr
  
  def clearBvars_preserves_interp_bv
    (expr: SingleLaneExpr sig)
    (bv bvRest: List salg.D)
    (b c: Valuation salg.D)
  :
    Eq
      (expr.interpretation salg bv b c)
      (interpretation salg (bv ++ bvRest) b c (expr.clearBvars bv.length))
  :=
    match expr with
    | .var _ _ => rfl
    | .bvar x =>
      if h: x < bv.length then
        let ltExtra: x < (bv ++ bvRest).length := 
          h.trans_le (bv.length_le_append_rite bvRest)
        let eq: clearBvars bv.length (bvar x) = bvar x :=
          clearBvars_eq_bvar h
        by
        rw [interp_bvar_eq_of_lt h, eq]
        rw [interp_bvar_eq_of_lt ltExtra]
        rw [bv.getElem_append_left h]
      else
        clearBvars_eq_none h ▸
        SingleLaneExpr.interp_bvar_eq_empty h ▸
        SingleLaneExpr.interp_none_eq_empty.symm
    | .op _ args =>
      eq_op_of_eq (fun param =>
        clearBvars_preserves_interp_bv (args param) bv bvRest b c)
    | .compl body =>
      let ih := clearBvars_preserves_interp_bv body bv bvRest b b
      eq_compl_of_eq c c ih
    | .arbUn body =>
      eq_arbUn_of_eq (fun dX =>
        clearBvars_preserves_interp_bv body (dX :: bv) bvRest b c)
    | .arbIr body =>
      eq_arbIr_of_eq (fun dX =>
        clearBvars_preserves_interp_bv (bvRest := bvRest) body (dX :: bv) b c)
  
  def clearBvars_preserves_interp
    (expr: SingleLaneExpr sig)
    (bv: List salg.D)
    (b c: Valuation salg.D)
  :
    Eq
      (expr.interpretation salg [] b c)
      (SingleLaneExpr.interpretation salg bv b c expr.clearBvars)
  :=
    clearBvars_preserves_interp_bv expr [] bv b c
  
  namespace IsClean
    def bvar_independent
      {expr: SingleLaneExpr sig}
      (isClean: expr.IsClean)
      (bv0 bv1: List salg.D)
      (b c: Valuation salg.D)
    :
      expr.interpretation salg bv0 b c = expr.interpretation salg bv1 b c
    :=
      isClean ▸
      clearBvars_preserves_interp expr bv0 b c ▸
      clearBvars_preserves_interp expr bv1 b c ▸
      rfl

    def changeBv
      {expr: SingleLaneExpr sig}
      (isClean: IsClean expr)
      {bv1: List salg.D}
      (dInExpr: expr.interpretation salg bv0 b c d)
    :
      expr.interpretation salg bv1 b c d
    :=
      bvar_independent isClean bv0 bv1 b c ▸ dInExpr
    
  end IsClean
end SingleLaneExpr

namespace BasicExpr
  def clearBvars_lane_comm
    (expr: BasicExpr sig)
    (lane: SingleLaneVarType)
    (i: Nat := 0)
  :
    Eq
      (Expr.clearBvars i (expr.toLane lane))
      (BasicExpr.toLane (Expr.clearBvars i expr) lane)
  :=
    match expr with
    | .var x => rfl
    | .bvar x => by
      show
        Eq
          (Expr.clearBvars i (.bvar x))
          (toLane (Expr.clearBvars i (.bvar x)) lane)
      if h: x < i then
        rw [Expr.clearBvars_eq_bvar h, Expr.clearBvars_eq_bvar h]
        rfl
      else
        rw [Expr.clearBvars_eq_none h, Expr.clearBvars_eq_none h]
        rfl
    | .op o args =>
      congrArg
        (SingleLaneExpr.op o)
        (funext fun param =>
          clearBvars_lane_comm (args param) lane i)
    | .compl body =>
      congrArg
        SingleLaneExpr.compl
        (clearBvars_lane_comm body lane.toggle i)
    | .arbUn body =>
      congrArg
        SingleLaneExpr.arbUn
        (clearBvars_lane_comm body lane (i + 1))
    | .arbIr body =>
      congrArg
        SingleLaneExpr.arbIr
        (clearBvars_lane_comm body lane (i + 1))
  
  def clearBvars_preserves_interp
    (expr: BasicExpr sig)
    (bv: List salg.D)
    (b c: Valuation salg.D)
  :
    Eq
      (expr.interpretation salg [] b c)
      (interpretation salg bv b c expr.clearBvars)
  :=
    let eqBvDef := (expr.toLane .defLane).clearBvars_preserves_interp bv b c
    let eqBvPos := (expr.toLane .posLane).clearBvars_preserves_interp bv b c
    Set3.eq
      (eqBvDef.trans (clearBvars_lane_comm expr .defLane ▸ rfl))
      (eqBvPos.trans (clearBvars_lane_comm expr .posLane ▸ rfl))
end BasicExpr
