import Etst.WFC.Utils.InterpretationMono

namespace Etst


namespace Expr
  def clearBvars_eq_bvar
    {ub: Nat}
    (lt: x < ub)
  :
    clearBvars (E := E) ub (.bvar x) = .bvar x
  :=
    if_pos lt
  
  def clearBvars_eq_none
    {ub: Nat}
    (nlt: ¬ x < ub)
  :
    clearBvars (E := E) ub (.bvar x) = none
  :=
    if_neg nlt
  
  def clearBvars_none_eq_none
  :
    clearBvars (E := E) n none = none
  :=
    show (if 0 < n + 1 then bvar 0 else none).arbUn.compl = none from
    if_pos (Nat.zero_lt_succ n) ▸ rfl
  
  def clearBvars_idempotent (expr: Expr E):
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
    | .null => rfl
    | .pair left rite =>
        congrArg₂ Expr.pair
          left.clearBvars_idempotent
          rite.clearBvars_idempotent
    | .un left rite =>
        congrArg₂ Expr.un
          left.clearBvars_idempotent
          rite.clearBvars_idempotent
    | .ir left rite =>
        congrArg₂ Expr.ir
          left.clearBvars_idempotent
          rite.clearBvars_idempotent
    | .condSome body =>
        congrArg Expr.condSome body.clearBvars_idempotent
    | .condFull body =>
        congrArg Expr.condFull body.clearBvars_idempotent
    | .compl body =>
        congrArg Expr.compl body.clearBvars_idempotent
    | .arbUn body =>
        congrArg Expr.arbUn (body.clearBvars_idempotent)
    | .arbIr body =>
        congrArg Expr.arbIr (body.clearBvars_idempotent)
  
  def clearBvars_isClean (expr: Expr E):
    IsClean expr.clearBvars
  :=
    (clearBvars_idempotent expr).symm
  
end Expr

namespace SingleLaneExpr
  open Expr
  
  def clearBvars_preserves_interp_bv
    (expr: SingleLaneExpr)
    (bv bvRest: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 bv b c)
      (intp2 (expr.clearBvars bv.length) (bv ++ bvRest) b c)
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
    | .null => rfl
    | .pair left rite =>
      eq_intp2_pair_of_eq
        (clearBvars_preserves_interp_bv left bv bvRest b c)
        (clearBvars_preserves_interp_bv rite bv bvRest b c)
    | .un left rite =>
      eq_intp2_un_of_eq
        (clearBvars_preserves_interp_bv left bv bvRest b c)
        (clearBvars_preserves_interp_bv rite bv bvRest b c)
    | .ir left rite =>
      eq_intp2_ir_of_eq
        (clearBvars_preserves_interp_bv left bv bvRest b c)
        (clearBvars_preserves_interp_bv rite bv bvRest b c)
    | .condSome body =>
      eq_intp2_condSome_of_eq
        (clearBvars_preserves_interp_bv body bv bvRest b c)
    | .condFull body =>
      eq_intp2_condFull_of_eq
        (clearBvars_preserves_interp_bv body bv bvRest b c)
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
    (expr: SingleLaneExpr)
    (bv: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 [] b c)
      (intp2 expr.clearBvars bv b c)
  :=
    clearBvars_preserves_interp_bv expr [] bv b c
  
  namespace IsClean
    def bvar_independent
      {expr: SingleLaneExpr}
      (isClean: expr.IsClean)
      (bv0 bv1: List Pair)
      (b c: Valuation Pair)
    :
      expr.intp2 bv0 b c = expr.intp2 bv1 b c
    :=
      isClean ▸
      clearBvars_preserves_interp expr bv0 b c ▸
      clearBvars_preserves_interp expr bv1 b c ▸
      rfl

    def changeBv
      {expr: SingleLaneExpr}
      (isClean: IsClean expr)
      {bv1: List Pair}
      (dInExpr: expr.intp2 bv0 b c d)
    :
      expr.intp2 bv1 b c d
    :=
      bvar_independent isClean bv0 bv1 b c ▸ dInExpr
    
  end IsClean
end SingleLaneExpr

namespace BasicExpr
  def clearBvars_lane_comm
    (expr: BasicExpr)
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
    | .null => rfl
    | .pair left rite =>
        congrArg₂
          SingleLaneExpr.pair
          (clearBvars_lane_comm left lane i)
          (clearBvars_lane_comm rite lane i)
    | .un left rite =>
        congrArg₂
          SingleLaneExpr.un
          (clearBvars_lane_comm left lane i)
          (clearBvars_lane_comm rite lane i)
    | .ir left rite =>
        congrArg₂
          SingleLaneExpr.ir
          (clearBvars_lane_comm left lane i)
          (clearBvars_lane_comm rite lane i)
    | .condSome body =>
        congrArg
          SingleLaneExpr.condSome
          (clearBvars_lane_comm body lane i)
    | .condFull body =>
        congrArg
          SingleLaneExpr.condFull
          (clearBvars_lane_comm body lane i)
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
    (expr: BasicExpr)
    (bv: List Pair)
    (b c: Valuation Pair)
  :
    expr.triIntp2 [] b c = triIntp2 expr.clearBvars bv b c
  :=
    let eqBvDef := (expr.toLane .defLane).clearBvars_preserves_interp bv b c
    let eqBvPos := (expr.toLane .posLane).clearBvars_preserves_interp bv b c
    Set3.eq
      (eqBvDef.trans (clearBvars_lane_comm expr .defLane ▸ rfl))
      (eqBvPos.trans (clearBvars_lane_comm expr .posLane ▸ rfl))
end BasicExpr

namespace DefList
  def interp_eq_bv
    (dl: DefList)
    (x: Nat)
    (bv0 bv1: List Pair)
    (b c: Valuation Pair)
  :
    (dl.getDef x).triIntp2 bv0 b c = (dl.getDef x).triIntp2 bv1 b c
  :=
    dl.isClean x ▸
    BasicExpr.clearBvars_preserves_interp (dl.getDef x) bv0 b c ▸
    BasicExpr.clearBvars_preserves_interp (dl.getDef x) bv1 b c ▸
    rfl
  
  def interp_eq_bv_def
    (dl: DefList)
    (x: Nat)
    (bv0 bv1: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (((dl.getDef x).toLane .defLane).intp2 bv0 b c)
      (((dl.getDef x).toLane .defLane).intp2 bv1 b c)
  :=
    Set3.eq_def (dl.interp_eq_bv x bv0 bv1 b c)
  
  def interp_eq_bv_pos
    (dl: DefList)
    (x: Nat)
    (bv0 bv1: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (((dl.getDef x).toLane .posLane).intp2 bv0 b c)
      (((dl.getDef x).toLane .posLane).intp2 bv1 b c)
  :=
    Set3.eq_pos (dl.interp_eq_bv x bv0 bv1 b c)
  
end DefList

namespace SingleLaneExpr
  def InWfm.of_in_def
    (inDef: InWfm bv dl ((dl.getDef x).toLane lane) d)
  :
    InWfm [] dl (.var lane x) d
  :=
    of_in_def_no_bv
      (match lane with
      | .defLane =>
        let eqDef := dl.interp_eq_bv_def x [] bv dl.wfm dl.wfm
        show intp2 _ _ _ _ _ from
        eqDef ▸ inDef
      | .posLane =>
        let eqPos := dl.interp_eq_bv_pos x [] bv dl.wfm dl.wfm
        show intp2 _ _ _ _ _ from
        eqPos ▸ inDef)
  
  def InWfm.in_def
    (inVar: InWfm [] dl (.var lane x) d)
  :
    InWfm bv dl ((dl.getDef x).toLane lane) d
  :=
    show intp2 _ _ _ _ _ from
    match lane with
    | .defLane =>
      dl.interp_eq_bv_def x bv [] dl.wfm dl.wfm ▸
      in_def_no_bv inVar
    | .posLane =>
      dl.interp_eq_bv_pos x bv [] dl.wfm dl.wfm ▸
      in_def_no_bv inVar
  
end SingleLaneExpr
