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
    | .ir left rite =>
        congrArg₂ Expr.ir
          left.clearBvars_idempotent
          rite.clearBvars_idempotent
    | .condFull body =>
        congrArg Expr.condFull body.clearBvars_idempotent
    | .compl body =>
        congrArg Expr.compl body.clearBvars_idempotent
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
        rw [intp2_bvar_eq_of_lt h, eq]
        rw [intp2_bvar_eq_of_lt ltExtra]
        rw [bv.getElem_append_left h]
      else
        clearBvars_eq_none h ▸
        SingleLaneExpr.intp2_bvar_eq_empty h ▸
        SingleLaneExpr.intp2_none_eq_empty.symm
    | .null => rfl
    | .pair left rite =>
      eq_intp2_pair_of_eq
        (clearBvars_preserves_interp_bv left bv bvRest b c)
        (clearBvars_preserves_interp_bv rite bv bvRest b c)
    | .ir left rite =>
      eq_intp2_ir_of_eq
        (clearBvars_preserves_interp_bv left bv bvRest b c)
        (clearBvars_preserves_interp_bv rite bv bvRest b c)
    | .condFull body =>
      eq_intp2_condFull_of_eq
        (clearBvars_preserves_interp_bv body bv bvRest b c)
    | .compl body =>
      let ih := clearBvars_preserves_interp_bv body bv bvRest c b
      eq_compl_of_eq ih
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
    (lane: Set3.Lane)
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
    | .ir left rite =>
        congrArg₂
          SingleLaneExpr.ir
          (clearBvars_lane_comm left lane i)
          (clearBvars_lane_comm rite lane i)
    | .condFull body =>
        congrArg
          SingleLaneExpr.condFull
          (clearBvars_lane_comm body lane i)
    | .compl body =>
        congrArg
          SingleLaneExpr.compl
          (clearBvars_lane_comm body lane.toggle i)
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


namespace Expr
  def looseBvarUB
    (expr: Expr E)
    (depth: Nat := 0)
  :
    Nat
  :=
    match expr with
    | .var _ _ => 0
    | .bvar x => if x < depth then 0 else x + 1 - depth
    | .null => 0
    | .pair left rite =>
        Nat.max (left.looseBvarUB depth) (rite.looseBvarUB depth)
    | .ir left rite =>
        Nat.max (left.looseBvarUB depth) (rite.looseBvarUB depth)
    | .condFull body => body.looseBvarUB depth
    | .compl body => body.looseBvarUB depth
    | .arbIr body => body.looseBvarUB depth
  
  def looseBvarUB_pair_lt_left
    (h : (pair l r).looseBvarUB d < x)
  :
    l.looseBvarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
  
  def looseBvarUB_pair_lt_rite
    (h : (pair l r).looseBvarUB d < x)
  :
    r.looseBvarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
  
  def looseBvarUB_un_lt_left
    (h : (un l r).looseBvarUB d < x)
  :
    l.looseBvarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
  
  def looseBvarUB_un_lt_rite
    (h : (un l r).looseBvarUB d < x)
  :
    r.looseBvarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
  
  def looseBvarUB_ir_lt_left
    (h : (ir l r).looseBvarUB d < x)
  :
    l.looseBvarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
  
  def looseBvarUB_ir_lt_rite
    (h : (ir l r).looseBvarUB d < x)
  :
    r.looseBvarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
  
  def looseBvarUB_pair_le_left
    (h : (pair l r).looseBvarUB d ≤ x)
  :
    l.looseBvarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_left _ _) h
  
  def looseBvarUB_pair_le_rite
    (h : (pair l r).looseBvarUB d ≤ x)
  :
    r.looseBvarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_right _ _) h
  
  def looseBvarUB_un_le_left
    (h : (un l r).looseBvarUB d ≤ x)
  :
    l.looseBvarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_left _ _) h
  
  def looseBvarUB_un_le_rite
    (h : (un l r).looseBvarUB d ≤ x)
  :
    r.looseBvarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_right _ _) h
  
  def looseBvarUB_ir_le_left
    (h : (ir l r).looseBvarUB d ≤ x)
  :
    l.looseBvarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_left _ _) h
  
  def looseBvarUB_ir_le_rite
    (h : (ir l r).looseBvarUB d ≤ x)
  :
    r.looseBvarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_right _ _) h
  
  
  def clearBvars_eq_of_ub
    {expr: Expr E}
    {ub: Nat}
    (h: expr.looseBvarUB ≤ ub)
  :
    Expr.clearBvars ub expr = expr
  :=
    let leL {l r} (h: max l r ≤ ub) := Nat.le_trans (Nat.le_max_left l r) h
    let leR {l r} (h: max l r ≤ ub) := Nat.le_trans (Nat.le_max_right l r) h
    match expr with
    | .var _ _ => rfl
    | .bvar _ => clearBvars_eq_bvar (Nat.lt_of_succ_le h)
    | .null => rfl
    | .pair _ _ =>
      congrArg₂ Expr.pair
        (clearBvars_eq_of_ub (leL h))
        (clearBvars_eq_of_ub (leR h))
    | .ir _ _ =>
      congrArg₂ Expr.ir
        (clearBvars_eq_of_ub (leL h))
        (clearBvars_eq_of_ub (leR h))
    | .condFull _ =>
      congrArg Expr.condFull (clearBvars_eq_of_ub h)
    | .compl _ =>
      congrArg Expr.compl (clearBvars_eq_of_ub h)
    | .arbIr _ =>
      congrArg
        Expr.arbIr
        (clearBvars_eq_of_ub (Nat.le_trans h (Nat.le_succ _)))
end Expr

namespace SingleLaneExpr
  def intp_append
    (dl: DefList)
    {expr: SingleLaneExpr}
    {bv: List Pair}
    (h: expr.looseBvarUB ≤ bv.length)
    (rest: List Pair)
    (p: Pair)
  :
    expr.intp bv dl.wfm p ↔ expr.intp (bv ++ rest) dl.wfm p
  := by
    unfold SingleLaneExpr.intp
    rw [SingleLaneExpr.clearBvars_preserves_interp_bv]
    rw [Expr.clearBvars_eq_of_ub h]
end SingleLaneExpr
