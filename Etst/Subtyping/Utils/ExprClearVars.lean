import Etst.WFC.Utils.InterpretationMono

namespace Etst


namespace Expr
  def clearVars_eq_var
    {ub: Nat}
    (lt: x < ub)
  :
    clearVars (E := E) ub (.var x) = .var x
  :=
    if_pos lt
  
  def clearVars_eq_none
    {ub: Nat}
    (nlt: ¬ x < ub)
  :
    clearVars (E := E) ub (.var x) = none
  :=
    if_neg nlt
  
  def clearVars_none_eq_none
  :
    clearVars (E := E) n none = none
  :=
    show (if 0 < n + 1 then var 0 else none).arbUn.compl = none from
    if_pos (Nat.zero_lt_succ n) ▸ rfl
  
  def clearVars_idempotent (expr: Expr E):
    (expr.clearVars n).clearVars n = expr.clearVars n
  :=
    match expr with
    | .const _ _ => rfl
    | .var x =>
      if h: x < n then by
        rw [clearVars_eq_var h, clearVars_eq_var h]
      else by
        rw [clearVars_eq_none h]
        exact clearVars_none_eq_none
    | .null => rfl
    | .pair left rite =>
        congrArg₂ Expr.pair
          left.clearVars_idempotent
          rite.clearVars_idempotent
    | .ir left rite =>
        congrArg₂ Expr.ir
          left.clearVars_idempotent
          rite.clearVars_idempotent
    | .condFull body =>
        congrArg Expr.condFull body.clearVars_idempotent
    | .compl body =>
        congrArg Expr.compl body.clearVars_idempotent
    | .arbIr body =>
        congrArg Expr.arbIr (body.clearVars_idempotent)
  
  def clearVars_isClean (expr: Expr E):
    IsClean expr.clearVars
  :=
    (clearVars_idempotent expr).symm
  
end Expr

namespace SingleLaneExpr
  open Expr
  
  def clearVars_preserves_interp_bv
    (expr: SingleLaneExpr)
    (bv bvRest: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 bv b c)
      (intp2 (expr.clearVars bv.length) (bv ++ bvRest) b c)
  :=
    match expr with
    | .const _ _ => rfl
    | .var x =>
      if h: x < bv.length then
        let ltExtra: x < (bv ++ bvRest).length := 
          h.trans_le (bv.length_le_append_rite bvRest)
        let eq: clearVars bv.length (var x) = var x :=
          clearVars_eq_var h
        by
        rw [intp2_var_eq_of_lt h, eq]
        rw [intp2_var_eq_of_lt ltExtra]
        rw [bv.getElem_append_left h]
      else
        clearVars_eq_none h ▸
        SingleLaneExpr.intp2_var_eq_empty h ▸
        SingleLaneExpr.intp2_none_eq_empty.symm
    | .null => rfl
    | .pair left rite =>
      eq_intp2_pair_of_eq
        (clearVars_preserves_interp_bv left bv bvRest b c)
        (clearVars_preserves_interp_bv rite bv bvRest b c)
    | .ir left rite =>
      eq_intp2_ir_of_eq
        (clearVars_preserves_interp_bv left bv bvRest b c)
        (clearVars_preserves_interp_bv rite bv bvRest b c)
    | .condFull body =>
      eq_intp2_condFull_of_eq
        (clearVars_preserves_interp_bv body bv bvRest b c)
    | .compl body =>
      let ih := clearVars_preserves_interp_bv body bv bvRest c b
      eq_intp2_compl_of_eq ih
    | .arbIr body =>
      eq_intp2_arbIr_of_eq (fun dX =>
        clearVars_preserves_interp_bv (bvRest := bvRest) body (dX :: bv) b c)
  
  def clearVars_preserves_interp
    (expr: SingleLaneExpr)
    (bv: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 [] b c)
      (intp2 expr.clearVars bv b c)
  :=
    clearVars_preserves_interp_bv expr [] bv b c
  
  namespace IsClean
    def var_independent
      {expr: SingleLaneExpr}
      (isClean: expr.IsClean)
      (bv0 bv1: List Pair)
      (b c: Valuation Pair)
    :
      expr.intp2 bv0 b c = expr.intp2 bv1 b c
    :=
      isClean ▸
      clearVars_preserves_interp expr bv0 b c ▸
      clearVars_preserves_interp expr bv1 b c ▸
      rfl

    def changeBv
      {expr: SingleLaneExpr}
      (isClean: IsClean expr)
      {bv1: List Pair}
      (dInExpr: expr.intp2 bv0 b c d)
    :
      expr.intp2 bv1 b c d
    :=
      var_independent isClean bv0 bv1 b c ▸ dInExpr
    
  end IsClean
end SingleLaneExpr

namespace BasicExpr
  def clearVars_lane_comm
    (expr: BasicExpr)
    (lane: Set3.Lane)
    (i: Nat := 0)
  :
    Eq
      (Expr.clearVars i (expr.toLane lane))
      (BasicExpr.toLane (Expr.clearVars i expr) lane)
  :=
    match expr with
    | .const x => rfl
    | .var x => by
      show
        Eq
          (Expr.clearVars i (.var x))
          (toLane (Expr.clearVars i (.var x)) lane)
      if h: x < i then
        rw [Expr.clearVars_eq_var h, Expr.clearVars_eq_var h]
        rfl
      else
        rw [Expr.clearVars_eq_none h, Expr.clearVars_eq_none h]
        rfl
    | .null => rfl
    | .pair left rite =>
        congrArg₂
          SingleLaneExpr.pair
          (clearVars_lane_comm left lane i)
          (clearVars_lane_comm rite lane i)
    | .ir left rite =>
        congrArg₂
          SingleLaneExpr.ir
          (clearVars_lane_comm left lane i)
          (clearVars_lane_comm rite lane i)
    | .condFull body =>
        congrArg
          SingleLaneExpr.condFull
          (clearVars_lane_comm body lane i)
    | .compl body =>
        congrArg
          SingleLaneExpr.compl
          (clearVars_lane_comm body lane.toggle i)
    | .arbIr body =>
        congrArg
          SingleLaneExpr.arbIr
          (clearVars_lane_comm body lane (i + 1))
  
  def clearVars_preserves_interp
    (expr: BasicExpr)
    (bv: List Pair)
    (b c: Valuation Pair)
  :
    expr.triIntp2 [] b c = triIntp2 expr.clearVars bv b c
  :=
    let eqBvDef := (expr.toLane .defLane).clearVars_preserves_interp bv b c
    let eqBvPos := (expr.toLane .posLane).clearVars_preserves_interp bv b c
    Set3.eq
      (eqBvDef.trans (clearVars_lane_comm expr .defLane ▸ rfl))
      (eqBvPos.trans (clearVars_lane_comm expr .posLane ▸ rfl))
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
    BasicExpr.clearVars_preserves_interp (dl.getDef x) bv0 b c ▸
    BasicExpr.clearVars_preserves_interp (dl.getDef x) bv1 b c ▸
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
    InWfm [] dl (.const lane x) d
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
    (inVar: InWfm [] dl (.const lane x) d)
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
  def freeVarUB
    (expr: Expr E)
    (depth: Nat := 0)
  :
    Nat
  :=
    match expr with
    | .const _ _ => 0
    | .var x => x + 1 - depth
    | .null => 0
    | .pair left rite =>
        Nat.max (left.freeVarUB depth) (rite.freeVarUB depth)
    | .ir left rite =>
        Nat.max (left.freeVarUB depth) (rite.freeVarUB depth)
    | .condFull body => body.freeVarUB depth
    | .compl body => body.freeVarUB depth
    | .arbIr body => body.freeVarUB (depth + 1)
  
  
  def freeVarUB_pair_lt
    (hl: l.freeVarUB d < x)
    (hr: r.freeVarUB d < x)
  :
    (pair l r).freeVarUB d < x
  :=
    Nat.max_lt.mpr ⟨hl, hr⟩
  
  def freeVarUB_pair_lt_left
    (h: (pair l r).freeVarUB d < x)
  :
    l.freeVarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
  
  def freeVarUB_pair_lt_rite
    (h: (pair l r).freeVarUB d < x)
  :
    r.freeVarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
  
  def freeVarUB_pair_lt_elim
    (h: (pair l r).freeVarUB d < x)
  :
    l.freeVarUB d < x ∧ r.freeVarUB d < x
  :=
    ⟨freeVarUB_pair_lt_left h, freeVarUB_pair_lt_rite h⟩
  
  
  def freeVarUB_un_lt
    (hl: l.freeVarUB d < x)
    (hr: r.freeVarUB d < x)
  :
    (un l r).freeVarUB d < x
  :=
    Nat.max_lt.mpr ⟨hl, hr⟩
  
  def freeVarUB_un_lt_left
    (h: (un l r).freeVarUB d < x)
  :
    l.freeVarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
  
  def freeVarUB_un_lt_rite
    (h: (un l r).freeVarUB d < x)
  :
    r.freeVarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
  
  def freeVarUB_un_lt_elim
    (h: (un l r).freeVarUB d < x)
  :
    l.freeVarUB d < x ∧ r.freeVarUB d < x
  :=
    ⟨freeVarUB_un_lt_left h, freeVarUB_un_lt_rite h⟩
  
  
  def freeVarUB_ir_lt
    (hl: l.freeVarUB d < x)
    (hr: r.freeVarUB d < x)
  :
    (ir l r).freeVarUB d < x
  :=
    Nat.max_lt.mpr ⟨hl, hr⟩
  
  def freeVarUB_ir_lt_left
    (h: (ir l r).freeVarUB d < x)
  :
    l.freeVarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
  
  def freeVarUB_ir_lt_rite
    (h: (ir l r).freeVarUB d < x)
  :
    r.freeVarUB d < x
  :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
  
  def freeVarUB_ir_lt_elim
    (h: (ir l r).freeVarUB d < x)
  :
    l.freeVarUB d < x ∧ r.freeVarUB d < x
  :=
    ⟨freeVarUB_ir_lt_left h, freeVarUB_ir_lt_rite h⟩
  
  
  def freeVarUB_null_le {E d x}:
    freeVarUB null (E := E) d ≤ x
  :=
    Nat.zero_le _
  
  def freeVarUB_any_le {E d x}:
    freeVarUB any (E := E) d ≤ x
  :=
    show 0 + 1 - (d + 1) ≤ x by simp
  
  
  def freeVarUB_pair_le
    (hl: l.freeVarUB d ≤ x)
    (hr: r.freeVarUB d ≤ x)
  :
    (pair l r).freeVarUB d ≤ x
  :=
    Nat.max_le.mpr ⟨hl, hr⟩
  
  def freeVarUB_pair_le_left
    (h: (pair l r).freeVarUB d ≤ x)
  :
    l.freeVarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_left _ _) h
  
  def freeVarUB_pair_le_rite
    (h: (pair l r).freeVarUB d ≤ x)
  :
    r.freeVarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_right _ _) h
  
  def freeVarUB_pair_le_elim
    (h: (pair l r).freeVarUB d ≤ x)
  :
    l.freeVarUB d ≤ x ∧ r.freeVarUB d ≤ x
  :=
    ⟨freeVarUB_pair_le_left h, freeVarUB_pair_le_rite h⟩
  
  
  def freeVarUB_un_le
    (hl: l.freeVarUB d ≤ x)
    (hr: r.freeVarUB d ≤ x)
  :
    (un l r).freeVarUB d ≤ x
  :=
    Nat.max_le.mpr ⟨hl, hr⟩
  
  def freeVarUB_un_le_left
    (h: (un l r).freeVarUB d ≤ x)
  :
    l.freeVarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_left _ _) h
  
  def freeVarUB_un_le_rite
    (h: (un l r).freeVarUB d ≤ x)
  :
    r.freeVarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_right _ _) h
  
  def freeVarUB_un_le_elim
    (h: (un l r).freeVarUB d ≤ x)
  :
    l.freeVarUB d ≤ x ∧ r.freeVarUB d ≤ x
  :=
    ⟨freeVarUB_un_le_left h, freeVarUB_un_le_rite h⟩
  
  
  def freeVarUB_ir_le
    (hl: l.freeVarUB d ≤ x)
    (hr: r.freeVarUB d ≤ x)
  :
    (ir l r).freeVarUB d ≤ x
  :=
    Nat.max_le.mpr ⟨hl, hr⟩
  
  def freeVarUB_ir_le_left
    (h: (ir l r).freeVarUB d ≤ x)
  :
    l.freeVarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_left _ _) h
  
  def freeVarUB_ir_le_rite
    (h: (ir l r).freeVarUB d ≤ x)
  :
    r.freeVarUB d ≤ x
  :=
    Nat.le_trans (Nat.le_max_right _ _) h
  
  
  def clearVars_eq_of_ub
    {expr: Expr E}
    {ub depth: Nat}
    (h: expr.freeVarUB depth ≤ ub)
  :
    Expr.clearVars (ub + depth) expr = expr
  :=
    let leL {l r} (h: max l r ≤ ub) := Nat.le_trans (Nat.le_max_left l r) h
    let leR {l r} (h: max l r ≤ ub) := Nat.le_trans (Nat.le_max_right l r) h
    match expr with
    | .const _ _ => rfl
    | .var _ => by
      unfold clearVars
      split_ifs with h_cv
      · rfl
      · exfalso
        unfold freeVarUB at h
        · omega
    | .null => rfl
    | .pair _ _ =>
      congrArg₂ Expr.pair
        (clearVars_eq_of_ub (leL h))
        (clearVars_eq_of_ub (leR h))
    | .ir _ _ =>
      congrArg₂ Expr.ir
        (clearVars_eq_of_ub (leL h))
        (clearVars_eq_of_ub (leR h))
    | .condFull _ =>
      congrArg Expr.condFull (clearVars_eq_of_ub h)
    | .compl _ =>
      congrArg Expr.compl (clearVars_eq_of_ub h)
    | .arbIr _ =>
      congrArg
        Expr.arbIr
        (clearVars_eq_of_ub (depth := depth + 1) h)
end Expr

namespace SingleLaneExpr
  def intp2_bv_append
    (dl: DefList)
    {expr: SingleLaneExpr}
    {bv: List Pair}
    (h: expr.freeVarUB ≤ bv.length)
    (rest: List Pair)
    (p: Pair)
  :
    expr.intp bv dl.wfm p ↔ expr.intp (bv ++ rest) dl.wfm p
  := by
    unfold SingleLaneExpr.intp
    rw [SingleLaneExpr.clearVars_preserves_interp_bv]
    have: Expr.clearVars bv.length expr = expr :=
      Expr.clearVars_eq_of_ub h
    rw [this]
end SingleLaneExpr
