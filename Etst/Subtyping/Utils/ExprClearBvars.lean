import Etst.WFC.Utils.ExprMonoEq

namespace Etst


namespace Expr
  def clearBvars (max := 0): Expr sig → Expr sig
    | .var x => .var x
    | .bvar x => if x < max then .bvar x else .none
    | .op o args => .op o (fun p => (args p).clearBvars max)
    | .cpl e => .cpl (e.clearBvars max)
    | .arbUn body => .arbUn (body.clearBvars (max + 1))
    | .arbIr body => .arbIr (body.clearBvars (max + 1))
  
  def clearBvars_eq_bvar
    {max: Nat}
    (lt: x < max)
  :
    clearBvars (sig := sig) max (.bvar x) = .bvar x
  :=
    if_pos lt
  
  def clearBvars_eq_none
    {max: Nat}
    (nlt: ¬ x < max)
  :
    clearBvars (sig := sig) max (.bvar x) = none
  :=
    if_neg nlt
  
  
  def clearVars_preserves_interp_bv
    (e: Expr sig)
    (bv: List salg.D)
    (b c: Valuation salg.D)
  :
    Eq
      (e.interpretation salg bv b c)
      ((e.clearBvars bv.length).interpretation salg (bv ++ bvRest) b c)
  :=
    match e with
    | var _ => rfl
    | bvar x =>
      if h: x < bv.length then by
        unfold interpretation
        rw [clearBvars_eq_bvar h, bv.get?_append_left h]
      else
        clearBvars_eq_none h ▸
        inter_bvar_eq_empty h ▸
        inter_none_eq_empty.symm
    | op _ args =>
      eq_op_of_eq (fun param =>
        clearVars_preserves_interp_bv (args param) bv b c)
    | cpl body =>
      let ih := clearVars_preserves_interp_bv body bv b b
      eq_cpl_of_eq ih
    | arbUn body =>
      eq_arbUn_of_eq (fun dX =>
        clearVars_preserves_interp_bv body (dX :: bv) b c)
    | arbIr body =>
      eq_arbIr_of_eq (fun dX =>
        clearVars_preserves_interp_bv (bvRest := bvRest) body (dX :: bv) b c)
  
  def clearVars_preserves_interp
    (e: Expr sig)
    (bv: List salg.D)
    (b c: Valuation salg.D)
  :
    Eq
      (e.interpretation salg [] b c)
      (e.clearBvars.interpretation salg bv b c)
  :=
    clearVars_preserves_interp_bv e [] b c
end Expr
