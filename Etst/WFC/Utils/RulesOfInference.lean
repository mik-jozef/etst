import Etst.WFC.Ch4_PairSalgebra
import Etst.WFC.Utils.Valuation

namespace Etst


namespace Expr
  -- `any` contains all elements, under any valuation.
  def any: Expr E sig := .arbUn (.bvar 0)
  -- `none` contains no elements, under any valuation.
  def none: Expr E sig := .compl any
end Expr

namespace SingleLaneExpr
  def inArbUn
    (dBound: salg.D)
    (inBody: body.interpretation salg (dBound :: bv) b c d)
  :
    (arbUn body).interpretation salg bv b c d
  :=
    ⟨dBound, inBody⟩
  
  
  def inArbUnElim
    (inArbUn: (arbUn body).interpretation salg bv b c d)
  :
    ∃ dBound, body.interpretation salg (dBound :: bv) b c d
  :=
    inArbUn
  
  
  def inArbIr
    {salg: Salgebra sig}
    {bv: List salg.D}
    {b c: Valuation salg.D}
    {d: salg.D}
    (inBody: ∀ dBound, body.interpretation salg (dBound :: bv) b c d)
  :
    (arbIr body).interpretation salg bv b c d
  :=
    fun d => inBody d
  
  
  def inArbIrElim
    (inArbIr: (arbIr body).interpretation salg bv b c d)
    (dBound: salg.D)
  :
    body.interpretation salg (dBound :: bv) b c d
  :=
    inArbIr dBound
  
  
  def inCompl
    (c: Valuation salg.D)
    (ninBody: ¬body.interpretation salg bv b b d)
  :
    (compl body).interpretation salg bv b c d
  :=
    ninBody
  
  def inComplElim
    (inCompl: (compl body).interpretation salg bv b b d)
  :
    ¬body.interpretation salg bv b b d
  :=
    inCompl
  
  -- Valuation c would be redundant since Lean would ignore it, and
  -- complain it cannot be synthetized.
  def ninCompl
    (inBody: body.interpretation salg bv b b d)
  :
    ¬(compl body).interpretation salg bv b b d
  :=
    (· inBody)
  
  
  def interp_bvar_eq_empty
    (nlt: ¬ x < bv.length)
  :
    (bvar x).interpretation salg bv b c = {}
  := by
    show (match bv[x]? with
      | .none => ∅
      | .some d => {d}) = _
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def interp_bvar_eq_of_lt
    (lt: x < bv.length)
  :
    (bvar x).interpretation salg bv b c = {bv[x]}
  := by
    show (match bv[x]? with
      | .none => ∅
      | .some d => {d}) = _
    rw [List.getElem?_eq_getElem lt]
  
  def interp_bvar_eq_singleton
    {bv: List salg.D}
    {dBound: salg.D}
    (eq: bv[x]? = some dBound)
  :
    (bvar x).interpretation salg bv b c = {dBound}
  := by
    show (match bv[x]? with
      | .none => ∅
      | .some d => {d}) = _
    rw [eq]
  
  def inBvar
    {bv: List salg.D}
    {dBound: salg.D}
    (eq: bv[x]? = some dBound)
  :
    (bvar x).interpretation salg bv b c dBound
  :=
    interp_bvar_eq_singleton eq ▸ rfl
  
  def inBvarElim
    (h: (bvar x).interpretation salg bv b c d)
    (eq: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [interp_bvar_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  
  def inAny: interpretation salg bv b c Expr.any d := inArbUn d (inBvar rfl)
  def ninNone: ¬ interpretation salg bv b b Expr.none d := ninCompl inAny
  
  def interp_none_eq_empty:
    interpretation salg bv b c Expr.none = {}
  :=
    le_antisymm (fun _ => ninNone) nofun
  
  
  abbrev InWfm
    (salg: Salgebra sig)
    (bv: List salg.D)
    (dl: DefList sig)
    (expr: SingleLaneExpr sig)
    (d: salg.D)
  :
    Prop
  :=
    expr.interpretation salg bv (dl.wfm salg) (dl.wfm salg) d
  
  
  def InWfm.of_in_def
    (inDef: InWfm salg [] dl ((dl.getDef x).toLane lane) d)
  :
    InWfm salg [] dl (.var lane x) d
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel salg dl]
    exact inDef
  
  
  def InWfm.in_def
    (s: InWfm salg [] dl (.var lane x) d)
  :
    InWfm salg [] dl ((dl.getDef x).toLane lane) d
  :=
    let v := dl.wfm salg
    
    let eqAtN: v x = dl.interpretation salg v v x :=
      congr (DefList.wfm_isModel salg dl) rfl
    
    match lane with
    | .defLane => show (dl.interpretation salg v v x).defMem d from eqAtN ▸ s
    | .posLane => show (dl.interpretation salg v v x).posMem d from eqAtN ▸ s
  
end SingleLaneExpr
