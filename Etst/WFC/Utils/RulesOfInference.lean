import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Valuation

namespace Etst


namespace Expr
  -- `any` contains all elements, under any valuation.
  def any: Expr E := .arbUn (.bvar 0)
  -- `none` contains no elements, under any valuation.
  def none: Expr E := .compl any
end Expr

namespace SingleLaneExpr
  def inArbUn
    (dBound: Pair)
    (inBody: body.interpretation (dBound :: bv) b c d)
  :
    (arbUn body).interpretation bv b c d
  :=
    ⟨dBound, inBody⟩
  
  
  def inArbUnElim
    (inArbUn: (arbUn body).interpretation bv b c d)
  :
    ∃ dBound, body.interpretation (dBound :: bv) b c d
  :=
    inArbUn
  
  
  def inArbIr
    {bv: List Pair}
    {b c: Valuation Pair}
    {d: Pair}
    (inBody: ∀ dBound, body.interpretation (dBound :: bv) b c d)
  :
    (arbIr body).interpretation bv b c d
  :=
    fun d => inBody d
  
  
  def inArbIrElim
    (inArbIr: (arbIr body).interpretation bv b c d)
    (dBound: Pair)
  :
    body.interpretation (dBound :: bv) b c d
  :=
    inArbIr dBound
  
  
  def inCompl
    (c: Valuation Pair)
    (ninBody: ¬body.interpretation bv b b d)
  :
    (compl body).interpretation bv b c d
  :=
    ninBody
  
  def inComplElim
    (inCompl: (compl body).interpretation bv b b d)
  :
    ¬body.interpretation bv b b d
  :=
    inCompl
  
  -- Valuation c would be redundant since Lean would ignore it, and
  -- complain it cannot be synthetized.
  def ninCompl
    (inBody: body.interpretation bv b b d)
  :
    ¬(compl body).interpretation bv b b d
  :=
    (· inBody)
  
  
  def interp_bvar_eq_empty
    (nlt: ¬ x < bv.length)
  :
    (bvar x).interpretation bv b c = {}
  := by
    show (match bv[x]? with
      | .none => ∅
      | .some d => {d}) = _
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def interp_bvar_eq_of_lt
    (lt: x < bv.length)
  :
    (bvar x).interpretation bv b c = {bv[x]}
  := by
    show (match bv[x]? with
      | .none => ∅
      | .some d => {d}) = _
    rw [List.getElem?_eq_getElem lt]
  
  def interp_bvar_eq_singleton
    {bv: List Pair}
    {dBound: Pair}
    (eq: bv[x]? = some dBound)
  :
    (bvar x).interpretation bv b c = {dBound}
  := by
    show (match bv[x]? with
      | .none => ∅
      | .some d => {d}) = _
    rw [eq]
  
  def inBvar
    {bv: List Pair}
    {dBound: Pair}
    (eq: bv[x]? = some dBound)
  :
    (bvar x).interpretation bv b c dBound
  :=
    interp_bvar_eq_singleton eq ▸ rfl
  
  def inBvarElim
    (h: (bvar x).interpretation bv b c d)
    (eq: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [interp_bvar_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  
  def inAny: interpretation bv b c Expr.any d := inArbUn d (inBvar rfl)
  def ninNone: ¬ interpretation bv b b Expr.none d := ninCompl inAny
  
  def interp_none_eq_empty:
    interpretation bv b c Expr.none = {}
  :=
    le_antisymm (fun _ => ninNone) nofun
  
  
  abbrev InWfm
    (bv: List Pair)
    (dl: DefList)
    (expr: SingleLaneExpr)
    (d: Pair)
  :
    Prop
  :=
    expr.interpretation bv dl.wfm dl.wfm d
  
  
  def InWfm.of_in_def
    (inDef: InWfm [] dl ((dl.getDef x).toLane lane) d)
  :
    InWfm [] dl (.var lane x) d
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel dl]
    exact inDef
  
  
  def InWfm.in_def
    (s: InWfm [] dl (.var lane x) d)
  :
    InWfm [] dl ((dl.getDef x).toLane lane) d
  :=
    let v := dl.wfm
    
    let eqAtN: v x = dl.interpretation v v x :=
      congr (DefList.wfm_isModel dl) rfl
    
    match lane with
    | .defLane => show (dl.interpretation v v x).defMem d from eqAtN ▸ s
    | .posLane => show (dl.interpretation v v x).posMem d from eqAtN ▸ s
  
end SingleLaneExpr
