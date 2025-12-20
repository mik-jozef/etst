import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Valuation

namespace Etst

namespace SingleLaneExpr
  def inArbUn
    (dBound: Pair)
    (inBody: body.intp2 (dBound :: bv) b c d)
  :
    (arbUn body).intp2 bv b c d
  :=
    ⟨dBound, inBody⟩
  
  
  def inArbUnElim
    (inArbUn: (arbUn body).intp2 bv b c d)
  :
    ∃ dBound, body.intp2 (dBound :: bv) b c d
  :=
    inArbUn
  
  
  def inArbIr
    {bv: List Pair}
    {b c: Valuation Pair}
    {d: Pair}
    (inBody: ∀ dBound, body.intp2 (dBound :: bv) b c d)
  :
    (arbIr body).intp2 bv b c d
  :=
    fun d => inBody d
  
  
  def inArbIrElim
    (inArbIr: (arbIr body).intp2 bv b c d)
    (dBound: Pair)
  :
    body.intp2 (dBound :: bv) b c d
  :=
    inArbIr dBound
  
  
  def inCompl
    (c: Valuation Pair)
    (ninBody: ¬body.intp2 bv b b d)
  :
    (compl body).intp2 bv b c d
  :=
    ninBody
  
  def inComplElim
    (inCompl: (compl body).intp2 bv b b d)
  :
    ¬body.intp2 bv b b d
  :=
    inCompl
  
  -- Valuation c would be redundant since Lean would ignore it, and
  -- complain it cannot be synthetized.
  def ninCompl
    (inBody: body.intp2 bv b b d)
  :
    ¬(compl body).intp2 bv b b d
  :=
    (· inBody)
  
  
  def interp_bvar_eq_empty
    (nlt: ¬ x < bv.length)
  :
    (bvar x).intp2 bv b c = {}
  := by
    show intp2Bvar bv x = _
    unfold intp2Bvar
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def interp_bvar_eq_of_lt
    (lt: x < bv.length)
  :
    (bvar x).intp2 bv b c = {bv[x]}
  := by
    show intp2Bvar bv x = _
    unfold intp2Bvar
    rw [List.getElem?_eq_getElem lt]
  
  def interp_bvar_eq_singleton
    {bv: List Pair}
    {dBound: Pair}
    (eq: bv[x]? = some dBound)
  :
    (bvar x).intp2 bv b c = {dBound}
  := by
    show intp2Bvar bv x = _
    unfold intp2Bvar
    rw [eq]
  
  def inBvar
    {bv: List Pair}
    {dBound: Pair}
    (eq: bv[x]? = some dBound)
  :
    (bvar x).intp2 bv b c dBound
  :=
    interp_bvar_eq_singleton eq ▸ rfl
  
  def inBvarElim
    (h: (bvar x).intp2 bv b c d)
    (eq: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [interp_bvar_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  
  def inAny: intp2 .any bv b c d := inArbUn d (inBvar rfl)
  def ninNone: ¬ intp2 .none bv b b d := ninCompl inAny
  
  def interp_none_eq_empty:
    intp2 .none bv b c = {}
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
    expr.intp2 bv dl.wfm dl.wfm d
  
  
  def InWfm.of_in_def_no_bv
    (inDef: InWfm [] dl ((dl.getDef x).toLane lane) d)
  :
    InWfm [] dl (.var lane x) d
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel dl]
    exact inDef
  
  
  def InWfm.in_def_no_bv
    (inVar: InWfm [] dl (.var lane x) d)
  :
    InWfm [] dl ((dl.getDef x).toLane lane) d
  :=
    let v := dl.wfm
    
    let eqAtN: v x = dl.triIntp2 v v x :=
      congr (DefList.wfm_isModel dl) rfl
    
    match lane with
    | .defLane => show (dl.triIntp2 v v x).defMem d from eqAtN ▸ inVar
    | .posLane => show (dl.triIntp2 v v x).posMem d from eqAtN ▸ inVar
  
end SingleLaneExpr
