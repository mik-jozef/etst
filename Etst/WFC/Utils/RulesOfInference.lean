import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Valuation

namespace Etst

namespace SingleLaneExpr
  def intp2_var_eq_empty
    (nlt: ¬ x < fv.length)
  :
    (var x).intp2 fv b c = {}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def intp2_var_eq_of_lt
    (lt: x < fv.length)
  :
    (var x).intp2 fv b c = {fv[x]}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_getElem lt]
  
  def intp2_var_eq_singleton
    {fv: List Pair}
    {dBound: Pair}
    (eq: fv[x]? = .some dBound)
  :
    (var x).intp2 fv b c = {dBound}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [eq]
  
  def inVar
    {fv: List Pair}
    {dBound: Pair}
    (eq: fv[x]? = .some dBound)
  :
    (var x).intp2 fv b c dBound
  :=
    intp2_var_eq_singleton eq ▸ rfl
  
  def inVarElim
    (h: (var x).intp2 fv b c d)
    (eq: fv[x]? = .some dBound)
  :
    d = dBound
  := by
    rw [intp2_var_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  
  def inNull:
    null.intp2 fv b c .null
  :=
    rfl
  
  def inNullElim
    (inNull: null.intp2 fv b c d)
  :
    d = .null
  :=
    inNull
  
  def inNullElimNeq
    (inNull: null.intp2 fv b c d)
    a b
  :
    d ≠ Pair.pair a b
  :=
    fun eq => Pair.noConfusion (inNull.symm.trans eq)
  
  def inNullElimPair
    (inNull: null.intp2 fv b c (Pair.pair pA pB))
    {P: Prop}
  :
    P
  :=
    (inNullElimNeq inNull pA pB rfl).elim
  
  
  def inPair
    (inLeft: exprL.intp2 fv b c pA)
    (inRite: exprR.intp2 fv b c pB)
  :
    (pair exprL exprR).intp2 fv b c (Pair.pair pA pB)
  :=
    ⟨pA, pB, rfl, inLeft, inRite⟩
  
  def inPairElim
    (inPair: (pair exprL exprR).intp2 fv b c (Pair.pair pA pB))
  :
    And
      (exprL.intp2 fv b c pA)
      (exprR.intp2 fv b c pB)
  :=
    let ⟨_pairL, _pairR, eq, inL, inR⟩ := inPair
    let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
    ⟨eqL ▸ inL, eqR ▸ inR⟩
  
  def inPairElimEx
    (inPair: (pair exprL exprR).intp2 fv b c d)
  :
    ∃ pA pB,
      d = Pair.pair pA pB ∧
      exprL.intp2 fv b c pA ∧
      exprR.intp2 fv b c pB
  :=
    match d with
    | Pair.pair pA pB =>
      let ⟨_pairL, _pairR, eq, inL, inR⟩ := inPair
      let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
      ⟨pA, pB, ⟨rfl, eqL ▸ inL, eqR ▸ inR⟩⟩
  
  def inPairElimNope
    (inPair: (pair exprL exprR).intp2 fv b c .null)
    {P: Prop}
  :
    P
  :=
    let ⟨_, _, eq, _⟩ := inPair
    Pair.noConfusion eq
  
  def ninPairElim
    (ninPair: ¬ (pair exprL exprR).intp2 fv b c (.pair pA pB))
  :
    ¬ exprL.intp2 fv b c pA ∨ ¬ exprR.intp2 fv b c pB
  :=
    not_and_or.mp fun ⟨inL, inR⟩ =>
      ninPair ⟨pA, pB, rfl, inL, inR⟩
  
  
  def inIr
    (l: exprL.intp2 fv b c d)
    (r: exprR.intp2 fv b c d)
  :
    (ir exprL exprR).intp2 fv b c d
  :=
    ⟨l, r⟩
  
  def inIrElim
    (inIr: (ir exprL exprR).intp2 fv b c d)
  :
    And
      (exprL.intp2 fv b c d)
      (exprR.intp2 fv b c d)
  :=
    inIr
  
  def inIrElimL
    (inIr: (ir exprL exprR).intp2 fv b c d)
  :
    exprL.intp2 fv b c d
  :=
    inIr.left

  def inIrElimR
    (inIr: (ir exprL exprR).intp2 fv b c d)
  :
    exprR.intp2 fv b c d
  :=
    inIr.right
  
  
  def inFull
    (d: Pair)
    (allInExpr: (dE: Pair) → expr.intp2 fv b c dE)
  :
    (full expr).intp2 fv b c d
  :=
    allInExpr
  
  def inFullElim
    -- note we're using null instead of d here because
    -- it is ignored by the interpretation function,
    -- so Lean frequently fails with "don't know how to
    -- synthesize this implicit argument" errors.
    (inFull: (full expr).intp2 fv b c .null)
  :
    ∀ dE, expr.intp2 fv b c dE
  :=
    inFull
  
  
  def inCompl
    (ninBody: ¬body.intp2 fv b c d)
  :
    (compl body).intp2 fv c b d
  :=
    ninBody
  
  def inComplElim
    (inCompl: (compl body).intp2 fv b c d)
  :
    ¬body.intp2 fv c b d
  :=
    inCompl
  
  def ninCompl
    (inBody: body.intp2 fv b c d)
  :
    ¬(compl body).intp2 fv c b d
  :=
    (· inBody)
  
  
  def inArbIr
    {fv: List Pair}
    {b c: Valuation Pair}
    {d: Pair}
    (inBody: ∀ dBound, body.intp2 (dBound :: fv) b c d)
  :
    (arbIr body).intp2 fv b c d
  :=
    fun d => inBody d
  
  
  def inArbIrElim
    (inArbIr: (arbIr body).intp2 fv b c d)
    (dBound: Pair)
  :
    body.intp2 (dBound :: fv) b c d
  :=
    inArbIr dBound
  
  
  def inUnL
    (inLeft: left.intp2 fv b c d)
  :
    (un left rite).intp2 fv b c d
  :=
    inCompl (fun ⟨ninL, _⟩ => ninL inLeft)
  
  def inUnR
    (inRite: rite.intp2 fv b c d)
  :
    (un left rite).intp2 fv b c d
  :=
    inCompl (fun ⟨_, ninR⟩ => ninR inRite)
  
  def inUnElim
    (inUn: (un left rite).intp2 fv b c d)
  :
    Or (left.intp2 fv b c d) (rite.intp2 fv b c d)
  :=
    match Classical.em (left.intp2 fv b c d) with
    | .inl inL => .inl inL
    | .inr ninL =>
      .inr <| Classical.byContradiction fun ninR =>
        inUn ⟨ninL, ninR⟩
  
  
  def inSome
    (d: Pair)
    (inBody: body.intp2 fv b c dE)
  :
    (some body).intp2 fv b c d
  :=
    inCompl (fun h => h dE inBody)
  
  def inSomeElim
    (inSome: (some body).intp2 fv b c d)
  :
    ∃ dE, body.intp2 fv b c dE
  :=
    Classical.byContradiction fun h =>
      inSome (fun dE ninBody => h ⟨dE, ninBody⟩)
  
  
  def inArbUn
    (dBound: Pair)
    (inBody: body.intp2 (dBound :: fv) b c d)
  :
    (arbUn body).intp2 fv b c d
  :=
    inCompl (fun h => h dBound inBody)
  
  def inArbUnElim
    (inArbUn: (arbUn body).intp2 fv b c d)
  :
    ∃ dBound, body.intp2 (dBound :: fv) b c d
  :=
    Classical.byContradiction fun h =>
      inArbUn (fun dBound ninBody => h ⟨dBound, ninBody⟩)
  
  
  def inAny: intp2 .any fv b c d := inArbUn d (inVar rfl)
  def ninNone: ¬ intp2 .none fv b c d := (· d rfl)
  def inNoneElim: intp2 .none fv b c d → P := ninNone.elim
  
  def intp2_none_eq_empty:
    intp2 .none fv b c = {}
  :=
    le_antisymm (fun _ => ninNone) nofun
  
  
  abbrev InWfm
    (fv: List Pair)
    (dl: DefList)
    (expr: SingleLaneExpr)
    (d: Pair)
  :
    Prop
  :=
    expr.intp2 fv dl.wfm dl.wfm d
  
  
  def InWfm.of_in_def_no_fv
    (inDef: InWfm [] dl ((dl.getDef x).toLane lane) d)
  :
    InWfm [] dl (.const lane x) d
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel dl]
    exact inDef
  
  
  def InWfm.in_def_no_fv
    (inConst: InWfm [] dl (.const lane x) d)
  :
    InWfm [] dl ((dl.getDef x).toLane lane) d
  :=
    let v := dl.wfm
    
    let eqAtN: v x = dl.triIntp2 v v x :=
      congr (DefList.wfm_isModel dl) rfl
    
    match lane with
    | .defLane => show (dl.triIntp2 v v x).defMem d from eqAtN ▸ inConst
    | .posLane => show (dl.triIntp2 v v x).posMem d from eqAtN ▸ inConst
  
end SingleLaneExpr
