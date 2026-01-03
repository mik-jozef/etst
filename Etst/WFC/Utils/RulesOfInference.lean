import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Valuation

namespace Etst

namespace SingleLaneExpr
  def intp2_bvar_eq_empty
    (nlt: ¬ x < bv.length)
  :
    (bvar x).intp2 bv b c = {}
  := by
    show intp2Bvar bv x = _
    unfold intp2Bvar
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def intp2_bvar_eq_of_lt
    (lt: x < bv.length)
  :
    (bvar x).intp2 bv b c = {bv[x]}
  := by
    show intp2Bvar bv x = _
    unfold intp2Bvar
    rw [List.getElem?_eq_getElem lt]
  
  def intp2_bvar_eq_singleton
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
    intp2_bvar_eq_singleton eq ▸ rfl
  
  def inBvarElim
    (h: (bvar x).intp2 bv b c d)
    (eq: bv[x]? = some dBound)
  :
    d = dBound
  := by
    rw [intp2_bvar_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  
  def inNull:
    null.intp2 bv b c .null
  :=
    rfl
  
  def inNullElim
    (inNull: null.intp2 bv b c d)
  :
    d = .null
  :=
    inNull
  
  def inNullElimNeq
    (inNull: null.intp2 bv b c d)
    a b
  :
    d ≠ Pair.pair a b
  :=
    fun eq => Pair.noConfusion (inNull.symm.trans eq)
  
  def inNullElimPair
    (inNull: null.intp2 bv b c (Pair.pair pA pB))
    {P: Prop}
  :
    P
  :=
    (inNullElimNeq inNull pA pB rfl).elim
  
  
  def inPair
    (inLeft: exprL.intp2 bv b c pA)
    (inRite: exprR.intp2 bv b c pB)
  :
    (pair exprL exprR).intp2 bv b c (Pair.pair pA pB)
  :=
    ⟨pA, pB, rfl, inLeft, inRite⟩
  
  def inPairElim
    (inPair: (pair exprL exprR).intp2 bv b c (Pair.pair pA pB))
  :
    And
      (exprL.intp2 bv b c pA)
      (exprR.intp2 bv b c pB)
  :=
    let ⟨_pairL, _pairR, eq, inL, inR⟩ := inPair
    let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
    ⟨eqL ▸ inL, eqR ▸ inR⟩
  
  def inPairElimEx
    (inPair: (pair exprL exprR).intp2 bv b c d)
  :
    ∃ pA pB,
      d = Pair.pair pA pB ∧
      exprL.intp2 bv b c pA ∧
      exprR.intp2 bv b c pB
  :=
    match d with
    | Pair.pair pA pB =>
      let ⟨_pairL, _pairR, eq, inL, inR⟩ := inPair
      let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
      ⟨pA, pB, ⟨rfl, eqL ▸ inL, eqR ▸ inR⟩⟩
  
  def inPairElimNope
    (inPair: (pair exprL exprR).intp2 bv b c .null)
    {P: Prop}
  :
    P
  :=
    let ⟨_, _, eq, _⟩ := inPair
    Pair.noConfusion eq
  
  
  def inIr
    (l: exprL.intp2 bv b c d)
    (r: exprR.intp2 bv b c d)
  :
    (ir exprL exprR).intp2 bv b c d
  :=
    ⟨l, r⟩
  
  def inIrElim
    (inIr: (ir exprL exprR).intp2 bv b c d)
  :
    And
      (exprL.intp2 bv b c d)
      (exprR.intp2 bv b c d)
  :=
    inIr
  
  def inIrElimL
    (inIr: (ir exprL exprR).intp2 bv b c d)
  :
    exprL.intp2 bv b c d
  :=
    inIr.left

  def inIrElimR
    (inIr: (ir exprL exprR).intp2 bv b c d)
  :
    exprR.intp2 bv b c d
  :=
    inIr.right
  
  
  def inCondFull
    (d: Pair)
    (allInExpr: (dE: Pair) → expr.intp2 bv b c dE)
  :
    (condFull expr).intp2 bv b c d
  :=
    allInExpr
  
  def inCondFullElim
    -- note we're using null instead of d here because
    -- it is ignored by the interpretation function,
    -- so Lean frequently fails with "don't know how to
    -- synthesize this implicit argument" errors.
    (inCondFull: (condFull expr).intp2 bv b c .null)
  :
    ∀ dE, expr.intp2 bv b c dE
  :=
    inCondFull
  
  
  def inCompl
    (ninBody: ¬body.intp2 bv b c d)
  :
    (compl body).intp2 bv c b d
  :=
    ninBody
  
  def inComplElim
    (inCompl: (compl body).intp2 bv b c d)
  :
    ¬body.intp2 bv c b d
  :=
    inCompl
  
  def ninCompl
    (inBody: body.intp2 bv b c d)
  :
    ¬(compl body).intp2 bv c b d
  :=
    (· inBody)
  
  
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
  
  
  def inUnL
    (inLeft: left.intp2 bv b c d)
  :
    (un left rite).intp2 bv b c d
  :=
    inCompl (fun ⟨ninL, _⟩ => ninL inLeft)
  
  def inUnR
    (inRite: rite.intp2 bv b c d)
  :
    (un left rite).intp2 bv b c d
  :=
    inCompl (fun ⟨_, ninR⟩ => ninR inRite)
  
  def inUnElim
    (inUn: (un left rite).intp2 bv b c d)
  :
    Or (left.intp2 bv b c d) (rite.intp2 bv b c d)
  :=
    match Classical.em (left.intp2 bv b c d) with
    | .inl inL => .inl inL
    | .inr ninL =>
      .inr <| Classical.byContradiction fun ninR =>
        inUn ⟨ninL, ninR⟩
  
  
  def inCondSome
    (d: Pair)
    (inBody: body.intp2 bv b c dE)
  :
    (condSome body).intp2 bv b c d
  :=
    inCompl (fun h => h dE inBody)
  
  def inCondSomeElim
    (inCondSome: (condSome body).intp2 bv b c d)
  :
    ∃ dE, body.intp2 bv b c dE
  :=
    Classical.byContradiction fun h =>
      inCondSome (fun dE ninBody => h ⟨dE, ninBody⟩)
  
  
  def inArbUn
    (dBound: Pair)
    (inBody: body.intp2 (dBound :: bv) b c d)
  :
    (arbUn body).intp2 bv b c d
  :=
    inCompl (fun h => h dBound inBody)
  
  def inArbUnElim
    (inArbUn: (arbUn body).intp2 bv b c d)
  :
    ∃ dBound, body.intp2 (dBound :: bv) b c d
  :=
    Classical.byContradiction fun h =>
      inArbUn (fun dBound ninBody => h ⟨dBound, ninBody⟩)
  
  
  def inAny: intp2 .any bv b c d := inArbUn d (inBvar rfl)
  def ninNone: ¬ intp2 .none bv b c d := ninCompl inAny
  def inNoneElim: intp2 .none bv b c d → P := ninNone.elim
  
  def intp2_none_eq_empty:
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
