import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Valuation

namespace Etst


namespace SingleLaneExpr
  variable
    {expr exprL exprR body left rite: SingleLaneExpr}
    {x: Nat}
    {pA pB pE pBound p: Pair}
    {fv: List Pair}
    {b c o: Valuation Pair}
  
  def intp2_var_eq_empty
    (nlt: ¬ x < fv.length)
  :
    (var x).intp2 fv b c o = {}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  def intp2_var_eq_of_lt
    (lt: x < fv.length)
  :
    (var x).intp2 fv b c o = {fv[x]}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_getElem lt]
  
  def intp2_var_eq_singleton
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp2 fv b c o = {pBound}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [eq]
  
  def inVar
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp2 fv b c o pBound
  :=
    intp2_var_eq_singleton eq ▸ rfl
  
  def inVarEq
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp2 fv b c o = {pBound}
  :=
    intp2_var_eq_singleton eq ▸ rfl
  
  def inVarElim
    (h: (var x).intp2 fv b c o p)
    (eq: fv[x]? = .some pBound)
  :
    p = pBound
  := by
    rw [intp2_var_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  def inVarElimLt
    (h: (var x).intp2 fv b c o p)
    (lt: x < fv.length)
  :
    fv[x] = p
  := by
    rw [intp2_var_eq_of_lt lt] at h
    exact Set.mem_singleton_iff.mp h.symm
  
  def inVarNope
    (h: (var x).intp2 fv b c o p)
    (nlt: ¬ x < fv.length)
    {P: Prop}
  :
    P
  := by
    rw [intp2_var_eq_empty nlt] at h
    exact h.elim
  
  
  def inNull:
    null.intp2 fv b c o .null
  :=
    rfl
  
  def inNullElim
    (inNull: null.intp2 fv b c o p)
  :
    p = .null
  :=
    inNull
  
  def inNullElimNeq
    (inNull: null.intp2 fv b c o p)
    a b
  :
    p ≠ .pair a b
  :=
    fun eq => Pair.noConfusion (inNull.symm.trans eq)
  
  def inNullElimNope
    (inNull: null.intp2 fv b c o (.pair pA pB))
    {P: Prop}
  :
    P
  :=
    (inNullElimNeq inNull pA pB rfl).elim
  
  
  def inProd
    (inLeft: exprL.intp2 fv b c o pA)
    (inRite: exprR.intp2 fv b c o pB)
  :
    (prod exprL exprR).intp2 fv b c o (.pair pA pB)
  :=
    ⟨pA, pB, rfl, inLeft, inRite⟩
  
  def inProdElim
    (inProd: (prod exprL exprR).intp2 fv b c o (.pair pA pB))
  :
    And
      (exprL.intp2 fv b c o pA)
      (exprR.intp2 fv b c o pB)
  :=
    let ⟨_pairL, _pairR, eq, inL, inR⟩ := inProd
    let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
    ⟨eqL ▸ inL, eqR ▸ inR⟩
  
  def inProdElimEx
    (inProd: (prod exprL exprR).intp2 fv b c o p)
  :
    ∃ pA pB,
      p = .pair pA pB ∧
      exprL.intp2 fv b c o pA ∧
      exprR.intp2 fv b c o pB
  :=
    match p with
    | .pair pA pB =>
      let ⟨_pairL, _pairR, eq, inL, inR⟩ := inProd
      let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
      ⟨pA, pB, ⟨rfl, eqL ▸ inL, eqR ▸ inR⟩⟩
  
  def inProdElimNope
    (inProdNull: (prod exprL exprR).intp2 fv b c o .null)
    {P: Prop}
  :
    P
  :=
    let ⟨_, _, eq, _⟩ := inProdNull
    Pair.noConfusion eq
  
  def ninProdElim
    (ninProd: ¬ (prod exprL exprR).intp2 fv b c o (.pair pA pB))
  :
    ¬ exprL.intp2 fv b c o pA ∨ ¬ exprR.intp2 fv b c o pB
  :=
    not_and_or.mp fun ⟨inL, inR⟩ =>
      ninProd ⟨pA, pB, rfl, inL, inR⟩
  
  
  def inIr
    (l: exprL.intp2 fv b c o p)
    (r: exprR.intp2 fv b c o p)
  :
    (ir exprL exprR).intp2 fv b c o p
  :=
    ⟨l, r⟩
  
  def inIrElim
    (inIr: (ir exprL exprR).intp2 fv b c o p)
  :
    And
      (exprL.intp2 fv b c o p)
      (exprR.intp2 fv b c o p)
  :=
    inIr
  
  def inIrElimL
    (inIr: (ir exprL exprR).intp2 fv b c o p)
  :
    exprL.intp2 fv b c o p
  :=
    inIr.left

  def inIrElimR
    (inIr: (ir exprL exprR).intp2 fv b c o p)
  :
    exprR.intp2 fv b c o p
  :=
    inIr.right
  
  
  def inFull
    (p: Pair)
    (allInExpr: (pE: Pair) → expr.intp2 fv b c o pE)
  :
    (full expr).intp2 fv b c o p
  :=
    allInExpr
  
  def inFullElim
    -- note we're using null instead of p here because
    -- it is ignored by the interpretation function,
    -- so Lean frequently fails with "don't know how to
    -- synthesize this implicit argument" errors.
    (inFull: (full expr).intp2 fv b c o .null)
  :
    ∀ pE, expr.intp2 fv b c o pE
  :=
    inFull
  
  
  def inCompl
    (ninBody: ¬body.intp2 fv b c o p)
  :
    (compl body).intp2 fv c b o p
  :=
    ninBody
  
  def inComplElim
    (inCompl: (compl body).intp2 fv b c o p)
  :
    ¬body.intp2 fv c b o p
  :=
    inCompl
  
  def ninCompl
    (inBody: body.intp2 fv b c o p)
  :
    ¬(compl body).intp2 fv c b o p
  :=
    (· inBody)
  
  
  def inArbIr
    {fv: List Pair}
    {b c: Valuation Pair}
    {p: Pair}
    (inBody: ∀ pBound, body.intp2 (pBound :: fv) b c o p)
  :
    (arbIr body).intp2 fv b c o p
  :=
    fun pBound => inBody pBound
  
  
  def inArbIrElim
    (inArbIr: (arbIr body).intp2 fv b c o p)
    (pBound: Pair)
  :
    body.intp2 (pBound :: fv) b c o p
  :=
    inArbIr pBound
  
  
  def inUnL
    (inLeft: left.intp2 fv b c o p)
  :
    (un left rite).intp2 fv b c o p
  :=
    inCompl (fun ⟨ninL, _⟩ => ninL inLeft)
  
  def inUnR
    (inRite: rite.intp2 fv b c o p)
  :
    (un left rite).intp2 fv b c o p
  :=
    inCompl (fun ⟨_, ninR⟩ => ninR inRite)
  
  def inUnElim
    (inUn: (un left rite).intp2 fv b c o p)
  :
    Or (left.intp2 fv b c o p) (rite.intp2 fv b c o p)
  :=
    match Classical.em (left.intp2 fv b c o p) with
    | .inl inL => .inl inL
    | .inr ninL =>
      .inr <| Classical.byContradiction fun ninR =>
        inUn ⟨ninL, ninR⟩
  
  
  def inSome
    (p: Pair)
    (inBody: body.intp2 fv b c o pE)
  :
    (some body).intp2 fv b c o p
  :=
    inCompl (fun h => h pE inBody)
  
  def inSomeElim
    (inSome: (some body).intp2 fv b c o p)
  :
    ∃ pE, body.intp2 fv b c o pE
  :=
    Classical.byContradiction fun h =>
      inSome (fun pE ninBody => h ⟨pE, ninBody⟩)
  
  
  def inArbUn
    (pBound: Pair)
    (inBody: body.intp2 (pBound :: fv) b c o p)
  :
    (arbUn body).intp2 fv b c o p
  :=
    inCompl (fun h => h pBound inBody)
  
  def inArbUnElim
    (inArbUn: (arbUn body).intp2 fv b c o p)
  :
    ∃ pBound, body.intp2 (pBound :: fv) b c o p
  :=
    Classical.byContradiction fun h =>
      inArbUn (fun pBound ninBody => h ⟨pBound, ninBody⟩)
  
  
  def inAny: intp2 .any fv b c o p := inArbUn p (inVar rfl)
  def ninNone: ¬ intp2 .none fv b c o p := (· p rfl)
  def inNoneElim {P}: intp2 .none fv b c o p → P := ninNone.elim
  
  def intp2_none_eq_empty:
    intp2 .none fv b c o = {}
  :=
    le_antisymm (fun _ => ninNone) nofun
  
  
  def toggle2N (lane: Set3.Lane): Nat → Set3.Lane
  | 0 => lane
  | n+1 => Set3.Lane.toggle (Set3.Lane.toggle (toggle2N lane n))
  
  def inToggle2
    (n: Nat)
    {expr: BasicExpr}
    {lane}
    (inToggle: intp2 (BasicExpr.toLane expr lane) fv b c o p)
  :
    intp2 (BasicExpr.toLane expr (toggle2N lane n)) fv b c o p
  :=
    match n with
    | 0 => inToggle
    | n+1 => by
      let ih := inToggle2 n inToggle
      rw [←Set3.Lane.toggle_toggle_eq (toggle2N lane n)] at ih
      exact ih
  
  def inToggle2Elim
    (n: Nat)
    {expr: BasicExpr}
    {lane}
    (inToggle:
      intp2 (BasicExpr.toLane expr (toggle2N lane n)) fv b c o p)
  :
    intp2 (BasicExpr.toLane expr lane) fv b c o p
  :=
    match n with
    | 0 => inToggle
    | n+1 =>
      let inToggle:
        (expr.toLane (toggle2N lane n).toggle.toggle).intp2 fv b c o p
      :=
        inToggle
      inToggle2Elim n (by
        rw [Set3.Lane.toggle_toggle_eq] at inToggle
        exact inToggle)
  
end SingleLaneExpr

namespace DefList
  abbrev InWfm
    (dl: DefList)
    (o: Valuation Pair)
    (fv: List Pair := [])
    (expr: SingleLaneExpr)
    (p: Pair)
  :
    Prop
  :=
    expr.intp2 fv (dl.wfm o) (dl.wfm o) o p
  
  def InWfm.of_in_def_no_fv {dl o x lane p}
    (inDef: InWfm dl o [] ((dl.getDef x).toLane lane) p)
  :
    dl.InWfm o [] (.const lane x) p
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel dl o]
    exact inDef
  
  def InWfm.in_def_no_fv {dl o x lane p}
    (inConst: InWfm dl o [] (.const lane x) p)
  :
    dl.InWfm o [] ((dl.getDef x).toLane lane) p
  :=
    let v := dl.wfm o
    
    let eqAtN: v x = dl.intpDefs v o x :=
      congr (DefList.wfm_isModel dl o) rfl
    
    match lane with
    | .defLane => show (dl.intpDefs v o x).defMem p from eqAtN ▸ inConst
    | .posLane => show (dl.intpDefs v o x).posMem p from eqAtN ▸ inConst
  
end DefList
