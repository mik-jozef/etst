module
public import Etst.WFC.Ch3_WellFoundedModel

public section
namespace Etst


namespace SingleLaneExpr
  variable
    {expr exprL exprR body left rite: SingleLaneExpr}
    {x: Nat}
    {pA pB pE pBound p: Pair}
    {fv: List Pair}
    {b c: Valuation Pair}
  
  theorem intp2_var_eq_empty
    (nlt: ¬ x < fv.length)
  :
    (var x).intp2 fv b c = {}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  theorem intp2_var_eq_of_lt
    (lt: x < fv.length)
  :
    (var x).intp2 fv b c = {fv[x]}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_getElem lt]
  
  theorem intp2_var_eq_singleton
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp2 fv b c = {pBound}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [eq]
  
  theorem inVar
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    pBound ∈ (var x).intp2 fv b c
  :=
    intp2_var_eq_singleton eq ▸ rfl
  
  theorem inVarEq
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp2 fv b c = {pBound}
  :=
    intp2_var_eq_singleton eq
  
  theorem inVarElim
    (h: p ∈ (var x).intp2 fv b c)
    (eq: fv[x]? = .some pBound)
  :
    p = pBound
  := by
    rw [intp2_var_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  theorem inVarElimLt
    (h: p ∈ (var x).intp2 fv b c)
    (lt: x < fv.length)
  :
    fv[x] = p
  := by
    rw [intp2_var_eq_of_lt lt] at h
    exact Set.mem_singleton_iff.mp h.symm
  
  theorem inVarNope
    (h: p ∈ (var x).intp2 fv b c)
    (nlt: ¬ x < fv.length)
    {P: Prop}
  :
    P
  := by
    rw [intp2_var_eq_empty nlt] at h
    exact h.elim
  
  
  theorem inNull:
    .null ∈ null.intp2 fv b c
  :=
    rfl
  
  theorem inNullElim
    (inNull: p ∈ null.intp2 fv b c)
  :
    p = .null
  :=
    inNull
  
  theorem inNullElimNeq
    (inNull: p ∈ null.intp2 fv b c)
    a b
  :
    p ≠ .pair a b
  :=
    fun eq => Pair.noConfusion (inNull.symm.trans eq)
  
  theorem inNullElimNope
    (inNull: .pair pA pB ∈ null.intp2 fv b c)
    {P: Prop}
  :
    P
  :=
    (inNullElimNeq inNull pA pB rfl).elim
  
  
  theorem inProd
    (inLeft: pA ∈ exprL.intp2 fv b c)
    (inRite: pB ∈ exprR.intp2 fv b c)
  :
    .pair pA pB ∈ (prod exprL exprR).intp2 fv b c
  :=
    ⟨pA, pB, rfl, inLeft, inRite⟩
  
  theorem inProdElim
    (inProd: .pair pA pB ∈ (prod exprL exprR).intp2 fv b c)
  :
    And
      (pA ∈ exprL.intp2 fv b c)
      (pB ∈ exprR.intp2 fv b c)
  :=
    let ⟨_pairL, _pairR, eq, inL, inR⟩ := inProd
    let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
    ⟨eqL ▸ inL, eqR ▸ inR⟩
  
  theorem inProdElimEx
    (inProd: p ∈ (prod exprL exprR).intp2 fv b c)
  :
    ∃ pA pB,
      p = .pair pA pB ∧
      pA ∈ exprL.intp2 fv b c ∧
      pB ∈ exprR.intp2 fv b c
  :=
    match p with
    | .pair pA pB =>
      let ⟨_pairL, _pairR, eq, inL, inR⟩ := inProd
      let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
      ⟨pA, pB, ⟨rfl, eqL ▸ inL, eqR ▸ inR⟩⟩
  
  theorem inProdElimNope
    (inProdNull: .null ∈ (prod exprL exprR).intp2 fv b c)
    {P: Prop}
  :
    P
  :=
    let ⟨_, _, eq, _⟩ := inProdNull
    Pair.noConfusion eq
  
  theorem ninProdElim
    (ninProd: ¬ .pair pA pB ∈ (prod exprL exprR).intp2 fv b c)
  :
    ¬ pA ∈ exprL.intp2 fv b c ∨ ¬ pB ∈ exprR.intp2 fv b c
  :=
    not_and_or.mp fun ⟨inL, inR⟩ =>
      ninProd ⟨pA, pB, rfl, inL, inR⟩
  
  
  theorem inIr
    (l: p ∈ exprL.intp2 fv b c)
    (r: p ∈ exprR.intp2 fv b c)
  :
    p ∈ (ir exprL exprR).intp2 fv b c
  :=
    ⟨l, r⟩
  
  theorem inIrElim
    (inIr: p ∈ (ir exprL exprR).intp2 fv b c)
  :
    And
      (p ∈ exprL.intp2 fv b c)
      (p ∈ exprR.intp2 fv b c)
  :=
    inIr
  
  theorem inIrElimL
    (inIr: p ∈ (ir exprL exprR).intp2 fv b c)
  :
    p ∈ exprL.intp2 fv b c
  :=
    inIr.left

  theorem inIrElimR
    (inIr: p ∈ (ir exprL exprR).intp2 fv b c)
  :
    p ∈ exprR.intp2 fv b c
  :=
    inIr.right
  
  
  theorem inFull
    (p: Pair)
    (allInExpr: (pE: Pair) → pE ∈ expr.intp2 fv b c)
  :
    p ∈ (full expr).intp2 fv b c
  :=
    allInExpr
  
  theorem inFullElim
    -- note we're using null instead of p here because
    -- it is ignored by the interpretation function,
    -- so Lean frequently fails with "don't know how to
    -- synthesize this implicit argument" errors.
    (inFull: p ∈ (full expr).intp2 fv b c)
  :
    ∀ pE, pE ∈ expr.intp2 fv b c
  :=
    inFull
  
  
  theorem inCompl
    (ninBody: ¬ p ∈ body.intp2 fv b c)
  :
    p ∈ (compl body).intp2 fv c b
  :=
    ninBody
  
  theorem inComplElim
    (inCompl: p ∈ (compl body).intp2 fv b c)
  :
    ¬ p ∈ body.intp2 fv c b
  :=
    inCompl
  
  theorem ninCompl
    (inBody: p ∈ body.intp2 fv b c)
  :
    ¬ p ∈ (compl body).intp2 fv c b
  :=
    (· inBody)
  
  
  theorem inArbIr
    {fv: List Pair}
    {b c: Valuation Pair}
    {p: Pair}
    (inBody: ∀ pBound, p ∈ body.intp2 (pBound :: fv) b c)
  :
    p ∈ (arbIr body).intp2 fv b c
  :=
    fun pBound => inBody pBound
  
  
  theorem inArbIrElim
    (inArbIr: p ∈ (arbIr body).intp2 fv b c)
    (pBound: Pair)
  :
    p ∈ body.intp2 (pBound :: fv) b c
  :=
    inArbIr pBound
  
  
  theorem inUnL
    (inLeft: p ∈ left.intp2 fv b c)
  :
    p ∈ (un left rite).intp2 fv b c
  :=
    inCompl (fun ⟨ninL, _⟩ => ninL inLeft)
  
  theorem inUnR
    (inRite: p ∈ rite.intp2 fv b c)
  :
    p ∈ (un left rite).intp2 fv b c
  :=
    inCompl (fun ⟨_, ninR⟩ => ninR inRite)
  
  theorem inUnElim
    (inUn: p ∈ (un left rite).intp2 fv b c)
  :
    p ∈ left.intp2 fv b c ∨ p ∈ rite.intp2 fv b c
  :=
    match Classical.em (p ∈ left.intp2 fv b c) with
    | .inl inL => .inl inL
    | .inr ninL =>
      .inr <| Classical.byContradiction fun ninR =>
        inUn ⟨ninL, ninR⟩
  
  
  theorem inSome
    (p: Pair)
    (inBody: pE ∈ body.intp2 fv b c)
  :
    p ∈ (some body).intp2 fv b c
  :=
    inCompl (fun h => h pE inBody)
  
  theorem inSomeElim
    (inSome: p ∈ (some body).intp2 fv b c)
  :
    ∃ pE, pE ∈ body.intp2 fv b c
  :=
    Classical.byContradiction fun h =>
      inSome (fun pE ninBody => h ⟨pE, ninBody⟩)
  
  
  theorem inArbUn
    (pBound: Pair)
    (inBody: p ∈ body.intp2 (pBound :: fv) b c)
  :
    p ∈ (arbUn body).intp2 fv b c
  :=
    inCompl (fun h => h pBound inBody)
  
  theorem inArbUnElim
    (inArbUn: p ∈ (arbUn body).intp2 fv b c)
  :
    ∃ pBound, p ∈ body.intp2 (pBound :: fv) b c
  :=
    Classical.byContradiction fun h =>
      inArbUn (fun pBound ninBody => h ⟨pBound, ninBody⟩)
  
  
  theorem inAny: p ∈ intp2 .any fv b c := inArbUn p (inVar rfl)
  theorem ninNone: ¬ p ∈ intp2 .none fv b c := (· p rfl)
  theorem inNoneElim {P: Prop}: p ∈ intp2 .none fv b c → P :=
    ninNone.elim
  
  theorem intp2_none_eq_empty:
    intp2 .none fv b c = {}
  :=
    le_antisymm (fun _ => ninNone) nofun
  
  
  exposed def toggle2N (lane: Set3.Lane): Nat → Set3.Lane
  | 0 => lane
  | n+1 => Set3.Lane.toggle (Set3.Lane.toggle (toggle2N lane n))
  
  theorem inToggle2
    (n: Nat)
    {expr: BasicExpr}
    {lane}
    (inToggle: p ∈ intp2 (BasicExpr.toLane expr lane) fv b c)
  :
    p ∈ intp2 (BasicExpr.toLane expr (toggle2N lane n)) fv b c
  :=
    match n with
    | 0 => inToggle
    | n+1 => by
      let ih := inToggle2 n inToggle
      rw [←Set3.Lane.toggle_toggle_eq (toggle2N lane n)] at ih
      exact ih
  
  theorem inToggle2Elim {expr lane}
    (n: Nat)
    (inToggle:
      p ∈ intp2 (BasicExpr.toLane expr (toggle2N lane n)) fv b c)
  :
    p ∈ intp2 (BasicExpr.toLane expr lane) fv b c
  :=
    match n with
    | 0 => inToggle
    | n+1 =>
      inToggle2Elim n ((toggle2N lane n).toggle_toggle_eq ▸ inToggle)
  
  -- Using inToggle2Elim can result in `max recursion depth exceeded`
  -- errors, this is a workaround to that.
  theorem inToggle2Elim' {expr lane lane'}
    (n: Nat)
    (inToggle: p ∈ (BasicExpr.toLane expr lane').intp2 fv b c)
    (laneEq: lane' = SingleLaneExpr.toggle2N lane n)
  :
    p ∈ (BasicExpr.toLane expr lane).intp2 fv b c
  :=
    inToggle2Elim n (laneEq ▸ inToggle)
  
end SingleLaneExpr

namespace DefList
  abbrev InWfm
    (dl: DefList)
    (fv: List Pair := [])
    (expr: SingleLaneExpr)
    (p: Pair)
  :
    Prop
  :=
    p ∈ expr.intp2 fv dl.wfm dl.wfm
  
  theorem InWfm.of_in_def_no_fv {dl x lane p}
    (inDef: InWfm dl [] ((dl.getDef x).toLane lane) p)
  :
    dl.InWfm [] (.const lane x) p
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel dl]
    exact inDef
  
  theorem InWfm.in_def_no_fv {dl x lane p}
    (inConst: InWfm dl [] (.const lane x) p)
  :
    dl.InWfm [] ((dl.getDef x).toLane lane) p
  :=
    let v := dl.wfm
    
    let eqAtN: v x = dl.intpDefs v x :=
      congr (DefList.wfm_isModel dl) rfl
    
    match lane with
    | .defLane =>
        show p ∈ (dl.intpDefs v x).defMem from eqAtN ▸ inConst
    | .posLane =>
        show p ∈ (dl.intpDefs v x).posMem from eqAtN ▸ inConst
  
end DefList
