module
public import Etst.WFC.Ch3_WellFoundedModel

public section
namespace Etst


theorem ExprKind.Lane.toggle_toggle {kind}
  (lane: ExprKind.Lane kind)
:
  lane = lane.toggle.toggle
:=
  match kind, lane with
  | .basic, .defLane => rfl
  | .basic, .posLane => rfl
  | .lane, _ => rfl

namespace Expr
  variable
    {kind: ExprKind}
    {lane: kind.Lane}
    {expr exprL exprR body left rite: Expr kind}
    {x: Nat}
    {pA pB pE pBound p: Pair}
    {fv: List Pair}
    {b c: Valuation Pair}
  
  
  theorem inToggle2
    (inToggle: p ∈ expr.intp lane b c fv)
  :
    p ∈ expr.intp lane.toggle.toggle b c fv
  :=
    lane.toggle_toggle ▸ inToggle
  
  theorem inToggle2Elim
    (inToggle: p ∈ expr.intp lane.toggle.toggle b c fv)
  :
    p ∈ expr.intp lane b c fv
  :=
    lane.toggle_toggle ▸ inToggle
  
  
  theorem intp_var_eq_empty
    (nlt: ¬ x < fv.length)
  :
    (var x).intp lane b c fv = {}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_none_iff.mpr (le_of_not_gt nlt)]
  
  theorem intp_var_eq_of_lt
    (lt: x < fv.length)
  :
    (var x).intp lane b c fv = {fv[x]}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [List.getElem?_eq_getElem lt]
  
  theorem intp_var_eq_singleton
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp lane b c fv = {pBound}
  := by
    show intpVar fv x = _
    unfold intpVar
    rw [eq]
  
  theorem inVar
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    pBound ∈ (var x).intp lane b c fv
  :=
    intp_var_eq_singleton eq ▸ rfl
  
  theorem inVarEq
    {fv: List Pair}
    {pBound: Pair}
    (eq: fv[x]? = .some pBound)
  :
    (var x).intp lane b c fv = {pBound}
  :=
    intp_var_eq_singleton eq
  
  theorem inVarElim
    (h: p ∈ (var x).intp lane b c fv)
    (eq: fv[x]? = .some pBound)
  :
    p = pBound
  := by
    rw [intp_var_eq_singleton eq] at h
    exact Set.mem_singleton_iff.mp h
  
  theorem inVarElimLt
    (h: p ∈ (var x).intp lane b c fv)
    (lt: x < fv.length)
  :
    fv[x] = p
  := by
    rw [intp_var_eq_of_lt lt] at h
    exact Set.mem_singleton_iff.mp h.symm
  
  theorem inVarNope
    (h: p ∈ (var x).intp lane b c fv)
    (nlt: ¬ x < fv.length)
    {P: Prop}
  :
    P
  := by
    rw [intp_var_eq_empty nlt] at h
    exact h.elim
  
  
  theorem inNull:
    .null ∈ null.intp lane b c fv
  :=
    rfl
  
  theorem inNullElim
    (inNull: p ∈ null.intp lane b c fv)
  :
    p = .null
  :=
    inNull
  
  theorem inNullElimNeq
    (inNull: p ∈ null.intp lane b c fv)
    a b
  :
    p ≠ .pair a b
  :=
    fun eq => Pair.noConfusion (inNull.symm.trans eq)
  
  theorem inNullElimNope
    (inNull: .pair pA pB ∈ null.intp lane b c fv)
    {P: Prop}
  :
    P
  :=
    (inNullElimNeq inNull pA pB rfl).elim
  
  
  theorem inProd
    (inLeft: pA ∈ exprL.intp lane b c fv)
    (inRite: pB ∈ exprR.intp lane b c fv)
  :
    .pair pA pB ∈ (prod exprL exprR).intp lane b c fv
  :=
    ⟨pA, pB, rfl, inLeft, inRite⟩
  
  theorem inProdElim
    (inProd: .pair pA pB ∈ (prod exprL exprR).intp lane b c fv)
  :
    And
      (pA ∈ exprL.intp lane b c fv)
      (pB ∈ exprR.intp lane b c fv)
  :=
    let ⟨_pairL, _pairR, eq, inL, inR⟩ := inProd
    let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
    ⟨eqL ▸ inL, eqR ▸ inR⟩
  
  theorem inProdElimEx
    (inProd: p ∈ (prod exprL exprR).intp lane b c fv)
  :
    ∃ pA pB,
      p = .pair pA pB ∧
      pA ∈ exprL.intp lane b c fv ∧
      pB ∈ exprR.intp lane b c fv
  :=
    match p with
    | .pair pA pB =>
      let ⟨_pairL, _pairR, eq, inL, inR⟩ := inProd
      let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
      ⟨pA, pB, ⟨rfl, eqL ▸ inL, eqR ▸ inR⟩⟩
  
  theorem inProdElimNope
    (inProdNull: .null ∈ (prod exprL exprR).intp lane b c fv)
    {P: Prop}
  :
    P
  :=
    let ⟨_, _, eq, _⟩ := inProdNull
    Pair.noConfusion eq
  
  theorem ninProdElim
    (ninProd: ¬ .pair pA pB ∈ (prod exprL exprR).intp lane b c fv)
  :
    ¬ pA ∈ exprL.intp lane b c fv ∨ ¬ pB ∈ exprR.intp lane b c fv
  :=
    not_and_or.mp fun ⟨inL, inR⟩ =>
      ninProd ⟨pA, pB, rfl, inL, inR⟩
  
  
  theorem inIr
    (l: p ∈ exprL.intp lane b c fv)
    (r: p ∈ exprR.intp lane b c fv)
  :
    p ∈ (ir exprL exprR).intp lane b c fv
  :=
    ⟨l, r⟩
  
  theorem inIrElim
    (inIr: p ∈ (ir exprL exprR).intp lane b c fv)
  :
    And
      (p ∈ exprL.intp lane b c fv)
      (p ∈ exprR.intp lane b c fv)
  :=
    inIr
  
  theorem inIrElimL
    (inIr: p ∈ (ir exprL exprR).intp lane b c fv)
  :
    p ∈ exprL.intp lane b c fv
  :=
    inIr.left

  theorem inIrElimR
    (inIr: p ∈ (ir exprL exprR).intp lane b c fv)
  :
    p ∈ exprR.intp lane b c fv
  :=
    inIr.right
  
  
  theorem inFull
    (p: Pair)
    (allInExpr: (pE: Pair) → pE ∈ expr.intp lane b c fv)
  :
    p ∈ (full expr).intp lane b c fv
  :=
    allInExpr
  
  theorem inFullElim
    -- note we're using null instead of p here because
    -- it is ignored by the interpretation function,
    -- so Lean frequently fails with "don't know how to
    -- synthesize this implicit argument" errors.
    (inFull: p ∈ (full expr).intp lane b c fv)
  :
    ∀ pE, pE ∈ expr.intp lane b c fv
  :=
    inFull
  
  
  theorem inCompl
    (ninBody: ¬ p ∈ body.intp lane.toggle b c fv)
  :
    p ∈ (compl body).intp lane c b fv
  :=
    lane.toggle_toggle ▸ ninBody
  
  theorem inComplToggle
    (ninBody: ¬ p ∈ body.intp lane b c fv)
  :
    p ∈ (compl body).intp lane.toggle c b fv
  :=
    inCompl (lane.toggle_toggle ▸ ninBody)
  
  theorem inComplElim
    (inCompl: p ∈ (compl body).intp lane b c fv)
  :
    ¬ p ∈ body.intp lane.toggle c b fv
  :=
    inCompl
  
  theorem inComplToggleElim
    (inCompl: p ∈ (compl body).intp lane.toggle b c fv)
  :
    ¬ p ∈ body.intp lane c b fv
  :=
    lane.toggle_toggle ▸ inCompl
  
  theorem ninCompl
    (inBody: p ∈ body.intp lane.toggle b c fv)
  :
    ¬ p ∈ (compl body).intp lane c b fv
  :=
    match kind, lane with
    | .basic, .defLane => (· inBody)
    | .basic, .posLane => (· inBody)
    | .lane, _ => (· inBody)
  
  theorem ninComplToggle
    (inBody: p ∈ body.intp lane b c fv)
  :
    ¬ p ∈ (compl body).intp lane.toggle c b fv
  :=
    match kind, lane with
    | .basic, .defLane => (· inBody)
    | .basic, .posLane => (· inBody)
    | .lane, _ => (· inBody)
  
  
  theorem inArbIr
    {fv: List Pair}
    {b c: Valuation Pair}
    {p: Pair}
    (inBody: ∀ pBound, p ∈ body.intp lane b c (pBound :: fv))
  :
    p ∈ (arbIr body).intp lane b c fv
  :=
    fun pBound => inBody pBound
  
  
  theorem inArbIrElim
    (inArbIr: p ∈ (arbIr body).intp lane b c fv)
    (pBound: Pair)
  :
    p ∈ body.intp lane b c (pBound :: fv)
  :=
    inArbIr pBound
  
  
  theorem inUnL
    (inLeft: p ∈ left.intp lane b c fv)
  :
    p ∈ (un left rite).intp lane b c fv
  :=
    inCompl fun ⟨ninL, _⟩ => ninL (inToggle2 inLeft)
  
  theorem inUnR
    (inRite: p ∈ rite.intp lane b c fv)
  :
    p ∈ (un left rite).intp lane b c fv
  :=
    inCompl fun ⟨_, ninR⟩ => ninR (inToggle2 inRite)
  
  theorem inUnElim
    (inUn: p ∈ (un left rite).intp lane b c fv)
  :
    p ∈ left.intp lane b c fv ∨ p ∈ rite.intp lane b c fv
  :=
    match Classical.em (p ∈ left.intp lane b c fv) with
    | .inl inL => .inl inL
    | .inr ninL =>
      .inr <| Classical.byContradiction fun ninR =>
        inUn ⟨
          fun h => ninL (inToggle2Elim h),
          fun h => ninR (inToggle2Elim h)
        ⟩
  
  
  theorem inSome
    (p: Pair)
    (inBody: pE ∈ body.intp lane b c fv)
  :
    p ∈ (some body).intp lane b c fv
  :=
    inCompl fun h => h pE (inToggle2 inBody)
  
  theorem inSomeElim
    (inSome: p ∈ (some body).intp lane b c fv)
  :
    ∃ pE, pE ∈ body.intp lane b c fv
  :=
    Classical.byContradiction fun h =>
      inSome (fun pE ninBody => h ⟨pE, inToggle2Elim ninBody⟩)
  
  
  theorem inArbUn
    (pBound: Pair)
    (inBody: p ∈ body.intp lane b c (pBound :: fv))
  :
    p ∈ (arbUn body).intp lane b c fv
  :=
    inCompl fun h => h pBound (inToggle2 inBody)
  
  theorem inArbUnElim
    (inArbUn: p ∈ (arbUn body).intp lane b c fv)
  :
    ∃ pBound, p ∈ body.intp lane b c (pBound :: fv)
  :=
    Classical.byContradiction fun h =>
      inArbUn (fun pBound ninBody => h ⟨pBound, inToggle2Elim ninBody⟩)
  
  
  theorem inAny: p ∈ intp .any lane b c fv := inArbUn p (inVar rfl)
  theorem ninNone: ¬ p ∈ intp .none lane b c fv := (· p rfl)
  theorem inNoneElim {P: Prop}: p ∈ intp .none lane b c fv → P :=
    ninNone.elim
  
  theorem intp_none_eq_empty:
    intp .none lane b c fv = {}
  :=
    le_antisymm (fun _ => ninNone) nofun
  
end Expr

namespace DefList
  abbrev InWfm {kind}
    (dl: DefList)
    (expr: Expr kind)
    (lane: kind.Lane)
    (fv: List Pair := [])
    (p: Pair)
  :
    Prop
  :=
    p ∈ expr.intp lane dl.wfm dl.wfm fv
  
  theorem InWfm.of_in_def_no_fv {dl x lane p}
    (inDef: InWfm dl (dl.getDef x) lane [] p)
  :
    dl.InWfm (.const () x) lane [] p
  := by
    cases lane
    all_goals
    unfold InWfm
    rw [DefList.wfm_isModel dl]
    exact inDef
  
  theorem InWfm.in_def_no_fv {dl x lane p}
    (inConst: InWfm dl (.const () x) lane [] p)
  :
    dl.InWfm (dl.getDef x) lane [] p
  :=
    let eqAtN: dl.wfm x = dl.intpDefs dl.wfm dl.wfm x :=
      congr (DefList.wfm_isModel dl) rfl
    match lane with
    | .defLane =>
        show p ∈ (dl.intpDefs dl.wfm dl.wfm x).defMem from
        eqAtN ▸ inConst
    | .posLane =>
        show p ∈ (dl.intpDefs dl.wfm dl.wfm x).posMem from
        eqAtN ▸ inConst
  
end DefList
