import Etst.WFC.Utils.SelfDefinability.UniSetMapDl

namespace Etst.uniSetMapDl
open SingleLaneExpr


def InUniSetMapAt (dl n fv b c expr lane p) :=
  let vars := [
    BasicExpr.encoding expr,
    Pair.listEncoding fv,
    DefList.prefixEncoding dl n,
  ]
  (exprEncList.toLane lane).intp2 vars b c p

def isAtOfInsDef {dl n fv b c lane expr p}
  (ins:
    ((uniSetMapDl.getDef consts.uniSetMap).toLane lane).intp2
      []
      b
      c
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  InUniSetMapAt dl n fv b c expr lane p
:=
  let ⟨dlEnc, ins⟩ := inArbUnElim ins
  let ⟨fvEnc, ins⟩ := inArbUnElim ins
  let ⟨exprEnc, ins⟩ := inArbUnElim ins
  let ⟨insEnc, insAt⟩ := inPairElim ins
  let ⟨dlEncEq, fvEncEq, exprEncEq⟩ :=
    let ⟨insDl, ins⟩ := inPairElim insEnc
    let ⟨insFv, insExpr⟩ := inPairElim ins
    And.intro
      (inVarElim insDl rfl)
      (And.intro
        (inVarElim insFv rfl)
        (inVarElim insExpr rfl))
  by
  unfold InUniSetMapAt
  exact dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ inToggle2Elim 3 insAt


/-
  ## Section: Non-matching expression encoding eliminators
-/

def isAtIndexNope
  {actual expected enc fv b c p indexExpr restExpr aliasVar}
  (insExprGuard:
    let expr := .some (ir (pair indexExpr restExpr) (var aliasVar))
    intp2 expr fv b c p)
  (evalActual: fv[aliasVar]? = .some (.pair (.nat actual) enc))
  (evalIndex:
    ∀ {d},
      indexExpr.intp2 fv b c d →
      d = Pair.nat expected)
  (indexNeq: actual ≠ expected)
  {P: Prop}
:
  P
:=
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqActual: _ = Pair.nat actual :=
      Pair.noConfusion (inVarElim insGuardR evalActual) fun eq _ => eq
    let eqExpected := evalIndex insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqActual.symm.trans eqExpected)))

def isAtConstNope {fv b c lane i enc p}
  (ins:
    (exprEncConst.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 0)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 0)) indexNeq

def isAtVarNope {fv b c lane i enc p}
  (ins:
    (exprEncVar.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 1)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 1)) indexNeq

def isAtNullNope {fv b c lane i enc p}
  (ins:
    (exprEncNull.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 2)
  {P: Prop}
:
  P
:=
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 2)) indexNeq

def isAtPairNope {fv b c lane i enc p}
  (ins:
    (exprEncPair.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 3)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 3)) indexNeq

def isAtIrNope {fv b c lane i enc p}
  (ins:
    (exprEncIr.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 4)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 4)) indexNeq

def isAtFullNope {fv b c lane i enc p}
  (ins:
    (exprEncFull.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 5)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 5)) indexNeq

def isAtComplNope {fv b c lane i enc p}
  (ins:
    (exprEncCompl.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 6)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 6)) indexNeq

def isAtArbIrNope {fv b c lane i enc p}
  (ins:
    (exprEncArbIr.toLane lane).intp2
      (.pair (.nat i) enc :: fv) b c p)
  (indexNeq: i ≠ 7)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 7)) indexNeq

def exprEncListElim {fv b c lane p}
  {P: Prop}
  (ins: (exprEncList.toLane lane).intp2 fv b c p)
  (onConst: (exprEncConst.toLane (toggle2N lane 1)).intp2 fv b c p → P)
  (onVar: (exprEncVar.toLane (toggle2N lane 2)).intp2 fv b c p → P)
  (onNull: (exprEncNull.toLane (toggle2N lane 3)).intp2 fv b c p → P)
  (onPair: (exprEncPair.toLane (toggle2N lane 4)).intp2 fv b c p → P)
  (onIr: (exprEncIr.toLane (toggle2N lane 5)).intp2 fv b c p → P)
  (onFull: (exprEncFull.toLane (toggle2N lane 6)).intp2 fv b c p → P)
  (onCompl: (exprEncCompl.toLane (toggle2N lane 7)).intp2 fv b c p → P)
  (onArbIr: (exprEncArbIr.toLane (toggle2N lane 7)).intp2 fv b c p → P)
:
  P
:=
  match inUnElim ins with
  | Or.inl ins => onConst ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onVar ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onNull ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onPair ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onIr ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onFull ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onCompl ins
  | Or.inr ins => onArbIr ins


/-
  ## Section: Matching expression encoding eliminators
-/

def exprGuardElimUnary {i iEnc encRest fv0 fvRest b c p}
  (ins:
    intp2
      (some (ir (pair i (var 0)) (var 1)))
      (fv0 :: .pair iEnc encRest :: fvRest)
      b
      c
      p)
:
  encRest = fv0
:=
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim ins
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨_, insVar⟩ := inPairElim insGuardL
    let eqRest :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun _ => id
    eqRest.symm.trans (inVarElim insVar rfl)

def exprGuardElimBinary {i iEnc encL encR fvRite fvLeft fvRest b c p}
  (ins:
    intp2
      (some (ir (pair i (pair (var 1) (var 0))) (var 2)))
      (fvRite :: fvLeft :: .pair iEnc (.pair encL encR) :: fvRest)
      b
      c
      p)
:
  encL = fvLeft ∧ encR = fvRite
:=
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim ins
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ exprGuardTuple =>
    let ⟨_, insTuple⟩ := inPairElim insGuardL
    match exprGuardTuple with
    | .null => inPairElimNope insTuple
    | .pair _ _ =>
      let ⟨insLeft, insRite⟩ := inPairElim insTuple
      let eqRest :=
        Pair.noConfusion (inVarElim insGuardR rfl) fun _ eq => eq
      let eqL := Pair.noConfusion eqRest fun l _ => l
      let eqR := Pair.noConfusion eqRest fun _ r => r
      And.intro
        (eqL.symm.trans (inVarElim insLeft rfl))
        (eqR.symm.trans (inVarElim insRite rfl))

def singleCallElim
  {dl n fv b c expr lane p pArg fvRest eDl eFv eExpr exprEnc}
  (toggleCount)
  (inMap:
    (uniSetMapConst.toLane (toggle2N lane toggleCount)).intp2
      fvRest b c (.pair pArg p))
  (inArg: (pair eDl (pair eFv eExpr)).intp2 fvRest b c pArg)
  (exprEncEq: expr.encoding = exprEnc)
  (evalDl: ∀ {v}, eDl.intp2 fvRest b c v → v = dl.prefixEncoding n)
  (evalFv: ∀ {v}, eFv.intp2 fvRest b c v → v = Pair.listEncoding fv)
  (evalExpr: ∀ {v}, eExpr.intp2 fvRest b c v → v = exprEnc)
:
  (c consts.uniSetMap).getLane
    lane
    (.pair (uniSetMapIndex dl n fv expr) p)
:=
  match pArg with
  | .null => inPairElimNope inArg
  | .pair _ .null => inPairElimNope (inPairElim inArg).right
  | .pair dlEncAlias (.pair fvAlias exprAlias) =>
    let ⟨insDlAlias, insL⟩ := inPairElim inArg
    let ⟨insFvAlias, insExprAlias⟩ := inPairElim insL
    let eqDlAlias := evalDl insDlAlias
    let eqFvAlias := evalFv insFvAlias
    let eqExprAlias := evalExpr insExprAlias
    by
    unfold uniSetMapIndex
    rw [←eqDlAlias, ←eqFvAlias, exprEncEq, ←eqExprAlias]
    exact inToggle2Elim toggleCount inMap


def isAtConstElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.const x) lane p)
  (getNthSat:
    ∀ {list i valEnc},
      (c consts.getNth).getLane lane (getNthEnc list i valEnc) →
      (uniSetMapDl.wfm consts.getNth).defMem (getNthEnc list i valEnc))
:
  (c consts.uniSetMap).getLane
    lane
    (.pair (uniSetMapIndexDef dl n x) p)
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary insExprGuard
    let ⟨pArg, inMap, inArg⟩ := inCallElim ins
    match pArg with
    | .null => inPairElimNope inArg
    | .pair _ .null => inPairElimNope (inPairElim inArg).right
    | .pair dlEncAlias (.pair fvAlias exprAlias) =>
      let ⟨insDlAlias, ins⟩ := inPairElim inArg
      let ⟨insFvAlias, insDefX⟩ := inPairElim ins
      let eqDlAlias := inVarElim insDlAlias rfl
      let eqFvAlias: fvAlias = Pair.listEncoding [] :=
        inNullElim insFvAlias
      let insDefX := inCallElimSingle insDefX rfl
      let insDefX := inCallElimSingle insDefX rfl
      let insDefX: (getNthConst.toLane lane).intp2 _ _ _ _ :=
        inToggle2Elim 8 (xEncEq ▸ insDefX)
      let insGetDef := getNthSat insDefX
      let exprAliasEq :=
        dl.prefixList_at_eq n x ▸
        getNthElimD (lane := .defLane) insGetDef
      by
      unfold uniSetMapIndexDef uniSetMapIndex
      exact
        exprAliasEq ▸ eqFvAlias ▸ eqDlAlias ▸ inToggle2Elim 4 inMap
  exprEncListElim
    ins
    main
    (isAtVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtPairNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtComplNope · (by decide))
    (isAtArbIrNope · (by decide))

def isAtVarElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.var x) lane p)
  (cinsSat: (∀ {x d}, d ∈ (c x).getLane lane → uniSetMapDl.Ins x d))
:
  (var x).intp2 fv (dl.prefix n).wfm (dl.prefix n).wfm p
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary insExprGuard
    let ins := inCallElimSingle ins rfl
    let ins := inCallElimSingle ins rfl
    let ins := inToggle2Elim 7 ins
    let ins := (cinsSat ins).isSound
    let ins := by rw [← xEncEq] at ins; exact ins
    inVar (getNthElim (lane := .defLane) ins)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    main
    (isAtNullNope · (by decide))
    (isAtPairNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtComplNope · (by decide))
    (isAtArbIrNope · (by decide))

def isAtNullElim {dl n fv b c lane p}
  (ins: InUniSetMapAt dl n fv b c .null lane p)
:
  SingleLaneExpr.null.intp2 fv b c p
:=
  let main ins :=
    let ⟨_insExprGuard, insBody⟩ := inIrElim ins
    let eqP := inNullElim insBody
    eqP ▸ inNull
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtVarNope · (by decide))
    main
    (isAtPairNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtComplNope · (by decide))
    (isAtArbIrNope · (by decide))

def isAtPairElim {dl n fv b c left rite lane p}
  (ins: InUniSetMapAt dl n fv b c (.pair left rite) lane p)
:
  ∃ pL pR,
    p = .pair pL pR ∧
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv left) pL) ∧
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv rite) pR)
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insPair⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary insExprGuard
    let ⟨pL, pR, eqP, insCallLeft, insCallRite⟩ := inPairElimEx insPair
    
    let ⟨pArgLeft, inMapLeft, inArgLeft⟩ := inCallElim insCallLeft
    let insLeftAlias := singleCallElim 8 inMapLeft inArgLeft leftEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    let ⟨pArgRite, inMapRite, inArgRite⟩ := inCallElim insCallRite
    let insRiteAlias := singleCallElim 8 inMapRite inArgRite riteEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    ⟨pL, pR, eqP, insLeftAlias, insRiteAlias⟩
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtNullNope · (by decide))
    main
    (isAtIrNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtComplNope · (by decide))
    (isAtArbIrNope · (by decide))

def isAtIrElim {dl n fv b c left rite lane p}
  (ins: InUniSetMapAt dl n fv b c (.ir left rite) lane p)
:
  (c consts.uniSetMap).getLane lane (.pair (uniSetMapIndex dl n fv left) p) ∧
  (c consts.uniSetMap).getLane lane (.pair (uniSetMapIndex dl n fv rite) p)
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insPair⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary insExprGuard
    
    let ⟨insCallLeft, insCallRite⟩ := inIrElim insPair
    
    let ⟨pArgLeft, inMapLeft, inArgLeft⟩ := inCallElim insCallLeft
    let insLeftAlias := singleCallElim 9 inMapLeft inArgLeft leftEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    let ⟨pArgRite, inMapRite, inArgRite⟩ := inCallElim insCallRite
    let insRiteAlias := singleCallElim 9 inMapRite inArgRite riteEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)

    ⟨insLeftAlias, insRiteAlias⟩
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtPairNope · (by decide))
    main
    (isAtFullNope · (by decide))
    (isAtComplNope · (by decide))
    (isAtArbIrNope · (by decide))
def isAtFullElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.full body) lane p)
:
  ∀ dB,
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv body) dB)
:=
  let main ins dB :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    
    let insArg := ins dB
    let ⟨pArg, inMap, inArg⟩ := inCallElim insArg
    singleCallElim 9 inMap inArg bodyEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtPairNope · (by decide))
    (isAtIrNope · (by decide))
    main
    (isAtComplNope · (by decide))
    (isAtArbIrNope · (by decide))

def isAtComplElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.compl body) lane p)
:
  Not
    ((b consts.uniSetMap).getLane
      lane.toggle
      (.pair (uniSetMapIndex dl n fv body) p))
:=
  let main insCompl insBody :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim insCompl
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    let insArg :=
      inPair (inVar rfl) (inPair (inVar rfl) (bodyEncEq ▸ rfl))
    inComplElim ins (inCall (inToggle2 10 insBody) insArg)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtPairNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtFullNope · (by decide))
    main
    (isAtArbIrNope · (by decide))

def isAtArbIrElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.arbIr body) lane p)
:
  ∀ dX,
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n (dX :: fv) body) p)
:=
  let main ins dX :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    let ⟨pArg, inMap, inArg⟩ := inCallElim (inArbIrElim ins dX)
    singleCallElim 10 inMap inArg bodyEncEq
      (inVarElim · rfl)
      (fun h =>
        let ⟨_vL, _vR, hEq, hL, hR⟩ := inPairElimEx h
        let eqL := inVarElim hL rfl
        let eqR := inVarElim hR rfl
        by rw [hEq, eqL, eqR]; rfl)
      (fun h => inVarElim h rfl)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtPairNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtComplNope · (by decide))
    main


/-
  ## Section: Expression encoding constructors
-/

def isInMap {dl n fv b c expr lane p}
  (isAt: InUniSetMapAt dl n fv b c expr lane p)
:
  intp2
    ((uniSetMapDl.getDef consts.uniSetMap).toLane lane)
    fv
    b
    c
    (.pair (uniSetMapIndex dl n fv expr) p)
:=
  inArbUn
    (dl.prefixEncoding n)
    (inArbUn
      (.listEncoding fv)
      (inArbUn
        expr.encoding
        (inPair
          (inPair rfl (inPair rfl rfl))
          (inToggle2 3 isAt))))

def isAtConst {dl n fv b c x lane p}
  (ins:
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndexDef dl n x) p))
  (insGetNth:
    (c consts.getNth).getLane lane (getDefNthEnc dl n x))
:
  InUniSetMapAt dl n fv b c (.const x) lane p
:=
  inUnL
    (inArbUn
      (.nat x)
      (inIr
        (inSome _ (inIr (inPair (inNat 0) rfl) rfl))
        (inCall
          (inToggle2 4 ins)
          (inPair
            rfl
            (inPair
              inNull
              (inCall
                (inCall
                  (inToggle2 8 insGetNth)
                  rfl)
                rfl))))))

def isAtNull {dl n fv b c lane}:
  InUniSetMapAt dl n fv b c .null lane .null
:=
  inUnR
    (inUnR
      (inUnL
        (inIr
          (inSome _ (inIr (inPair (inNat 2) inNull) rfl))
          inNull)))

def isAtVar {dl n fv b c x lane p}
  (insGetNth:
    (c consts.getNth).getLane lane (getNthEnc fv x p))
:
  InUniSetMapAt dl n fv b c (.var x) lane p
:=
  inUnR
    (inUnL
      (inArbUn
        (.nat x)
        (inIr
          (inSome _ (inIr (inPair (inNat 1) rfl) rfl))
          (inCall
            (inCall
              (inToggle2 7 insGetNth)
              rfl)
            rfl))))

def isAtPair {dl n fv b c left rite lane pL pR}
  (insLeft:
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv left) pL))
  (insRite:
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv rite) pR))
:
  InUniSetMapAt dl n fv b c (.pair left rite) lane (.pair pL pR)
:=
  inUnR
    (inUnR
      (inUnR
        (inUnL
          (inArbUn
            left.encoding
            (inArbUn
              rite.encoding
              (inIr
                (inSome _
                  (inIr
                    (inPair
                      (inNat 3)
                      (inPair (inVar rfl) (inVar rfl)))
                    rfl))
                (inPair
                  (inCall
                    (inToggle2 8 insLeft)
                    (inPair rfl (inPair rfl (inVar rfl))))
                  (inCall
                    (inToggle2 8 insRite)
                    (inPair rfl (inPair rfl (inVar rfl)))))))))))

def isAtIr {dl n fv b c left rite lane p}
  (insLeft:
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv left) p))
  (insRite:
    (c consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndex dl n fv rite) p))
:
  InUniSetMapAt dl n fv b c (.ir left rite) lane p
:=
  inUnR
    (inUnR
      (inUnR
        (inUnR
          (inUnL
            (inArbUn
              left.encoding
              (inArbUn
                rite.encoding
                (inIr
                  (inSome _
                    (inIr
                      (inPair
                        (inNat 4)
                        (inPair (inVar rfl) (inVar rfl))) rfl))
                  (inIr
                    (inCall
                      (inToggle2 9 insLeft)
                      (inPair rfl (inPair rfl (inVar rfl))))
                    (inCall
                      (inToggle2 9 insRite)
                      (inPair rfl (inPair rfl (inVar rfl))))))))))))

def isAtFull {dl n fv b c body lane p}
  (insBody:
    ∀ dB,
      (c consts.uniSetMap).getLane
        lane
        (.pair (uniSetMapIndex dl n fv body) dB))
:
  InUniSetMapAt dl n fv b c (.full body) lane p
:=
  inUnR
    (inUnR
      (inUnR
        (inUnR
          (inUnR
            (inUnL
              (inArbUn
                body.encoding
                (inIr
                  (inSome _ (inIr (inPair (inNat 5) rfl) rfl))
                  (inFull p fun dB =>
                    inCall
                      (inToggle2 9 (insBody dB))
                      (inPair rfl (inPair rfl (inVar rfl)))))))))))

def isAtCompl {dl n fv b c body lane p}
  (out:
    Not
      ((b consts.uniSetMap).getLane
        lane.toggle
        (.pair (uniSetMapIndex dl n fv body) p)))
:
  InUniSetMapAt dl n fv b c (.compl body) lane p
:=
  let ninsCall insCall :=
    let ⟨arg, inMap, inArg⟩ := inCallElim insCall
    match arg with
    | .null => inPairElimNope inArg
    | .pair _ .null =>
      inPairElimNope (inPairElim inArg).right
    | .pair dlAlias (.pair fvAlias bodyAlias) =>
      let ⟨insDlAlias, ins⟩ := inPairElim inArg
      let ⟨insFvAlias, insBodyAlias⟩ := inPairElim ins
      let eqDlAlias := inVarElim insDlAlias rfl
      let eqFvAlias := inVarElim insFvAlias rfl
      let eqBodyAlias := inVarElim insBodyAlias rfl
      out (by
        unfold uniSetMapIndex
        rw [←eqBodyAlias, ←eqFvAlias, ←eqDlAlias]
        exact inToggle2Elim 10 inMap)
  inUnR
    (inUnR
      (inUnR
        (inUnR
          (inUnR
            (inUnR
              (inUnL
                (inArbUn
                  body.encoding
                  (inIr
                    (inSome _ (inIr (inPair (inNat 6) rfl) rfl))
                    (inCompl ninsCall)))))))))

  def isAtArbIr {dl n fv b c body lane p}
    (insBody:
      ∀ dX,
        (c consts.uniSetMap).getLane
          lane
          (.pair (uniSetMapIndex dl n (dX :: fv) body) p))
  :
    InUniSetMapAt dl n fv b c (.arbIr body) lane p
  :=
    inUnR
      (inUnR
        (inUnR
          (inUnR
            (inUnR
              (inUnR
                (inUnR
                  (inArbUn
                    body.encoding
                    (inIr
                      (inSome _ (inIr (inPair (inNat 7) rfl) rfl))
                      (inArbIr fun dX =>
                        inCall
                          (inToggle2 10 (insBody dX))
                          (inPair
                            rfl
                            (inPair
                              (inPair (inVar rfl) rfl)
                              (inVar rfl))))))))))))


/-
  ## Section: Cause building
-/

def causeConst
  (dl: DefList)
  (n: Nat)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:= {
  cins xExt dExt :=
    let expr := (dl.prefix n).getDef xInt
    Or
      (And
        (xExt = consts.getNth)
        (dExt = getDefNthEnc dl n xInt))
      (And
        (xExt = consts.uniSetMap)
        (dExt = .pair (uniSetMapIndex dl n [] expr) dInt))
  bout _ := {}
}

def causeVar
  (fv: List Pair)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:= {
  cins xExt dExt :=
    xExt = consts.getNth ∧
    dExt = getNthEnc fv xInt dInt
  bout _ := {}
}

abbrev causeNull: Cause Pair := Cause.empty

def causePair
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (left rite: BasicExpr)
  (pL pR: Pair)
:
  Cause Pair
:= {
  cins xExt dExt :=
    Or
      (And
        (xExt = consts.uniSetMap)
        (dExt = .pair (uniSetMapIndex dl n fv left) pL))
      (And
        (xExt = consts.uniSetMap)
        (dExt = .pair (uniSetMapIndex dl n fv rite) pR))
  bout _ := {}
}

def causeIr
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (left rite: BasicExpr)
  (p: Pair)
:
  Cause Pair
:= {
  cins xExt dExt :=
    Or
      (And
        (xExt = consts.uniSetMap)
        (dExt = .pair (uniSetMapIndex dl n fv left) p))
      (And
        (xExt = consts.uniSetMap)
        (dExt = .pair (uniSetMapIndex dl n fv rite) p))
  bout _ := {}
}

def causeFull
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: BasicExpr)
:
  Cause Pair
:= {
  cins xExt dExt :=
    ∃ dB,
      xExt = consts.uniSetMap ∧
      dExt = .pair (uniSetMapIndex dl n fv body) dB
  bout _ := {}
}

def causeCompl
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: BasicExpr)
  (dInt: Pair)
:
  Cause Pair
:= {
  cins _ := {}
  bout xExt dExt:=
    And
      (xExt = consts.uniSetMap)
      (dExt = .pair (uniSetMapIndex dl n fv body) dInt)
}

def causeArbIr
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: BasicExpr)
  (dInt: Pair)
:
  Cause Pair
:= {
  cins xExt dExt :=
    ∃ dX,
      xExt = consts.uniSetMap ∧
      dExt = .pair (uniSetMapIndex dl n (dX :: fv) body) dInt
  bout _ := {}
}


def isWeakCauseConst {dl n fv x d}:
  (causeConst dl n x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.const x)) d)
:=
  fun _ _ isSat =>
    let insGetNth := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)

def isWeakCauseVar {dl n fv x d}:
  (causeVar fv x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.var x)) d)
:=
  fun _ _ isSat =>
    let inGetNth := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtVar inGetNth)

def isWeakCauseNull {dl n fv}:
  causeNull.IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv .null) .null)
:=
  fun _ _ _ => isInMap isAtNull

def isWeakCausePair {dl n fv left rite pL pR}:
  (causePair dl n fv left rite pL pR).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.pair left rite)) (.pair pL pR))
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let inRite := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtPair inLeft inRite)

def isWeakCauseIr {dl n fv left rite p}:
  (causeIr dl n fv left rite p).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.ir left rite)) p)
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let inRite := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtIr inLeft inRite)

def isWeakCauseFull {dl n fv body p}:
  (causeFull dl n fv body).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.full body)) p)
:=
  fun _ _ isSat =>
    isInMap (isAtFull fun dB => isSat.cinsSat ⟨dB, rfl, rfl⟩)

def isWeakCauseCompl {dl n fv body d}:
  (causeCompl dl n fv body d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.compl body)) d)
:=
  fun _ _ isSat =>
    let out := isSat.boutSat (And.intro rfl rfl)
    isInMap (isAtCompl out)

def isWeakCauseArbIr {dl n fv body d}:
  (causeArbIr dl n fv body d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.arbIr body)) d)
:=
  fun _ _ isSat =>
    isInMap (isAtArbIr fun dX => isSat.cinsSat ⟨dX, rfl, rfl⟩)

/-
  ## Section: Not beyond prefix
  
  TODO:
  - this section
  - replace un elim towers
  - single helper for non-matching eliminators
-/
