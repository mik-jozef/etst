module
public import Etst.WFC.Utils.SelfDefinability.UniSetMapDl
public import Etst.WFC.Utils.Cause
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst.uniSetMapDl
open SingleLaneExpr


exposed def InUniSetMapAt (dl n fv b c expr lane p) :=
  let vars := [
    BasicExpr.encoding expr,
    Pair.listEncoding fv,
    DefList.prefixEncoding dl n,
  ]
  p ∈ (exprEncList.toLane lane).intp2 vars b c

theorem isAtOfInsDef {dl n fv b c lane expr p}
  (ins:
    Set.Mem
      (((uniSetMapDl.getDef consts.uniSetMap).toLane lane).intp2
        []
        b
        c)
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  InUniSetMapAt dl n fv b c expr lane p
:=
  let ⟨dlEnc, ins⟩ := inArbUnElim ins
  let ⟨fvEnc, ins⟩ := inArbUnElim ins
  let ⟨exprEnc, ins⟩ := inArbUnElim ins
  let ⟨insEnc, insAt⟩ := inProdElim ins
  let ⟨dlEncEq, fvEncEq, exprEncEq⟩ :=
    let ⟨insDl, ins⟩ := inProdElim insEnc
    let ⟨insFv, insExpr⟩ := inProdElim ins
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

theorem isAtIndexNope
  {actual expected enc fv b c p indexExpr restExpr aliasVar}
  (insExprGuard:
    let expr := .some (ir (prod indexExpr restExpr) (var aliasVar))
    p ∈ intp2 expr fv b c)
  (evalActual: fv[aliasVar]? = .some (.pair (.nat actual) enc))
  (evalIndex:
    ∀ {pIndex},
      pIndex ∈ indexExpr.intp2 fv b c →
      pIndex = Pair.nat expected)
  (indexNeq: actual ≠ expected)
  {P: Prop}
:
  P
:=
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inProdElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inProdElim insGuardL
    let eqActual: _ = Pair.nat actual :=
      Pair.noConfusion (inVarElim insGuardR evalActual) fun eq _ => eq
    let eqExpected := evalIndex insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqActual.symm.trans eqExpected)))

theorem isAtConstNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncConst.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 0)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 0)) indexNeq

theorem isAtComplConstNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncComplConst.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 1)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 1)) indexNeq

theorem isAtVarNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncVar.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 2)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 2)) indexNeq

theorem isAtComplVarNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncComplVar.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 3)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 3)) indexNeq

theorem isAtNullNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncNull.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 4)
  {P: Prop}
:
  P
:=
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 4)) indexNeq

theorem isAtProdNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncProd.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 5)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 5)) indexNeq

theorem isAtIrNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncIr.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 6)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 6)) indexNeq

theorem isAtUnNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncUn.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 7)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 7)) indexNeq

theorem isAtFullNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncFull.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 8)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 8)) indexNeq

theorem isAtSomeNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncSome.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 9)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 9)) indexNeq

theorem isAtArbIrNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncArbIr.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 10)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 10)) indexNeq

theorem isAtArbUnNope {fv b c lane i enc p}
  (ins:
    Set.Mem
      ((exprEncArbUn.toLane lane).intp2
        (.pair (.nat i) enc :: fv)
        b
        c)
      p)
  (indexNeq: i ≠ 11)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 11)) indexNeq

private theorem exprEncListElim {fv b c lane p}
  {P: Prop}
  (ins: p ∈ (exprEncList.toLane lane).intp2 fv b c)
  (onConst: p ∈ (exprEncConst.toLane (toggle2N lane 1)).intp2 fv b c → P)
  (onComplConst: p ∈ (exprEncComplConst.toLane (toggle2N lane 2)).intp2 fv b c → P)
  (onVar: p ∈ (exprEncVar.toLane (toggle2N lane 3)).intp2 fv b c → P)
  (onComplVar: p ∈ (exprEncComplVar.toLane (toggle2N lane 4)).intp2 fv b c → P)
  (onNull: p ∈ (exprEncNull.toLane (toggle2N lane 5)).intp2 fv b c → P)
  (onProd: p ∈ (exprEncProd.toLane (toggle2N lane 6)).intp2 fv b c → P)
  (onIr: p ∈ (exprEncIr.toLane (toggle2N lane 7)).intp2 fv b c → P)
  (onUn: p ∈ (exprEncUn.toLane (toggle2N lane 8)).intp2 fv b c → P)
  (onFull: p ∈ (exprEncFull.toLane (toggle2N lane 9)).intp2 fv b c → P)
  (onSome: p ∈ (exprEncSome.toLane (toggle2N lane 10)).intp2 fv b c → P)
  (onArbIr: p ∈ (exprEncArbIr.toLane (toggle2N lane 11)).intp2 fv b c → P)
  (onArbUn: p ∈ (exprEncArbUn.toLane (toggle2N lane 11)).intp2 fv b c → P)
:
  P
:=
  match inUnElim ins with
  | Or.inl ins => onConst ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onComplConst ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onVar ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onComplVar ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onNull ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onProd ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onIr ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onUn ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onFull ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onSome ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onArbIr ins
  | Or.inr ins => onArbUn ins


/-
  ## Section: Matching expression encoding eliminators
-/

theorem exprGuardElimUnary {i iEnc encRest fv0 fvRest b c p}
  (ins:
    Set.Mem
      (intp2
        (some (ir (prod i (var 0)) (var 1)))
        (fv0 :: .pair iEnc encRest :: fvRest)
        b
        c)
      p)
:
  encRest = fv0
:=
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim ins
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inProdElimNope insGuardL
  | .pair _ _ =>
    let ⟨_, insVar⟩ := inProdElim insGuardL
    let eqRest :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun _ => id
    eqRest.symm.trans (inVarElim insVar rfl)

theorem exprGuardElimBinary {i iEnc encL encR fvRite fvLeft fvRest b c p}
  (ins:
    Set.Mem
      (intp2
        (some (ir (prod i (prod (var 1) (var 0))) (var 2)))
        (fvRite :: fvLeft :: .pair iEnc (.pair encL encR) :: fvRest)
        b
        c)
      p)
:
  encL = fvLeft ∧ encR = fvRite
:=
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim ins
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inProdElimNope insGuardL
  | .pair _ exprGuardTuple =>
    let ⟨_, insTuple⟩ := inProdElim insGuardL
    match exprGuardTuple with
    | .null => inProdElimNope insTuple
    | .pair _ _ =>
      let ⟨insLeft, insRite⟩ := inProdElim insTuple
      let eqRest :=
        Pair.noConfusion (inVarElim insGuardR rfl) fun _ eq => eq
      let eqL := Pair.noConfusion eqRest fun l _ => l
      let eqR := Pair.noConfusion eqRest fun _ r => r
      And.intro
        (eqL.symm.trans (inVarElim insLeft rfl))
        (eqR.symm.trans (inVarElim insRite rfl))

private theorem inMapCallElim
  {dl n fv b c expr lane p fvMeta eDl eFv eExpr exprEnc}
  (toggleCount: Nat)
  (inCall:
    Set.Mem
      (intp2
        (.call
          (uniSetMapConst.toLane (toggle2N lane toggleCount))
          (.prod eDl (.prod eFv eExpr)))
        fvMeta
        b
        c)
      p)
  (exprEncEq: expr.encoding = exprEnc)
  (evalDl: ∀ {v fvH}, v ∈ intp2 eDl (fvH::fvMeta) b c → v = dl.prefixEncoding n)
  (evalFv: ∀ {v fvH}, v ∈ intp2 eFv (fvH::fvMeta) b c → v = Pair.listEncoding fv)
  (evalExpr: ∀ {v fvH}, v ∈ intp2 eExpr (fvH::fvMeta) b c → v = exprEnc)
:
  ((c consts.uniSetMap).getLane lane).Mem
    (.pair (uniSetMapIndex dl n fv expr) p)
:=
  let ⟨pArg, inMap, inArg⟩ := inCallElim inCall
  match pArg with
  | .null => inProdElimNope inArg
  | .pair _ .null => inProdElimNope (inProdElim inArg).right
  | .pair dlEncAlias (.pair fvAlias exprAlias) =>
    let ⟨insDlAlias, insL⟩ := inProdElim inArg
    let ⟨insFvAlias, insExprAlias⟩ := inProdElim insL
    let eqDlAlias := evalDl insDlAlias
    let eqFvAlias := evalFv insFvAlias
    let eqExprAlias := evalExpr insExprAlias
    by
    unfold uniSetMapIndex
    rw [←eqDlAlias, ←eqFvAlias, exprEncEq, ←eqExprAlias]
    exact inToggle2Elim toggleCount inMap


theorem isAtConstElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.const x) lane p)
  (getNthSat:
    ∀ {list i valEnc},
      getNthEnc list i valEnc ∈ (c consts.getNth).getLane lane →
      getNthEnc list i valEnc ∈ vals.getNth.defMem)
:
  ((c consts.uniSetMap).getLane lane).Mem
    (.pair (uniSetMapIndexDef dl n x) p)
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary (i:=.nat 0) insExprGuard
    let ⟨pArg, inMap, inArg⟩ := inCallElim ins
    match pArg with
    | .null => inProdElimNope inArg
    | .pair _ .null => inProdElimNope (inProdElim inArg).right
    | .pair dlEncAlias (.pair fvAlias exprAlias) =>
      let ⟨insDlAlias, ins⟩ := inProdElim inArg
      let ⟨insFvAlias, insDefX⟩ := inProdElim ins
      let eqDlAlias := inVarElim insDlAlias rfl
      let eqFvAlias: fvAlias = Pair.listEncoding [] :=
        inNullElim insFvAlias
      let insDefX := inCallElimSingle insDefX rfl
      let insDefX := inCallElimSingle insDefX rfl
      let insDefX: _ ∈ (getNthConst.toLane lane).intp2 _ _ _ :=
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
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtComplConstElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.compl (.const x)) lane p)
:
  Or
    (Not
      (Set.Mem
        ((b consts.getNth).getLane lane.toggle)
        ((getDefNthEnc dl n x))))
    (Not
      (Set.Mem
        ((b consts.uniSetMap).getLane lane.toggle)
        (.pair (uniSetMapIndexDef dl n x) p)))
:=
  let main insCompl :=
    not_and_or.mp fun insBoth =>
    let ⟨insGetNth, insBody⟩ := insBoth
    let ⟨xEnc, ins⟩ := inArbUnElim insCompl
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary (i := .nat 1) insExprGuard
    let insArg :=
      inProd
        (inVar rfl)
        (inProd
          inNull
          (inCall
            (inCall
              (inToggle2 9 (xEncEq ▸ insGetNth))
              (inVar rfl))
            (inVar rfl)))
    inComplElim ins (inCall (inToggle2 5 insBody) insArg)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    main
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtVarElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.var x) lane p)
:
  getNthEnc fv x p ∈ (c consts.getNth).getLane lane
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary insExprGuard
    let ins := inCallElimSingle ins rfl
    let ins := inCallElimSingle ins rfl
    let ins := inToggle2Elim 8 ins
    by unfold getNthEnc; exact xEncEq ▸ ins
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    main
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtComplVarElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.compl (.var x)) lane p)
:
  ¬ getNthEnc fv x p ∈ (b consts.getNth).getLane lane.toggle
:=
  let main insCompl insGetNth :=
    let ⟨xEnc, ins⟩ := inArbUnElim insCompl
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary (i := .nat 3) insExprGuard
    inComplElim
      ins
      (inCall
        (inCall
          (inToggle2 9 (xEncEq ▸ insGetNth))
          rfl)
        rfl)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    main
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtNullElim {dl n fv b c lane p}
  (ins: InUniSetMapAt dl n fv b c .null lane p)
:
  p ∈ SingleLaneExpr.null.intp2 fv b c
:=
  let main ins :=
    let ⟨_insExprGuard, insBody⟩ := inIrElim ins
    let eqP := inNullElim insBody
    eqP ▸ inNull
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    main
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtProdElim {dl n fv b c left rite lane p}
  (ins: InUniSetMapAt dl n fv b c (.prod left rite) lane p)
:
  ∃ pL pR,
    p = .pair pL pR ∧
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) pL) ∧
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) pR)
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insPair⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary insExprGuard
    let ⟨pL, pR, eqP, insCallLeft, insCallRite⟩ := inProdElimEx insPair
    
    let insLeftAlias := inMapCallElim 10 insCallLeft leftEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    let insRiteAlias := inMapCallElim 10 insCallRite riteEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    ⟨pL, pR, eqP, insLeftAlias, insRiteAlias⟩
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    main
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtIrElim {dl n fv b c left rite lane p}
  (ins: InUniSetMapAt dl n fv b c (.ir left rite) lane p)
:
  And
    (((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) p))
    (((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) p))
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insPair⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary insExprGuard
    
    let ⟨insCallLeft, insCallRite⟩ := inIrElim insPair
    
    let insLeftAlias := inMapCallElim 11 insCallLeft leftEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    let insRiteAlias := inMapCallElim 11 insCallRite riteEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)

    ⟨insLeftAlias, insRiteAlias⟩
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    main
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtComplIrElim {dl n fv b c left rite lane p}
  (ins:
    let expr := .compl (.ir left rite)
    InUniSetMapAt dl n fv b c expr lane p)
:
  Or
    (((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left.compl) p))
    (((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite.compl) p))
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insUnCall⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary (i := .nat 7) insExprGuard
    match inUnElim insUnCall with
    | .inl insCallLeft =>
      let ⟨_pArgLeft, inMapLeft, inArgLeft⟩ := inCallElim insCallLeft
      .inl
        (inMapCallElim 13 insCallLeft leftEncEq
          (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl))
    | .inr insCallRite =>
      let ⟨_pArgRite, inMapRite, inArgRite⟩ := inCallElim insCallRite
      .inr
        (inMapCallElim 13 insCallRite riteEncEq
          (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl))
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    main
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtFullElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.full body) lane p)
:
  ∀ pB,
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv body) pB)
:=
  let main ins pB :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    inMapCallElim 12 (ins pB) bodyEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    main
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtComplFullElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.compl (.full body)) lane p)
:
  ∃ pB,
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv (.compl body)) pB)
:=
  let main ins :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary (i := .nat 9) insExprGuard
    let ⟨pB, insArg⟩ := inSomeElim ins
    let ⟨_pArg, inMap, inArg⟩ := inCallElim insArg
    ⟨pB,
      inMapCallElim 14 insArg bodyEncEq
        (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)⟩
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    main
    (isAtArbIrNope · (by decide))
    (isAtArbUnNope · (by decide))

theorem isAtArbIrElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.arbIr body) lane p)
:
  ∀ pX,
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n (pX :: fv) body) p)
:=
  let main ins pX :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    inMapCallElim 14 (ins pX) bodyEncEq
      (inVarElim · rfl)
      (fun h =>
        let ⟨_vL, _vR, hEq, hL, hR⟩ := inProdElimEx h
        let eqL := inVarElim hL rfl
        let eqR := inVarElim hR rfl
        by rw [hEq, eqL, eqR]; rfl)
      (inVarElim · rfl)
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    main
    (isAtArbUnNope · (by decide))

theorem isAtComplArbIrElim {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.compl (.arbIr body)) lane p)
:
  ∃ pX,
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n (pX :: fv) (.compl body)) p)
:=
  let main ins :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary (i := .nat 11) insExprGuard
    let ⟨pX, insArg⟩ := inArbUnElim ins
    ⟨pX,
      inMapCallElim 15 insArg bodyEncEq
        (inVarElim · rfl)
        (fun h =>
          let ⟨_vL, _vR, hEq, hL, hR⟩ := inProdElimEx h
          let eqL := inVarElim hL rfl
          let eqR := inVarElim hR rfl
          by rw [hEq, eqL, eqR]; rfl)
        (inVarElim · rfl)⟩
  exprEncListElim
    ins
    (isAtConstNope · (by decide))
    (isAtComplConstNope · (by decide))
    (isAtVarNope · (by decide))
    (isAtComplVarNope · (by decide))
    (isAtNullNope · (by decide))
    (isAtProdNope · (by decide))
    (isAtIrNope · (by decide))
    (isAtUnNope · (by decide))
    (isAtFullNope · (by decide))
    (isAtSomeNope · (by decide))
    (isAtArbIrNope · (by decide))
    main


/-
  ## Section: Expression encoding constructors
-/


theorem isInMap {dl n fv b c expr lane p}
  (isAt: InUniSetMapAt dl n fv b c expr lane p)
:
  Set.Mem
    (intp2
      ((uniSetMapDl.getDef consts.uniSetMap).toLane lane)
      fv
      b
      c)
    (.pair (uniSetMapIndex dl n fv expr) p)
:=
  inArbUn
    (dl.prefixEncoding n)
    (inArbUn
      (.listEncoding fv)
      (inArbUn
        expr.encoding
        (inProd
          (inProd rfl (inProd rfl rfl))
          (inToggle2 3 isAt))))

theorem isAtConst {dl n fv b c x lane p}
  (ins:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndexDef dl n x) p))
  (insGetNth:
    ((c consts.getNth).getLane lane).Mem (getDefNthEnc dl n x))
:
  InUniSetMapAt dl n fv b c (.const x) lane p
:=
  inUnL
    (inArbUn
      (.nat x)
      (inIr
        (inSome _ (inIr (inProd (inNat 0) rfl) rfl))
        (inCall
          (inToggle2 4 ins)
          (inProd
            rfl
            (inProd
              inNull
              (inCall
                (inCall
                  (inToggle2 8 insGetNth)
                  rfl)
                rfl))))))

theorem isAtComplConst {dl n fv b c x lane p}
  (ninGetNth:
    (∀ {exprEnc: Pair},
      exprEnc ≠ ((dl.prefix n).getDef x).encoding →
      Not
        (((b consts.getNth).getLane lane.toggle).Mem
          (getNthEnc (dl.prefixList 0 n) x exprEnc))))
  (ninMap:
    Not
      (((b consts.uniSetMap).getLane lane.toggle).Mem
        (.pair (uniSetMapIndexDef dl n x) p)))
:
  InUniSetMapAt dl n fv b c (.compl (.const x)) lane p
:=
  inUnR
    (inUnL
      (inArbUn
        (.nat x)
        (inIr
          (inSome _ (inIr (inProd (inNat 1) rfl) rfl))
          (inCompl fun insBody =>
            let inMap := inMapCallElim 5 insBody rfl
              (inVarElim · rfl)
              (fv:=[])
              inNullElim
              (expr := (dl.prefix n).getDef x)
              (fun inGetNthCall =>
                let ⟨pArgX, inMid, inArgX⟩ := inCallElim inGetNthCall
                let ⟨pArgDl, inFn, inArgDl⟩ := inCallElim inMid
                let eqX := inVarElim inArgX rfl
                let eqDl := inVarElim inArgDl rfl
                let inFn := by
                  rw [eqX, eqDl] at inFn;
                  exact inToggle2Elim 9 inFn
                byContradiction (ninGetNth · inFn))
            ninMap inMap))))

theorem isAtVar {dl n fv b c x lane p}
  (insGetNth:
    ((c consts.getNth).getLane lane).Mem (getNthEnc fv x p))
:
  InUniSetMapAt dl n fv b c (.var x) lane p
:=
  inUnR
  (inUnR
  (inUnL
  (inArbUn
    (.nat x)
    (inIr
      (inSome _ (inIr (inProd (inNat 2) rfl) rfl))
      (inCall
        (inCall
          (inToggle2 8 insGetNth)
          rfl)
        rfl)))))

theorem isAtComplVar {dl n fv b c x lane p}
  (ninGetNth:
    Not
      (((b consts.getNth).getLane lane.toggle).Mem
        (getNthEnc fv x p)))
:
  InUniSetMapAt dl n fv b c (.compl (.var x)) lane p
:=
  inUnR
  (inUnR
  (inUnR
  (inUnL
    (inArbUn
      (.nat x)
      (inIr
        (inSome _ (inIr (inProd (inNat 3) rfl) rfl))
        (inCompl fun insGetNthCall =>
          let insGetNth := inCallElimSingle insGetNthCall rfl
          let insGetNth := inCallElimSingle insGetNth rfl
          let insGetNth := inToggle2Elim 9 insGetNth
          ninGetNth insGetNth))))))

theorem isAtNull {dl n fv b c lane}:
  InUniSetMapAt dl n fv b c .null lane .null
:=
  inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnL
  (inIr
    (inSome _ (inIr (inProd (inNat 4) inNull) rfl))
    inNull)))))

theorem isAtProd {dl n fv b c left rite lane pL pR}
  (insLeft:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) pL))
  (insRite:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) pR))
:
  InUniSetMapAt dl n fv b c (.prod left rite) lane (.pair pL pR)
:=
  inUnR
  (inUnR
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
            (inProd
              (inNat 5)
              (inProd (inVar rfl) (inVar rfl)))
            rfl))
        (inProd
          (inCall
            (inToggle2 10 insLeft)
            (inProd rfl (inProd rfl (inVar rfl))))
          (inCall
            (inToggle2 10 insRite)
            (inProd rfl (inProd rfl (inVar rfl)))))))))))))

theorem isAtIr {dl n fv b c left rite lane p}
  (insLeft:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) p))
  (insRite:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) p))
:
  InUniSetMapAt dl n fv b c (.ir left rite) lane p
:=
  inUnR
  (inUnR
  (inUnR
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
            (inProd
              (inNat 6)
              (inProd (inVar rfl) (inVar rfl)))
            rfl))
        (inIr
          (inCall
            (inToggle2 11 insLeft)
            (inProd rfl (inProd rfl (inVar rfl))))
          (inCall
            (inToggle2 11 insRite)
            (inProd rfl (inProd rfl (inVar rfl))))))))))))))

theorem isAtUn {dl n fv b c left rite lane p}
  (ins:
    Or
      (((c consts.uniSetMap).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv left.compl) p))
      (((c consts.uniSetMap).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv rite.compl) p)))
:
  InUniSetMapAt dl n fv b c (.compl (.ir left rite)) lane p
:=
  let ins :=
    match ins with
    | .inl insLeft =>
      inUnL
        (inCall
          (inToggle2 13 insLeft)
          (inProd rfl (inProd rfl (inVar rfl))))
    | .inr insRite =>
      inUnR
        (inCall
          (inToggle2 13 insRite)
          (inProd rfl (inProd rfl (inVar rfl))))
  inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnL
  (inArbUn
    left.compl.encoding
    (inArbUn
      rite.compl.encoding
      (inIr
        (inSome _
          (inIr
            (inProd
              (inNat 7)
              (inProd (inVar rfl) (inVar rfl)))
            rfl))
        ins))))))))))

theorem isAtFull {dl n fv b c body lane p}
  (insBody:
    ∀ dB,
      ((c consts.uniSetMap).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv body) dB))
:
  InUniSetMapAt dl n fv b c (.full body) lane p
:=
  inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnL
  (inArbUn
    body.encoding
    (inIr
      (inSome _ (inIr (inProd (inNat 8) rfl) rfl))
      (inFull p fun dB =>
        inCall
          (inToggle2 12 (insBody dB))
          (inProd rfl (inProd rfl (inVar rfl))))))))))))))

theorem isAtSome {dl n fv b c body lane p}
  (dB: Pair)
  (insBody:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv body.compl) dB))
:
  InUniSetMapAt dl n fv b c (.compl (.full body)) lane p
:=
  inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnL
  (inArbUn
    body.compl.encoding
    (inIr
      (inSome _ (inIr (inProd (inNat 9) rfl) rfl))
      (inSome dB
        (inCall
          (inToggle2 14 insBody)
          (inProd rfl (inProd rfl (inVar rfl))))))))))))))))

theorem isAtArbIr {dl n fv b c body lane p}
  (insBody:
    ∀ dX,
      ((c consts.uniSetMap).getLane lane).Mem
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
  (inUnR
  (inUnR
  (inUnR
  (inUnL
  (inArbUn
    body.encoding
    (inIr
      (inSome _ (inIr (inProd (inNat 10) rfl) rfl))
      (inArbIr fun dX =>
        inCall
          (inToggle2 14 (insBody dX))
          (inProd
            rfl
            (inProd
              (inProd rfl rfl)
              rfl)))))))))))))))

theorem isAtArbUn {dl n fv b c body lane p}
  (dX: Pair)
  (insBody:
    ((c consts.uniSetMap).getLane lane).Mem
      (.pair (uniSetMapIndex dl n (dX :: fv) body.compl) p))
:
  InUniSetMapAt dl n fv b c (.compl (.arbIr body)) lane p
:=
  inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnR
  (inArbUn
    body.compl.encoding
    (inIr
      (inSome _ (inIr (inProd (inNat 11) rfl) rfl))
      (inArbUn
        dX
        (inCall
          (inToggle2 15 insBody)
          (inProd
            rfl
            (inProd
              (inProd rfl rfl)
              rfl))))))))))))))))


/-
  ## Section: Cause building
-/

exposed def causeExpr
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
  (p: Pair)
:
  Cause Pair
:=
  Cause.cinsJust
    consts.uniSetMap
    (.pair (uniSetMapIndex dl n fv expr) p)

exposed def causeTwoExprs
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (left rite: BasicExpr)
  (pL pR: Pair)
:
  Cause Pair
:=
  Cause.union (causeExpr dl n fv left pL) (causeExpr dl n fv rite pR)

exposed def causeConst
  (dl: DefList)
  (n: Nat)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.union
    (Cause.cinsJust
      consts.getNth
      (getDefNthEnc dl n xInt))
    (Cause.cinsJust
      consts.uniSetMap
      (.pair (uniSetMapIndexDef dl n xInt) dInt))

exposed def causeComplConst
  (dl: DefList)
  (n: Nat)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:= {
  cins _ _ := False
  bout xExt dExt :=
    Or
      (∃ exprEnc,
        exprEnc ≠ ((dl.prefix n).getDef xInt).encoding ∧
        xExt = consts.getNth ∧
        dExt = getNthEnc (dl.prefixList 0 n) xInt exprEnc)
      (xExt = consts.uniSetMap ∧
        dExt = .pair (uniSetMapIndexDef dl n xInt) dInt)
}

exposed def causeVar
  (fv: List Pair)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.cinsJust consts.getNth (getNthEnc fv xInt dInt)

exposed def causeComplVar
  (fv: List Pair)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.boutJust consts.getNth (getNthEnc fv xInt dInt)

exposed def causeFull
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
  bout _ _ := False
}

exposed def causeSome
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: BasicExpr)
  (dBody: Pair)
:
  Cause Pair
:=
  Cause.cinsJust
    consts.uniSetMap
    (.pair (uniSetMapIndex dl n fv body) dBody)

exposed def causeArbIr
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
  bout _ _ := False
}

exposed def causeArbUn
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: BasicExpr)
  (dX: Pair)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.cinsJust
    consts.uniSetMap
    (.pair (uniSetMapIndex dl n (dX :: fv) body) dInt)


theorem isWeakCauseConst {dl n fv x d}:
  (causeConst dl n x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.const x)) d)
:=
  fun _ _ isSat =>
    let insGetNth := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)

theorem isWeakCauseComplConst {dl n fv x d}:
  (causeComplConst dl n x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.compl (.const x))) d)
:=
  fun _ _ isSat =>
    let ninGetNth :=
      fun {exprEnc} exprEncNe inGetNth =>
        isSat.boutSat
          (Or.inl ⟨exprEnc, exprEncNe, rfl, rfl⟩)
          inGetNth
    let ninMap :=
      fun inMap =>
        isSat.boutSat
          (Or.inr ⟨rfl, rfl⟩)
          inMap
    isInMap (isAtComplConst ninGetNth ninMap)

theorem isWeakCauseVar {dl n fv x d}:
  (causeVar fv x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.var x)) d)
:=
  fun _ _ isSat =>
    let inGetNth := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtVar inGetNth)

theorem isWeakCauseComplVar {dl n fv x d}:
  (causeComplVar fv x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.compl (.var x))) d)
:=
  fun _ _ isSat =>
    let ninGetNth :=
      fun inGetNth =>
        isSat.boutSat ⟨rfl, rfl⟩ inGetNth
    isInMap (isAtComplVar ninGetNth)

theorem isWeakCauseNull {dl n fv}:
  Cause.empty.IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv .null) .null)
:=
  fun _ _ _ => isInMap isAtNull

theorem isWeakCauseProd {dl n fv left rite pL pR}:
  (causeTwoExprs dl n fv left rite pL pR).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.prod left rite)) (.pair pL pR))
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let inRite := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtProd inLeft inRite)

theorem isWeakCauseIr {dl n fv left rite p}:
  (causeTwoExprs dl n fv left rite p p).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.ir left rite)) p)
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let inRite := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtIr inLeft inRite)

theorem isWeakCauseUnL {dl n fv p}
  (left rite: BasicExpr)
:
  (causeExpr dl n fv left p).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.un left rite)) p)
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtUn (Or.inl inLeft))

theorem isWeakCauseUnR {dl n fv p}
  (left rite: BasicExpr)
:
  (causeExpr dl n fv rite p).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.un left rite)) p)
:=
  fun _ _ isSat =>
    let inRite := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtUn (Or.inr inRite))

theorem isWeakCauseFull {dl n fv body p}:
  (causeFull dl n fv body).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.full body)) p)
:=
  fun _ _ isSat =>
    isInMap (isAtFull fun dB => isSat.cinsSat ⟨dB, rfl, rfl⟩)

theorem isWeakCauseSome {dl n fv p}
  (body: BasicExpr)
  (dBody: Pair)
:
  (causeSome dl n fv body dBody).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.some body)) p)
:=
  fun _ _ isSat =>
    let inBody := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtSome dBody inBody)

theorem isWeakCauseArbIr {dl n fv body d}:
  (causeArbIr dl n fv body d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.arbIr body)) d)
:=
  fun _ _ isSat =>
    isInMap (isAtArbIr fun dX => isSat.cinsSat ⟨dX, rfl, rfl⟩)

theorem isWeakCauseArbUn {dl n fv body dX d}:
  (causeArbUn dl n fv body dX d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.arbUn body)) d)
:=
  fun _ _ isSat =>
    let inBody := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtArbUn dX inBody)

/-
  ## Section: Some extra randos
-/

exposed noncomputable def usmWfm := uniSetMapDl.wfm

theorem isAtAny {dl n fv p lane}:
  InUniSetMapAt dl n fv usmWfm usmWfm .any lane p
:=
  isAtArbUn
    p
    (DefList.InWfm.of_in_def_no_fv
      (isInMap
        (isAtVar
          (uniSetMapDl.getNth
            (Nat.succ_pos fv.length)))))

theorem notAtDefGeN {dl n x d}
  (xNlt: ¬ x < n)
:
  ¬ .pair (uniSetMapIndexDef dl n x) d ∈ vals.uniSetMap.posMem
:=
  open DefList in
  fun inMap =>
    let isAtNone :=
      DefList.prefix_none_at (dl:=dl) (n:=n) (x:=x) xNlt ▸
      isAtOfInsDef (InWfm.in_def_no_fv (lane := .posLane) inMap)
    isAtComplVarElim
      (isAtOfInsDef (InWfm.in_def_no_fv (isAtArbIrElim isAtNone d)))
      (uniSetMapDl.getNth (list:=[d]) zero_lt_one)
