module
public import Etst.WFC.Utils.SelfDefinability.UniSetMapDl
public import Etst.WFC.Utils.Cause
public import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst.uniSetMapDl
open Expr

exposed def InUniSetMapAtEnc (lane b c p dl n fv exprEnc) :=
  let vars := [
    exprEnc,
    Pair.listEncoding fv,
    DefList.prefixEncoding dl n,
  ]
  p ∈ exprEncListRaw.intp lane b c vars

exposed def InUniSetMapAt (lane b c p dl n fv expr) :=
  InUniSetMapAtEnc lane b c p dl n fv (Expr.encoding expr)


theorem isAtOfInsDefEnc {dl n fv exprEnc lane b c p}
  (ins:
    Set.Mem
      ((uniSetMapDl.dl.getDef (cst "uniSetMap")).intp
        lane
        b
        c
        [])
      (.pair (uniSetMapIndexEnc dl n fv exprEnc) p))
:
  InUniSetMapAtEnc lane b c p dl n fv exprEnc
:=
  let ⟨dlEnc, ins⟩ := inArbUnElim ins
  let ⟨fvEnc, ins⟩ := inArbUnElim ins
  let ⟨exprEncAlias, ins⟩ := inArbUnElim ins
  let ⟨insEnc, insAt⟩ := inProdElim ins
  let ⟨insDl, ins⟩ := inProdElim insEnc
  let ⟨insFv, insExpr⟩ := inProdElim ins
  let dlEncEq := inVarElim insDl rfl
  let fvEncEq := inVarElim insFv rfl
  let exprEncEq := inVarElim insExpr rfl
  by
  unfold InUniSetMapAtEnc
  exact dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insAt

theorem isAtOfInsDef {lane b c p dl n fv expr}
  (ins:
    Set.Mem
      ((uniSetMapDl.dl.getDef (cst "uniSetMap")).intp lane b c [])
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  InUniSetMapAt lane b c p dl n fv expr
:=
  isAtOfInsDefEnc ins


/-
  ## Section: Non-matching expression encoding eliminators
-/

theorem isAtIndexNope
  {actual expected enc lane b c fv p indexExpr restExpr aliasVar}
  (insExprGuard:
    let expr: Expr .basic :=
      .some (ir (prod indexExpr restExpr) (var aliasVar))
    p ∈ expr.intp lane b c fv)
  (evalActual: fv[aliasVar]? = .some (.pair (.nat actual) enc))
  (evalIndex:
    ∀ {pIndex},
      pIndex ∈ indexExpr.intp lane b c fv →
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

exposed def isAtFv (i: Nat) (enc: Pair) (fv: List Pair) :=
  .pair (.nat i) enc :: fv

theorem isAtConstNope {b c fv lane i enc p}
  (ins: p ∈ exprEncConstRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 0)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 0)) indexNeq

theorem isAtComplConstNope {b c fv lane i enc p}
  (ins: p ∈ exprEncComplConstRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 1)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 1)) indexNeq

theorem isAtVarNope {b c fv lane i enc p}
  (ins: p ∈ exprEncVarRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 2)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 2)) indexNeq

theorem isAtComplVarNope {b c fv lane i enc p}
  (ins: p ∈ exprEncComplVarRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 3)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 3)) indexNeq

theorem isAtNullNope {b c fv lane i enc p}
  (ins: p ∈ exprEncNullRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 4)
  {P: Prop}
:
  P
:=
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 4)) indexNeq

theorem isAtProdNope {b c fv lane i enc p}
  (ins: p ∈ exprEncProdRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 5)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 5)) indexNeq

theorem isAtIrNope {b c fv lane i enc p}
  (ins: p ∈ exprEncIrRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 6)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 6)) indexNeq

theorem isAtUnNope {b c fv lane i enc p}
  (ins: p ∈ exprEncUnRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 7)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 7)) indexNeq

theorem isAtFullNope {b c fv lane i enc p}
  (ins: p ∈ exprEncFullRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 8)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 8)) indexNeq

theorem isAtSomeNope {b c fv lane i enc p}
  (ins: p ∈ exprEncSomeRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 9)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 9)) indexNeq

theorem isAtArbIrNope {b c fv lane i enc p}
  (ins: p ∈ exprEncArbIrRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 10)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 10)) indexNeq

theorem isAtArbUnNope {b c fv lane i enc p}
  (ins: p ∈ exprEncArbUnRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 11)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 11)) indexNeq

theorem isAtUniSetMapNope {b c fv lane i enc p}
  (ins: p ∈ exprEncUniSetMapRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 12)
  {P: Prop}
:
  P
:=
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 12)) indexNeq

theorem isAtToEncodingNope {b c fv lane i enc p}
  (ins: p ∈ exprEncToEncodingRaw.intp lane b c (isAtFv i enc fv))
  (indexNeq: i ≠ 13)
  {P: Prop}
:
  P
:=
  let ⟨_, ins⟩ := inArbUnElim ins
  let ⟨insExprGuard, _⟩ := inIrElim ins
  isAtIndexNope insExprGuard rfl (inNatElim (n := 13)) indexNeq

theorem exprEncListElim {b c fv lane p}
  {P: Prop}
  (ins: p ∈ exprEncListRaw.intp lane b c fv)
  (onConst: p ∈ exprEncConstRaw.intp lane b c fv → P)
  (onComplConst: p ∈ exprEncComplConstRaw.intp lane b c fv → P)
  (onVar: p ∈ exprEncVarRaw.intp lane b c fv → P)
  (onComplVar: p ∈ exprEncComplVarRaw.intp lane b c fv → P)
  (onNull: p ∈ exprEncNullRaw.intp lane b c fv → P)
  (onProd: p ∈ exprEncProdRaw.intp lane b c fv → P)
  (onIr: p ∈ exprEncIrRaw.intp lane b c fv → P)
  (onUn: p ∈ exprEncUnRaw.intp lane b c fv → P)
  (onFull: p ∈ exprEncFullRaw.intp lane b c fv → P)
  (onSome: p ∈ exprEncSomeRaw.intp lane b c fv → P)
  (onArbIr: p ∈ exprEncArbIrRaw.intp lane b c fv → P)
  (onArbUn: p ∈ exprEncArbUnRaw.intp lane b c fv → P)
  (onUniSetMap: p ∈ exprEncUniSetMapRaw.intp lane b c fv → P)
  (onToEncoding: p ∈ exprEncToEncodingRaw.intp lane b c fv → P)
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
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onArbUn ins
  | Or.inr ins =>
  match inUnElim ins with
  | Or.inl ins => onUniSetMap ins
  | Or.inr ins => onToEncoding ins


/-
  ## Section: Matching expression encoding eliminators
-/

theorem exprGuardElimUnary {i lane b c iEnc encRest fv0 fvRest p}
  (ins:
    let expr: Expr .basic := some (ir (prod i (var 0)) (var 1))
    p ∈ (expr.intp lane b c (fv0 :: .pair iEnc encRest :: fvRest)))
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

theorem exprGuardElimBinary {i iEnc lane b c encL encR fvRite fvLeft fvRest p}
  (ins:
    let expr: Expr .basic :=
      some (ir (prod i (prod (var 1) (var 0))) (var 2))
    Set.Mem
      (expr.intp lane b c
        (fvRite :: fvLeft :: .pair iEnc (.pair encL encR) :: fvRest))
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
  {dl n b c fv expr lane p fvMeta eDl eFv eExpr exprEnc}
  (inCall:
    Set.Mem
      ((call (cstExpr "uniSetMap") (prod eDl (prod eFv eExpr))).intp
        lane
        b
        c
        fvMeta)
      p)
  (exprEncEq: expr.encoding = exprEnc)
  (evalDl: ∀ {v fvH}, v ∈ eDl.intp lane b c (fvH::fvMeta) → v = dl.prefixEncoding n)
  (evalFv: ∀ {v fvH}, v ∈ eFv.intp lane b c (fvH::fvMeta) → v = Pair.listEncoding fv)
  (evalExpr: ∀ {v fvH}, v ∈ eExpr.intp lane b c (fvH::fvMeta) → v = exprEnc)
:
  ((c (cst "uniSetMap")).getLane lane).Mem
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
    unfold uniSetMapIndex uniSetMapIndexEnc
    rw [←eqDlAlias, ←eqFvAlias, exprEncEq, ←eqExprAlias]
    exact inMap


theorem isAtConstElim {lane b c p dl n fv x}
  (ins: InUniSetMapAt lane b c p dl n fv (.const () x))
  (getNthSat:
    ∀ {list i valEnc},
      getNthEnc list i valEnc ∈ (c (cst "getNth")).getLane lane →
      getNthEnc list i valEnc ∈ (uniSetMapDl.val "getNth").defMem)
:
  ((c (cst "uniSetMap")).getLane lane).Mem
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
      let insDefX := xEncEq ▸ insDefX
      let insGetDef := getNthSat insDefX
      let exprAliasEq :=
        dl.prefixList_at_eq n x ▸
        getNthElimD (lane := .defLane) insGetDef
      by
      unfold uniSetMapIndexDef uniSetMapIndex uniSetMapIndexEnc
      exact
        exprAliasEq ▸ eqFvAlias ▸ eqDlAlias ▸ inMap
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtComplConstElim {lane b c p dl n fv x}
  (ins: InUniSetMapAt lane b c p dl n fv (.compl (.const () x)))
:
  Or
    (Not
      (Set.Mem
        ((b (cst "getNth")).getLane lane.toggle)
        ((getDefNthEnc dl n x))))
    (Not
      (Set.Mem
        ((b (cst "uniSetMap")).getLane lane.toggle)
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
              (xEncEq ▸ insGetNth)
              (inVar rfl))
            (inVar rfl)))
    inComplElim ins (inCall insBody insArg)
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtVarElim {lane b c p dl n fv x}
  (ins: InUniSetMapAt lane b c p dl n fv (.var x))
:
  getNthEnc fv x p ∈ (c (cst "getNth")).getLane lane
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary insExprGuard
    let ins := inCallElimSingle ins rfl
    let ins := inCallElimSingle ins rfl
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtComplVarElim {lane b c p dl n fv x}
  (ins: InUniSetMapAt lane b c p dl n fv (.compl (.var x)))
:
  ¬ getNthEnc fv x p ∈ (b (cst "getNth")).getLane lane.toggle
:=
  let main insCompl insGetNth :=
    let ⟨xEnc, ins⟩ := inArbUnElim insCompl
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimUnary (i := .nat 3) insExprGuard
    inComplElim
      ins
      (inCall
        (inCall
          (xEncEq ▸ insGetNth)
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtNullElim {lane b c p dl n fv}
  (ins: InUniSetMapAt lane b c p dl n fv .null)
:
  p ∈ (Expr.null (kind := .basic)).intp lane b c fv
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtProdElim {lane b c p dl n fv left rite}
  (ins: InUniSetMapAt lane b c p dl n fv (.prod left rite))
:
  ∃ pL pR,
    p = .pair pL pR ∧
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) pL) ∧
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) pR)
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insPair⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary insExprGuard
    let ⟨pL, pR, eqP, insCallLeft, insCallRite⟩ := inProdElimEx insPair
    
    let insLeftAlias := inMapCallElim insCallLeft leftEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    let insRiteAlias := inMapCallElim insCallRite riteEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtIrElim {lane b c p dl n fv left rite}
  (ins: InUniSetMapAt lane b c p dl n fv (.ir left rite))
:
  And
    (((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) p))
    (((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) p))
:=
  let main ins :=
    let ⟨leftEnc, ins⟩ := inArbUnElim ins
    let ⟨riteEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, insPair⟩ := inIrElim ins
    let ⟨leftEncEq, riteEncEq⟩ := exprGuardElimBinary insExprGuard
    
    let ⟨insCallLeft, insCallRite⟩ := inIrElim insPair
    
    let insLeftAlias := inMapCallElim insCallLeft leftEncEq
      (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl)
    
    let insRiteAlias := inMapCallElim insCallRite riteEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtComplIrElim {lane b c p dl n fv left rite}
  (ins: InUniSetMapAt lane b c p dl n fv (compl (.ir left rite)))
:
  Or
    (((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left.compl) p))
    (((c (cst "uniSetMap")).getLane lane).Mem
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
        (inMapCallElim insCallLeft leftEncEq
          (inVarElim · rfl) (inVarElim · rfl) (inVarElim · rfl))
    | .inr insCallRite =>
      let ⟨_pArgRite, inMapRite, inArgRite⟩ := inCallElim insCallRite
      .inr
        (inMapCallElim insCallRite riteEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

/-- The NNF-shaped eliminator corresponding to `isAtUnNnf`. -/
theorem isAtUnElim {lane b c p dl n fv left rite}
  (ins: InUniSetMapAt lane b c p dl n fv (.un left rite))
:
  Or
    (((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) p))
    (((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) p))
:=
  (isAtComplIrElim (left := left.compl) (rite := rite.compl) ins).elim
    .inl
    .inr

theorem isAtFullElim {lane b c p dl n fv body}
  (ins: InUniSetMapAt lane b c p dl n fv (.full body))
:
  ∀ pB,
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv body) pB)
:=
  let main ins pB :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    inMapCallElim (ins pB) bodyEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtComplFullElim {dl n b c fv body lane p}
  (ins: InUniSetMapAt lane b c p dl n fv (.compl (.full body)))
:
  ∃ pB,
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv (.compl body)) pB)
:=
  let main ins :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary (i := .nat 9) insExprGuard
    let ⟨pB, insArg⟩ := inSomeElim ins
    let ⟨_pArg, inMap, inArg⟩ := inCallElim insArg
    ⟨pB,
      inMapCallElim insArg bodyEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtArbIrElim {lane b c p dl n fv body}
  (ins: InUniSetMapAt lane b c p dl n fv (.arbIr body))
:
  ∀ pX,
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n (pX :: fv) body) p)
:=
  let main ins pX :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary insExprGuard
    inMapCallElim (ins pX) bodyEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))

theorem isAtComplArbIrElim {lane b c p dl n fv body}
  (ins: InUniSetMapAt lane b c p dl n fv (.compl (.arbIr body)))
:
  ∃ pX,
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n (pX :: fv) (.compl body)) p)
:=
  let main ins :=
    let ⟨bodyEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let bodyEncEq := exprGuardElimUnary (i := .nat 11) insExprGuard
    let ⟨pX, insArg⟩ := inArbUnElim ins
    ⟨pX,
      inMapCallElim insArg bodyEncEq
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
    (isAtUniSetMapNope · (by decide))
    (isAtToEncodingNope · (by decide))


/-
  ## Section: Expression encoding constructors
-/

theorem isInMapEnc {lane b c p dl n fv exprEnc}
  (isAt: InUniSetMapAtEnc lane b c p dl n fv exprEnc)
:
  Set.Mem
    ((uniSetMapDl.getDef "uniSetMap").intp lane b c [])
    (.pair (uniSetMapIndexEnc dl n fv exprEnc) p)
:=
  inArbUn
    (dl.prefixEncoding n)
    (inArbUn
      (.listEncoding fv)
      (inArbUn
        exprEnc
        (inProd
          (inProd rfl (inProd rfl rfl))
          isAt)))

theorem isInMap {lane b c p dl n fv expr}
  (isAt: InUniSetMapAt lane b c p dl n fv expr)
:
  Set.Mem
    ((uniSetMapDl.getDef "uniSetMap").intp lane b c [])
    (.pair (uniSetMapIndex dl n fv expr) p)
:=
  isInMapEnc isAt

theorem isAtConst {lane b c p dl n fv x}
  (ins:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndexDef dl n x) p))
  (insGetNth:
    ((c (cst "getNth")).getLane lane).Mem (getDefNthEnc dl n x))
:
  InUniSetMapAt lane b c p dl n fv (.const () x)
:=
  inUnL
    (inArbUn
      (.nat x)
      (inIr
        (inSome _ (inIr (inProd (inNat 0) rfl) rfl))
        (inCall
          ins
          (inProd
            rfl
            (inProd
              inNull
              (inCall
                (inCall
                  insGetNth
                  rfl)
                rfl))))))

theorem isAtComplConst {lane b c p dl n fv x}
  (ninGetNth:
    (∀ {exprEnc: Pair},
      exprEnc ≠ ((dl.prefix n).getDef x).encoding →
      Not
        (((b (cst "getNth")).getLane lane.toggle).Mem
          (getNthEnc (dl.prefixList 0 n) x exprEnc))))
  (ninMap:
    Not
      (((b (cst "uniSetMap")).getLane lane.toggle).Mem
        (.pair (uniSetMapIndexDef dl n x) p)))
:
  InUniSetMapAt lane b c p dl n fv (.compl (.const () x))
:=
  inUnR
    (inUnL
      (inArbUn
        (.nat x)
        (inIr
          (inSome _ (inIr (inProd (inNat 1) rfl) rfl))
          (inCompl fun insBody =>
            let inMap := inMapCallElim insBody rfl
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
                  exact inFn
                byContradiction (ninGetNth · inFn))
            ninMap inMap))))

theorem isAtVar {lane b c p dl n fv x}
  (insGetNth:
    ((c (cst "getNth")).getLane lane).Mem (getNthEnc fv x p))
:
  InUniSetMapAt lane b c p dl n fv (.var x)
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
          insGetNth
          rfl)
        rfl)))))

theorem isAtComplVar {lane b c p dl n fv x}
  (ninGetNth:
    Not
      (((b (cst "getNth")).getLane lane.toggle).Mem
        (getNthEnc fv x p)))
:
  InUniSetMapAt lane b c p dl n fv (.compl (.var x))
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
          ninGetNth insGetNth))))))

theorem isAtNull {lane b c dl n fv}:
  InUniSetMapAt lane b c .null dl n fv .null
:=
  inUnR
  (inUnR
  (inUnR
  (inUnR
  (inUnL
  (inIr
    (inSome _ (inIr (inProd (inNat 4) inNull) rfl))
    inNull)))))

theorem isAtProd {lane b c pL pR dl n fv left rite}
  (insLeft:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) pL))
  (insRite:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) pR))
:
  InUniSetMapAt lane b c (.pair pL pR) dl n fv (.prod left rite)
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
            insLeft
            (inProd rfl (inProd rfl (inVar rfl))))
          (inCall
            insRite
            (inProd rfl (inProd rfl (inVar rfl)))))))))))))

theorem isAtIr {lane b c p dl n fv left rite}
  (insLeft:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv left) p))
  (insRite:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv rite) p))
:
  InUniSetMapAt lane b c p dl n fv (.ir left rite)
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
            insLeft
            (inProd rfl (inProd rfl (inVar rfl))))
          (inCall
            insRite
            (inProd rfl (inProd rfl (inVar rfl))))))))))))))

theorem isAtUn {lane b c p dl n fv left rite}
  (ins:
    Or
      (((c (cst "uniSetMap")).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv left.compl) p))
      (((c (cst "uniSetMap")).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv rite.compl) p)))
:
  InUniSetMapAt lane b c p dl n fv (.compl (.ir left rite))
:=
  let ins :=
    match ins with
    | .inl insLeft =>
      inUnL
        (inCall
          insLeft
          (inProd rfl (inProd rfl (inVar rfl))))
    | .inr insRite =>
      inUnR
        (inCall
          insRite
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

/--
  An NNF-shaped variant of `isAtUn`. The statements of `isAtUn` and
  `isAtComplIrElim` mention the pre-NNF shape `.compl (.ir left rite)`,
  which never matches `.un`-headed goals syntactically; the defeq
  fallback then normalizes the compiled `exprEncListRaw`, which blows
  `maxRecDepth`. Use this variant (and `isAtUnElim`) at `.un`-headed
  use sites to keep unification syntactic.
-/
theorem isAtUnNnf {lane b c p dl n fv left rite}
  (ins:
    Or
      (((c (cst "uniSetMap")).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv left) p))
      (((c (cst "uniSetMap")).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv rite) p)))
:
  InUniSetMapAt lane b c p dl n fv (.un left rite)
:=
  isAtUn (ins.elim .inl .inr)

theorem isAtFull {lane b c p dl n fv body}
  (insBody:
    ∀ dB,
      ((c (cst "uniSetMap")).getLane lane).Mem
        (.pair (uniSetMapIndex dl n fv body) dB))
:
  InUniSetMapAt lane b c p dl n fv (.full body)
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
          (insBody dB)
          (inProd rfl (inProd rfl (inVar rfl))))))))))))))

theorem isAtSome {lane b c p dl n fv body}
  (dB: Pair)
  (insBody:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n fv body.compl) dB))
:
  InUniSetMapAt lane b c p dl n fv (.compl (.full body))
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
          insBody
          (inProd rfl (inProd rfl (inVar rfl))))))))))))))))

theorem isAtArbIr {lane b c p dl n fv body}
  (insBody:
    ∀ dX,
      ((c (cst "uniSetMap")).getLane lane).Mem
        (.pair (uniSetMapIndex dl n (dX :: fv) body) p))
:
  InUniSetMapAt lane b c p dl n fv (.arbIr body)
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
          (insBody dX)
          (inProd
            rfl
            (inProd
              (inProd rfl rfl)
              rfl)))))))))))))))

theorem isAtArbUn {lane b c p dl n fv body}
  (dX: Pair)
  (insBody:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndex dl n (dX :: fv) body.compl) p))
:
  InUniSetMapAt lane b c p dl n fv (.compl (.arbIr body))
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
  (inUnL
  (inArbUn
    body.compl.encoding
    (inIr
      (inSome _ (inIr (inProd (inNat 11) rfl) rfl))
      (inArbUn
        dX
        (inCall
          insBody
          (inProd
            rfl
            (inProd
              (inProd rfl rfl)
              rfl)))))))))))))))))

/-
  ## Section: The extension encodings

  `(12, null)` denotes `uniSetMap` itself, and `(13, b)` denotes the
  singleton triset containing the encoding of `b` as an expression.
-/

theorem isAtUniSetMap {lane b c p dl n fv}
  (ins: ((c (cst "uniSetMap")).getLane lane).Mem p)
:
  InUniSetMapAtEnc lane b c p dl n fv (.pair (.nat 12) .null)
:=
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnL <|
  inIr
    (inSome p (inIr (inProd (inNat 12) inNull) (inVar rfl)))
    ins

theorem isAtToEncodingNull {lane b c dl n fv}:
  InUniSetMapAtEnc lane b c (.pair (.nat 4) .null)
    dl n fv (.pair (.nat 13) .null)
:=
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inUnR <|
  inArbUn .null <|
  inIr
    (inSome _ (inIr (inProd (inNat 13) (inVar rfl)) (inVar rfl)))
    (inUnL <|
      inIr
        (inSome _ (inIr (inVar rfl) inNull))
        (inProd (inNat 4) inNull))


theorem isAtToEncodingPair {lane b c qL qR dl n fv pL pR}
  (insL:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndexEnc dl n fv (.pair (.nat 13) pL)) qL))
  (insR:
    ((c (cst "uniSetMap")).getLane lane).Mem
      (.pair (uniSetMapIndexEnc dl n fv (.pair (.nat 13) pR)) qR))
:
  InUniSetMapAtEnc lane b c (.pair (.nat 5) (.pair qL qR))
    dl n fv (.pair (.nat 13) (.pair pL pR))
:=
  inUnR <| inUnR <| inUnR <| inUnR <| inUnR <| inUnR <|
  inUnR <| inUnR <| inUnR <| inUnR <| inUnR <| inUnR <|
  inUnR <|
  inArbUn (.pair pL pR) <|
  inIr
    (inSome _
      (inIr (inProd (inNat 13) (inVar rfl)) (inVar rfl)))
    (inUnR <|
      inArbUn pL <|
      inArbUn pR <|
      inIr
        (inSome _
          (inIr (inVar rfl) (inProd (inVar rfl) (inVar rfl))))
        (inProd
          (inNat 5)
          (inProd
            (inCall
              insL
              (inProd rfl (inProd rfl (inProd (inNat 13) (inVar rfl)))))
            (inCall
              insR
              (inProd rfl (inProd rfl (inProd (inNat 13) (inVar rfl))))))))


/-
  ## Section: Cause building
-/

exposed def causeExpr
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: Expr .basic)
  (p: Pair)
:
  Cause Pair
:=
  Cause.cinsJust
    (cst "uniSetMap")
    (.pair (uniSetMapIndex dl n fv expr) p)

exposed def causeTwoExprs
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (left rite: Expr .basic)
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
      (cst "getNth")
      (getDefNthEnc dl n xInt))
    (Cause.cinsJust
      (cst "uniSetMap")
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
        xExt = (cst "getNth") ∧
        dExt = getNthEnc (dl.prefixList 0 n) xInt exprEnc)
      (xExt = (cst "uniSetMap") ∧
        dExt = .pair (uniSetMapIndexDef dl n xInt) dInt)
}

exposed def causeVar
  (fv: List Pair)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.cinsJust (cst "getNth") (getNthEnc fv xInt dInt)

exposed def causeComplVar
  (fv: List Pair)
  (xInt: Nat)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.boutJust (cst "getNth") (getNthEnc fv xInt dInt)

exposed def causeFull
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: Expr .basic)
:
  Cause Pair
:= {
  cins xExt dExt :=
    ∃ dB,
      xExt = (cst "uniSetMap") ∧
      dExt = .pair (uniSetMapIndex dl n fv body) dB
  bout _ _ := False
}

exposed def causeSome
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: Expr .basic)
  (dBody: Pair)
:
  Cause Pair
:=
  Cause.cinsJust
    (cst "uniSetMap")
    (.pair (uniSetMapIndex dl n fv body) dBody)

exposed def causeArbIr
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: Expr .basic)
  (dInt: Pair)
:
  Cause Pair
:= {
  cins xExt dExt :=
    ∃ dX,
      xExt = (cst "uniSetMap") ∧
      dExt = .pair (uniSetMapIndex dl n (dX :: fv) body) dInt
  bout _ _ := False
}

exposed def causeArbUn
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (body: Expr .basic)
  (dX: Pair)
  (dInt: Pair)
:
  Cause Pair
:=
  Cause.cinsJust
    (cst "uniSetMap")
    (.pair (uniSetMapIndex dl n (dX :: fv) body) dInt)

theorem isWeakCauseConst {dl n fv x p}:
  (causeConst dl n x p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.const () x)) p)
:=
  fun _ _ isSat =>
    let insGetNth := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)

theorem isWeakCauseComplConst {dl n fv x p}:
  (causeComplConst dl n x p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.compl (.const () x))) p)
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

theorem isWeakCauseVar {dl n fv x p}:
  (causeVar fv x p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.var x)) p)
:=
  fun _ _ isSat =>
    let inGetNth := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtVar inGetNth)

theorem isWeakCauseComplVar {dl n fv x p}:
  (causeComplVar fv x p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.compl (.var x))) p)
:=
  fun _ _ isSat =>
    let ninGetNth :=
      fun inGetNth =>
        isSat.boutSat ⟨rfl, rfl⟩ inGetNth
    isInMap (isAtComplVar ninGetNth)

theorem isWeakCauseNull {dl n fv}:
  Cause.empty.IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv .null) .null)
:=
  fun _ _ _ => isInMap isAtNull

theorem isWeakCauseProd {dl n fv left rite pL pR}:
  (causeTwoExprs dl n fv left rite pL pR).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.prod left rite)) (.pair pL pR))
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let inRite := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtProd inLeft inRite)

theorem isWeakCauseIr {dl n fv left rite p}:
  (causeTwoExprs dl n fv left rite p p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.ir left rite)) p)
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let inRite := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtIr inLeft inRite)

theorem isWeakCauseUnL {dl n fv p}
  (left rite: Expr .basic)
:
  (causeExpr dl n fv left p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.un left rite)) p)
:=
  fun _ _ isSat =>
    let inLeft := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtUn (Or.inl inLeft))

theorem isWeakCauseUnR {dl n fv p}
  (left rite: Expr .basic)
:
  (causeExpr dl n fv rite p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.un left rite)) p)
:=
  fun _ _ isSat =>
    let inRite := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtUn (Or.inr inRite))

theorem isWeakCauseFull {dl n fv body p}:
  (causeFull dl n fv body).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.full body)) p)
:=
  fun _ _ isSat =>
    isInMap (isAtFull fun dB => isSat.cinsSat ⟨dB, rfl, rfl⟩)

theorem isWeakCauseSome {dl n fv p}
  (body: Expr .basic)
  (dBody: Pair)
:
  (causeSome dl n fv body dBody).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.some body)) p)
:=
  fun _ _ isSat =>
    let inBody := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtSome dBody inBody)

theorem isWeakCauseArbIr {dl n fv body p}:
  (causeArbIr dl n fv body p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.arbIr body)) p)
:=
  fun _ _ isSat =>
    isInMap (isAtArbIr fun dX => isSat.cinsSat ⟨dX, rfl, rfl⟩)

theorem isWeakCauseArbUn {dl n fv body dX p}:
  (causeArbUn dl n fv body dX p).IsWeakCause
    (uniSetMapDl.getDef "uniSetMap")
    (.pair (uniSetMapIndex dl n fv (.arbUn body)) p)
:=
  fun _ _ isSat =>
    let inBody := isSat.cinsSat ⟨rfl, rfl⟩
    isInMap (isAtArbUn dX inBody)

/-
  ## Section: Some extra randos
-/

exposed noncomputable def usmWfm := uniSetMapDl.dl.wfm

theorem isAtAny {dl n fv p lane}:
  InUniSetMapAt lane usmWfm usmWfm p dl n fv .any
:=
  isAtArbUn
    p
    (DefList.in_def_no_fv
      (isInMap
        (isAtVar
          (uniSetMapDl.getNth
            (Nat.succ_pos fv.length)))))

theorem notAtDefGeN {dl n x d}
  (xNlt: ¬ x < n)
:
  Not
    ((uniSetMapDl.val "uniSetMap").posMem.Mem
      (.pair (uniSetMapIndexDef dl n x) d))
:=
  open DefList in
  fun inMap =>
    let isAtNone :=
      DefList.prefix_none_at (dl:=dl) (n:=n) (x:=x) xNlt ▸
      isAtOfInsDef (in_def_body_no_fv (lane := .posLane) inMap)
    isAtComplVarElim
      (isAtOfInsDef (in_def_body_no_fv (isAtArbIrElim isAtNone d)))
      (uniSetMapDl.getNth (list:=[d]) zero_lt_one)
