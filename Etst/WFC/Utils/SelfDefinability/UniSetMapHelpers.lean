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

-- ## Section: Non-matching expression encoding eliminators
-----------------------------------------------------------

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqZero := inNatElim (n := 0) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqZero)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqOne := inNatElim (n := 1) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqOne)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqTwo := inNatElim (n := 2) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqTwo)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqThree := inNatElim (n := 3) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqThree)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqFour := inNatElim (n := 4) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqFour)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqFive := inNatElim (n := 5) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqFive)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqSix := inNatElim (n := 6) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqSix)))

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
  let ⟨exprGuard, insGuardIr⟩ := inSomeElim insExprGuard
  let ⟨insGuardL, insGuardR⟩ := inIrElim insGuardIr
  match exprGuard with
  | .null => inPairElimNope insGuardL
  | .pair _ _ =>
    let ⟨insNat, _⟩ := inPairElim insGuardL
    let eqI :=
      Pair.noConfusion (inVarElim insGuardR rfl) fun eq _ => eq
    let eqSeven := inNatElim (n := 7) insNat
    False.elim (indexNeq (Pair.nat_inj_eq (eqI.symm.trans eqSeven)))


-- ## Section: Matching expression encoding eliminators
-------------------------------------------------------

def isAtConstElim {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.const x) lane p)
  (cinsSat: (∀ {x d}, d ∈ (c x).getLane lane → uniSetMapDl.Ins x d))
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
      let insGetDef :=
        (cinsSat (inToggle2Elim 8 insDefX)).isSound
      let exprAliasEq :=
        dl.prefixList_at_eq n x ▸
        getNthElimD
          (show intp (const .defLane 0) _ _ _
          from xEncEq ▸ insGetDef)
      by
      unfold uniSetMapIndexDef uniSetMapIndex
      exact
        exprAliasEq ▸ eqFvAlias ▸ eqDlAlias ▸ inToggle2Elim 4 inMap
  (inUnElim ins).elim
    main
    (fun ins =>
      (inUnElim ins).elim
        (isAtVarNope · (by decide))
        (fun ins =>
          (inUnElim ins).elim
            (isAtNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            (isAtComplNope · (by decide))
                            (isAtArbIrNope · (by decide))))))))

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
    let ins := xEncEq ▸ inToggle2Elim 7 ins
    let ins := (cinsSat ins).isSound
    inVar (getNthElim (lane:=.defLane) ins)
  (inUnElim ins).elim
    (isAtConstNope · (by decide))
    (fun ins =>
      (inUnElim ins).elim
        main
        (fun ins =>
          (inUnElim ins).elim
            (isAtNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            (isAtComplNope · (by decide))
                            (isAtArbIrNope · (by decide))))))))

def isAtNullElim := 42 -- TODO
def isAtPairElim := 42 -- TODO
def isAtIrElim := 42 -- TODO
def isAtFullElim := 42 -- TODO

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
  (inUnElim ins).elim
    (isAtConstNope · (by decide))
    (fun ins =>
      (inUnElim ins).elim
        (isAtVarNope · (by decide))
        (fun ins =>
          (inUnElim ins).elim
            (isAtNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            main
                            (isAtArbIrNope · (by decide))))))))

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
    match pArg with
    | .null => inPairElimNope inArg
    | .pair _ .null => inPairElimNope (inPairElim inArg).right
    | .pair dlEncAlias (.pair fvAlias exprAlias) =>
      let ⟨insDlAlias, ins⟩ := inPairElim inArg
      let ⟨insFvAlias, insBodyAlias⟩ := inPairElim ins
      let eqDlAlias := inVarElim insDlAlias rfl
      let eqBodyAlias := inVarElim insBodyAlias rfl
      match fvAlias with
      | .null => inPairElimNope insFvAlias
      | .pair dXAlias fvTailAlias =>
        let ⟨insDXAlias, insFvTailAlias⟩ := inPairElim insFvAlias
        let eqDXAlias := inVarElim insDXAlias rfl
        let eqFvTailAlias := inVarElim insFvTailAlias rfl
        let fvEq:
          Eq
            (Pair.listEncoding (dX :: fv))
            (.pair dX (Pair.listEncoding fv))
          :=
            rfl
        by
        unfold uniSetMapIndex
        exact
          bodyEncEq ▸
          eqBodyAlias ▸
          fvEq ▸
          eqFvTailAlias ▸
          eqDXAlias ▸
          eqDlAlias ▸
          inToggle2Elim 10 inMap
  (inUnElim ins).elim
    (isAtConstNope · (by decide))
    (fun ins =>
      (inUnElim ins).elim
        (isAtVarNope · (by decide))
        (fun ins =>
          (inUnElim ins).elim
            (isAtNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            (isAtComplNope · (by decide))
                            main))))))


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
    (c consts.getNth).getLane lane (getNthEnc dl n x))
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
        (dExt = getNthEnc dl n xInt))
      (And
        (xExt = consts.uniSetMap)
        (dExt = .pair (uniSetMapIndex dl n [] expr) dInt))
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


def isWeakCauseConst {dl n fv x d}:
  (causeConst dl n x d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.const x)) d)
:=
  fun _ _ isSat =>
    let insGetNth := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)

def isWeakCauseCompl {dl n fv body d}:
  (causeCompl dl n fv body d).IsWeakCause
    (uniSetMapDl.getDef consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.compl body)) d)
:=
  fun _ _ isSat =>
    let out := isSat.boutSat (And.intro rfl rfl)
    isInMap (isAtCompl out)
