import Etst.WFC.Utils.MembershipPs.OutIntro3
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


-- ## Section: Non-matching expression encoding eliminators
-----------------------------------------------------------

def isAtElimConstNope {fv b c lane i enc p}
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

def isAtElimVarNope {fv b c lane i enc p}
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

def isAtElimNullNope {fv b c lane i enc p}
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

def isAtElimPairNope {fv b c lane i enc p}
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

def isAtElimIrNope {fv b c lane i enc p}
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

def isAtElimFullNope {fv b c lane i enc p}
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

def isAtElimComplNope {fv b c lane i enc p}
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

def isAtElimArbIrNope {fv b c lane i enc p}
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

def isAtElimConst {dl n fv b c lane x p}
  (ins: InUniSetMapAt dl n fv b c (.const x) lane p)
  (cinsSat: (∀ {x d}, d ∈ (c x).getLane lane → uniSetMapDl.Ins x d))
:
  (c uniSetMapDl.consts.uniSetMap).getLane
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
        uniSetMapDl.getNthElimD
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
        (isAtElimVarNope · (by decide))
        (fun ins =>
          (inUnElim ins).elim
            (isAtElimNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtElimPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtElimIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtElimFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            (isAtElimComplNope · (by decide))
                            (isAtElimArbIrNope · (by decide))))))))

def isAtElimVar {dl n fv b c lane x p}
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
    inVar (uniSetMapDl.getNthElim (lane:=.defLane) ins)
  (inUnElim ins).elim
    (isAtElimConstNope · (by decide))
    (fun ins =>
      (inUnElim ins).elim
        main
        (fun ins =>
          (inUnElim ins).elim
            (isAtElimNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtElimPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtElimIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtElimFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            (isAtElimComplNope · (by decide))
                            (isAtElimArbIrNope · (by decide))))))))

def isAtElimNull := 42 -- TODO
def isAtElimPair := 42 -- TODO
def isAtElimIr := 42 -- TODO
def isAtElimFull := 42 -- TODO

def isAtElimCompl {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.compl body) lane p)
:
  Not
    ((b uniSetMapDl.consts.uniSetMap).getLane
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
    (isAtElimConstNope · (by decide))
    (fun ins =>
      (inUnElim ins).elim
        (isAtElimVarNope · (by decide))
        (fun ins =>
          (inUnElim ins).elim
            (isAtElimNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtElimPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtElimIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtElimFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            main
                            (isAtElimArbIrNope · (by decide))))))))

def isAtElimArbIr {dl n fv b c body lane p}
  (ins: InUniSetMapAt dl n fv b c (.arbIr body) lane p)
:
  ∀ dX,
    (c uniSetMapDl.consts.uniSetMap).getLane
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
    (isAtElimConstNope · (by decide))
    (fun ins =>
      (inUnElim ins).elim
        (isAtElimVarNope · (by decide))
        (fun ins =>
          (inUnElim ins).elim
            (isAtElimNullNope · (by decide))
            (fun ins =>
              (inUnElim ins).elim
                (isAtElimPairNope · (by decide))
                (fun ins =>
                  (inUnElim ins).elim
                    (isAtElimIrNope · (by decide))
                    (fun ins =>
                      (inUnElim ins).elim
                        (isAtElimFullNope · (by decide))
                        (fun ins =>
                          (inUnElim ins).elim
                            (isAtElimComplNope · (by decide))
                            main))))))


/-
  ## Section: Expression encoding constructors
-/

def isInMap {dl n fv b c expr lane p}
  (isAt: InUniSetMapAt dl n fv b c expr lane p)
:
  intp2
    (BasicExpr.toLane
      (uniSetMapDl.getDef uniSetMapDl.consts.uniSetMap)
      lane)
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
    (c uniSetMapDl.consts.uniSetMap).getLane
      lane
      (.pair (uniSetMapIndexDef dl n x) p))
  (insGetNth:
    (c uniSetMapDl.consts.getNth).getLane
      lane
      (uniSetMapDl.getNthEnc dl n x))
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
      ((b uniSetMapDl.consts.uniSetMap).getLane
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
        (xExt = uniSetMapDl.consts.getNth)
        (dExt = uniSetMapDl.getNthEnc dl n xInt))
      (And
        (xExt = uniSetMapDl.consts.uniSetMap)
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
      (xExt = uniSetMapDl.consts.uniSetMap)
      (dExt = .pair (uniSetMapIndex dl n fv body) dInt)
}

def isWeakCauseConst {dl n fv x d}:
  (causeConst dl n x d).IsWeakCause
    (uniSetMapDl.getDef uniSetMapDl.consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.const x)) d)
:=
  fun _ _ isSat =>
    let insGetNth := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)

def isWeakCauseCompl {dl n fv body d}:
  (causeCompl dl n fv body d).IsWeakCause
    (uniSetMapDl.getDef uniSetMapDl.consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.compl body)) d)
:=
  fun _ _ isSat =>
    let out := isSat.boutSat (And.intro rfl rfl)
    isInMap (isAtCompl out)


/-
  ## Section: The main recursive proof
-/
def IsInappExtIh
  (dl: DefList)
  (outSet: Nat → Set Pair)
  (externalCause: Cause Pair)
:
  Prop
:=
  externalCause.IsInapplicable outSet fun x d =>
    {n fv expr dInt: _} →
    x = uniSetMapDl.consts.uniSetMap →
    d = .pair (uniSetMapIndex dl n fv expr) dInt →
    ((dl.prefix n).triIntp fv expr).defMem dInt

def intOfExtCycle
  (dl: DefList)
  (n: Nat)
  (extCycle: Nat → Set Pair)
  (x: Nat)
  (d: Pair)
:
  Prop
:=
  Or
    (extCycle
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndexDef dl n x) d))
    (¬ x < n)

def allInternalInapp {dl n fv d expr}
  {extCycle: Nat → Set Pair}
  (extIsEmpty:
    ∀ {x d},
      extCycle x d →
      (cause: Cause Pair) →
      cause.IsWeakCause (uniSetMapDl.getDef x) d →
      uniSetMapDl.IsCauseInapplicable extCycle cause)
  (everyCauseInapp:
    ∀ {x d},
      extCycle x d →
      (cause: Cause Pair) →
      cause.IsWeakCause (uniSetMapDl.getDef x) d →
      IsInappExtIh dl extCycle cause)
  (inExtCycle:
    extCycle
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) d))
  (cause : Cause Pair)
  (isCause: cause.IsWeakCauseFv fv expr d)
:
  (dl.prefix n).IsCauseInapplicableExtended
    (intOfExtCycle dl n extCycle)
    cause
:=
  match expr with
  | .const x =>
    if h: x < n then
      let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseConst
      match isExtInapp with
      | .blockedCins (d:=dd) (x:=xx) (Or.inl ⟨xEq, dEq⟩) inCycle =>
        let out := DefList.Out.intro extCycle extIsEmpty inCycle
        let insGetNth :=
          uniSetMapDl.getNthDl (lane:=.posLane) (fv:=[]) h
        False.elim (out.isSound (xEq ▸ dEq ▸ insGetNth))
      | .blockedCins (d:=dd) (x:=xx) (Or.inr ⟨xEq, dEq⟩) inCycle =>
        let inCycle:
          extCycle
            uniSetMapDl.consts.uniSetMap
            (.pair (uniSetMapIndexDef dl n x) d)
        :=
          xEq ▸ dEq ▸ inCycle
        let intCycle x d :=
          extCycle
            uniSetMapDl.consts.uniSetMap
            (.pair (uniSetMapIndex dl n fv (.const x)) d)
        .blockedCinsCycle isCause.constElim (Or.inl inCycle)
    else
      .blockedCinsCycle isCause.constElim (Or.inr h)
  | .var _ => sorry
  | .null => sorry
  | .pair _ _ => sorry
  | .ir _ _ => sorry
  | .full _ => sorry
  | .compl _ =>
    let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseCompl
    match isExtInapp with
    | .blockedBout (d:=dd) (x:=xx) ⟨xEq, dEq⟩ isDefFn =>
      let isDef := not_not_intro (isDefFn xEq dEq)
      let isInapp := isCause.isInapplicableOfIsNonmember isDef
      match isInapp with
      | .blockedCins inCins notPos =>
        .blockedCinsOut inCins (DefList.Out.isComplete notPos)
      | .blockedBout inBout isDef =>
        .blockedBout inBout (DefList.Ins.isComplete isDef)
  | .arbIr _ => sorry

/-
  Has to use the weird equality trick :( else we get:
  
  ```
    fail to show termination for
    [...]
    Not considering parameter ins of Etst.externalInsElimHelper:
      its type Etst.DefList.Ins is an inductive family and
      indices are not variables
  ```
-/
mutual
def externalInsElimHelper {dl n fv index cst expr p}
  (ins: uniSetMapDl.Ins cst index)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
:
(expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  match ins with
  | .intro _ _ cause isCause cinsSat boutSat =>
    let ins := isCause cause.leastValsApxAreSat
    let ⟨dlEnc, ins⟩ := inArbUnElim (cstEq ▸ indexEq ▸ ins)
    let ⟨fvEnc, ins⟩ := inArbUnElim ins
    let ⟨exprEnc, ins⟩ := inArbUnElim ins
    let ⟨insEnc, insList⟩ := inPairElim ins
    let ⟨dlEncEq, fvEncEq, exprEncEq⟩ :=
      let ⟨insDl, ins⟩ := inPairElim insEnc
      let ⟨insFv, insExpr⟩ := inPairElim ins
      And.intro
        (inVarElim insDl rfl)
        (And.intro
          (inVarElim insFv rfl)
          (inVarElim insExpr rfl))
    
    match expr with
    | .const x =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      let inCins := isAtElimConst insList cinsSat
      let ih := externalInsElimHelper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .var x =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      isAtElimVar insList cinsSat
    | .null => sorry
    | .pair _ _ => sorry
    | .ir _ _ => sorry
    | .full _ => sorry
    | .compl _ =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      let inBout := boutSat (isAtElimCompl insList).dne
      externalOutElimHelper inBout rfl rfl
    | .arbIr _ =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      inArbIr fun dX =>
        let insBody := cinsSat (isAtElimArbIr insList dX)
        externalInsElimHelper insBody rfl rfl

def externalOutElimHelper {dl n fv index cst expr p}
  (out: uniSetMapDl.Out cst index)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  match out with
  | .intro extCycle extIsEmpty inExtCycle =>
    let everyCauseInapp {x d}
      (inCycle: extCycle x d)
      {cause}
      (isCause: cause.IsWeakCause (uniSetMapDl.getDef x) d)
    :
      IsInappExtIh dl extCycle cause
    :=
      match extIsEmpty inCycle cause isCause with
      | .blockedCins _ inCins inCycle =>
        .blockedCins inCins inCycle
      | .blockedBout _ inBout ins =>
        .blockedBout inBout fun xEq dEq =>
          externalInsElimHelper ins xEq dEq
    
    fun isPos =>
      let isCause: Cause.IsWeakCauseFv _ fv expr p :=
        Cause.IsWeakCauseFv.ofValPos isPos
      let isInapplicable :=
        allInternalInapp
          extIsEmpty
          everyCauseInapp
          (cstEq ▸ indexEq ▸ inExtCycle)
          _
          isCause
      match isInapplicable with
      | .blockedCinsCycle inCins inCycle =>
        let out :=
          DefList.Out.intro3
            (intOfExtCycle dl n extCycle)
            (fun
            | Or.inl inCycle =>
              allInternalInapp extIsEmpty everyCauseInapp inCycle
            | Or.inr xNotLt =>
              fun cause isCause =>
                let isCause :=
                  DefList.prefix_none_at xNotLt ▸ isCause
                isCause.noneElim)
            inCycle
        out.nopePos inCins
      | .blockedCinsOut inCins out => out.isSound inCins
      | .blockedBout inBout ins => ins.nopeNotDef inBout
end


-- ## Section: The main result of the file

def externalInsElim {dl n fv expr p}
  (ins:
    uniSetMapDl.Ins
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  externalInsElimHelper ins rfl rfl

def externalOutElim {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  externalOutElimHelper out rfl rfl

def uniSetMapAt_le
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  uniSetMapAt dl n fv expr ⊑ expr.triIntp fv (dl.prefix n).wfm
:= {
  defLe _ := externalInsElim ∘ DefList.Ins.isComplete
  posLe _ :=
    Function.mtr (externalOutElim ∘ DefList.Out.isComplete)
}
