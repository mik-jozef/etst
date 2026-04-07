import Etst.WFC.Utils.SelfDefinability.UniSetMapDl

namespace Etst
open SingleLaneExpr

set_option pp.fieldNotation false


def InUniSetMapDefAt (dl n fv b c expr lane p) :=
  let vars := [
    BasicExpr.encoding expr,
    Pair.listEncoding fv,
    DefList.prefixEncoding dl n,
  ]
  intp2 (exprEncList.toLane lane) vars b c p

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
  (ins: InUniSetMapDefAt dl n fv b c (.const x) lane p)
  (cinsSat: (∀ {x d}, d ∈ (c x).getLane lane → uniSetMapDl.Ins x d))
:
  (c uniSetMapDl.consts.uniSetMap).getLane
    lane
    (.pair (uniSetMapIndex dl n [] ((dl.prefix n).getDef x)) p)
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
      unfold uniSetMapIndex
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

def isAtElimVar {dl n fv b c i lane p}
  (ins: InUniSetMapDefAt dl n fv b c (.var i) lane p)
  (cinsSat: (∀ {x d}, d ∈ (c x).getLane lane → uniSetMapDl.Ins x d))
:
  sorry
:=
  sorry

def isAtElimNull := 42 -- TODO
def isAtElimPair := 42 -- TODO
def isAtElimIr := 42 -- TODO
def isAtElimFull := 42 -- TODO

def isAtElimCompl {dl n fv b c body lane p}
  (ins: InUniSetMapDefAt dl n fv b c (.compl body) lane p)
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


/-
  ## Section: Expression encoding constructors
-/

def isInMap {dl n fv b c expr lane p}
  (isAt: InUniSetMapDefAt dl n fv b c expr lane p)
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
      (.pair (uniSetMapIndex dl n [] ((dl.prefix n).getDef x)) p))
  (insGetNth:
    (c uniSetMapDl.consts.getNth).getLane
      lane
      (uniSetMapDl.getNthEnc dl n x))
:
  InUniSetMapDefAt dl n fv b c (.const x) lane p
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

def isWeakCauseConst {dl n fv x d}:
  (causeConst dl n x d).IsWeakCause
    (uniSetMapDl.getDef uniSetMapDl.consts.uniSetMap)
    (.pair (uniSetMapIndex dl n fv (.const x)) d)
:=
  fun _ _ isSat =>
    let insGetNth := isSat.cinsSat (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.cinsSat (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)


def Cause.IsWeakCauseFv.constElim {x d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCause (.const x) d)
:
  cause.cins x d
:=
  byContradiction fun notInCins =>
    let isSat := cause.maximalValsApxAreSat
    notInCins (isCause isSat)

def Cause.IsWeakCauseFv.noneElim {d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCause (.none) d)
  {P: Prop}
:
  P
:=
  inNoneElim (isCause cause.maximalValsApxAreSat)


/-
  ## Section: The main recursive proof
  
  Has to use the weird equality trick :( else we get:
  
  ```
    fail to show termination for
    [...]
    Not considering parameter ins of Etst.uniSetMapAt_le_ins:
      its type Etst.DefList.Ins is an inductive family and
      indices are not variables
  ```
-/
inductive uniSetMapAt_le.IsInappIh
(dl: DefList)
:
  (Nat → Set Pair) →
  Cause Pair →
  Prop
|
  blockedCins
  (cause: Cause Pair)
  {x d} (inContextIns: cause.cins x d)
  {cycle} (inCycle: cycle x d)
:
  IsInappIh dl cycle cause
|
  blockedBout {cycle}
  (cause: Cause Pair)
  {x d} (inBout: cause.bout x d)
  (isDef:
    {n i: Nat} →
    d = .pair (uniSetMapIndex dl n [] (.const i)) d →
    x = uniSetMapDl.consts.uniSetMap →
    ((dl.prefix n).wfm i).defMem d)
:
  IsInappIh dl cycle cause

def uniSetMapAt_le.intOfExtCycle
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
      (.pair
        (uniSetMapIndex dl n [] ((dl.prefix n).getDef x))
        d))
    (¬ x < n)

def uniSetMapAt_le.allInternalInapp {dl n fv d expr}
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
      uniSetMapAt_le.IsInappIh dl extCycle cause)
  (inExtCycle:
    extCycle
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) d))
  (cause : Cause Pair)
  (isCause: cause.IsWeakCauseFv fv expr d)
:
  (dl.prefix n).IsCauseInapplicable
    (intOfExtCycle dl n extCycle)
    cause
:=
  match expr with
  | .const x =>
    if h: x < n then
      let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseConst
      match isExtInapp with
      | .blockedCins (d:=dd) (x:=xx) _ (Or.inl ⟨xEq, dEq⟩) inCycle =>
        let out := DefList.Out.intro extCycle extIsEmpty inCycle
        -- let xEq: xx = _ := xEq
        -- let dEq: dd = _ := dEq
        let insGetNth :=
          uniSetMapDl.getNthDl (lane:=.posLane) (fv:=[]) h
        False.elim (out.isSound (xEq ▸ dEq ▸ insGetNth))
      | .blockedCins (d:=dd) (x:=xx) _ (Or.inr ⟨xEq, dEq⟩) inCycle =>
        -- let xEq: xx = _ := xEq
        -- let dEq: dd = _ := dEq
        let inCycle:
          extCycle
            uniSetMapDl.consts.uniSetMap
            (.pair
              (uniSetMapIndex dl n [] ((dl.prefix n).getDef x))
              d)
        :=
          xEq ▸ dEq ▸ inCycle
        let intCycle x d :=
          extCycle
            uniSetMapDl.consts.uniSetMap
            (.pair (uniSetMapIndex dl n fv (.const x)) d)
        .blockedCins _ isCause.constElim (Or.inl inCycle)
    else
      .blockedCins _ isCause.constElim (Or.inr h)
  | .var _ => sorry
  | .null => sorry
  | .pair _ _ => sorry
  | .ir _ _ => sorry
  | .full _ => sorry
  | .compl _ => sorry
  | .arbIr _ => sorry

mutual
def uniSetMapAt_le_ins_helper {dl n fv index cst expr p}
  (ins: uniSetMapDl.Ins cst index)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
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
      let ih := uniSetMapAt_le_ins_helper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .var _ => sorry
    | .null => sorry
    | .pair _ _ => sorry
    | .ir _ _ => sorry
    | .full _ => sorry
    | .compl _ =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      let inBout := boutSat (isAtElimCompl insList).dne
      uniSetMapAt_le_out_helper inBout rfl rfl
    | .arbIr _ => sorry

def uniSetMapAt_le_out_helper {dl n fv index cst expr p}
  (out: uniSetMapDl.Out cst index)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  open uniSetMapAt_le in
  match out with
  | .intro extCycle extIsEmpty inExtCycle =>
    let everyCauseInapp {x d}
      (inCycle: extCycle x d)
      {cause}
      (isCause: cause.IsWeakCause (uniSetMapDl.getDef x) d)
    :
      IsInappIh dl extCycle cause
    :=
      match extIsEmpty inCycle cause isCause with
      | .blockedCins _ inCins inCycle =>
        .blockedCins cause inCins inCycle
      | .blockedBout _ inBout ins =>
        .blockedBout cause inBout fun dEq xEq =>
          uniSetMapAt_le_ins_helper ins dEq xEq
    
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
      | .blockedCins _ inCins inCycle =>
        let out :=
          DefList.Out.intro
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
      | .blockedBout _ inBout ins =>
        ins.nopeNotDef inBout
end


-- ## Section: The main result of the file

def uniSetMapAt_le_ins {dl n fv expr p}
  (ins:
    uniSetMapDl.Ins
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  uniSetMapAt_le_ins_helper ins rfl rfl

def uniSetMapAt_le_out {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  uniSetMapAt_le_out_helper out rfl rfl

def uniSetMapAt_le
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  uniSetMapAt dl n fv expr ⊑ expr.triIntp fv (dl.prefix n).wfm
:= {
  defLe _ := uniSetMapAt_le_ins ∘ DefList.Ins.isComplete
  posLe _ :=
    Function.mtr (uniSetMapAt_le_out ∘ DefList.Out.isComplete)
}
