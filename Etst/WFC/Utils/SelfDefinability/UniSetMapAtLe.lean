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

def exprGuardElimGuardUnary {i iEnc encRest fv0 fvRest b c p}
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
  (cinsSat: (∀ {d x}, d ∈ (c x).getLane lane → uniSetMapDl.Ins d x))
:
  (c uniSetMapDl.consts.uniSetMap).getLane
    lane
    (.pair (uniSetMapIndex dl n [] ((dl.prefix n).getDef x)) p)
:=
  let main ins :=
    let ⟨xEnc, ins⟩ := inArbUnElim ins
    let ⟨insExprGuard, ins⟩ := inIrElim ins
    let xEncEq := exprGuardElimGuardUnary insExprGuard
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
  (cinsSat: (∀ {d x}, d ∈ (c x).getLane lane → uniSetMapDl.Ins d x))
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
    let bodyEncEq := exprGuardElimGuardUnary insExprGuard
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
  (x: Nat)
  (p: Pair)
:
  Cause Pair
:= {
  contextIns dx :=
    let expr := (dl.prefix n).getDef x
    Or
      (And
        (dx.x = uniSetMapDl.consts.getNth)
        (dx.d = uniSetMapDl.getNthEnc dl n x))
      (And
        (dx.x = uniSetMapDl.consts.uniSetMap)
        (dx.d = .pair (uniSetMapIndex dl n [] expr) p))
  backgroundIns := {}
  backgroundOut := {}
}

def isWeakCauseConst {dl n fv x p}:
  IsWeakCause
    (causeConst dl n x p)
    (.pair (uniSetMapIndex dl n fv (.const x)) p)
    (uniSetMapDl.getDef uniSetMapDl.consts.uniSetMap)
:=
  fun isSat =>
    let insGetNth := isSat.contextInsHold (Or.inl ⟨rfl, rfl⟩)
    let ins := isSat.contextInsHold (Or.inr ⟨rfl, rfl⟩)
    isInMap (isAtConst ins insGetNth)


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
mutual
def uniSetMapAt_le_ins_helper {dl n fv index cst expr p}
  (ins: uniSetMapDl.Ins index cst)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  match ins with
  | .intro _ _ cause isCause cinsSat binsSat boutSat =>
    let isConsistent :=
      Cause.IsStronglySatisfiedByBackground.toIsConsistent {
        backgroundInsHold := DefList.Ins.isSound ∘ binsSat
        backgroundOutHold := DefList.Out.isSound ∘ boutSat
      }
    let ins := isCause isConsistent.leastValsApxAreSat
    let ⟨dlEnc, ins⟩ := inArbUnElim (indexEq ▸ cstEq ▸ ins)
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
  (out: uniSetMapDl.Out index cst)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  match out with
  | .intro cycle isEmpty inCycle =>
    match expr with
    | .const x =>
      if h: x < n then
        let everyCauseInapp := isEmpty (indexEq ▸ cstEq ▸ inCycle)
        let isInapp := everyCauseInapp _ isWeakCauseConst
        match isInapp with
        | .blockedContextIns (d:=dd) (x:=xx) _ inCins inCycle =>
          let out := DefList.Out.intro cycle isEmpty inCycle
          match inCins with
          | Or.inl ⟨xEq, dEq⟩ =>
            let xEq: xx = _ := xEq
            let dEq: dd = _ := dEq
            let insGetNth :=
              uniSetMapDl.getNthDl (lane:=.posLane) (fv:=[]) h
            False.elim (out.isSound (xEq ▸ dEq ▸ insGetNth))
          | Or.inr ⟨xEq, dEq⟩ =>
            let xEq: xx = _ := xEq
            let dEq: dd = _ := dEq
            -- This is not the right approach. I would need to
            -- "recurse" on the cycle, but the cycle is, ehm,
            -- circular, so such recursion would not be terminating.
            -- What I need to do is to transform `out` into another
            -- `Out` instance and call isSound on that.
            -- 
            -- The main reason for this comment:
            -- I wonder if this approach would work if Out was
            -- a coinductive type. In fact, `Out` does look like
            -- it's "naturally coinductive" to my eyes. But it's
            -- also mutually defined with `Ins`, which is decidedly
            -- inductive, wonder if that causes any issues. Do
            -- investigate this some time.
            sorry
      else show
        Not
          ((((dl.prefix n).wfm) x).posMem p)
      from
        -- dl.prefix_none_at h ▸
        sorry
    | _ => sorry
end


-- ## Section: Putting it all together

def uniSetMapAt_le_out {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      (.pair (uniSetMapIndex dl n fv expr) p)
      uniSetMapDl.consts.uniSetMap)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  uniSetMapAt_le_out_helper out rfl rfl

def uniSetMapAt_le_ins {dl n fv expr p}
  (ins:
    uniSetMapDl.Ins
      (.pair (uniSetMapIndex dl n fv expr) p)
      uniSetMapDl.consts.uniSetMap)
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  uniSetMapAt_le_ins_helper ins rfl rfl

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
