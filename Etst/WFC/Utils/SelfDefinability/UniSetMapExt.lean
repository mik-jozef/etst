/-
  Correctness of the two extra expression encodings supported by
  `uniSetMap` (see the comment in `UniSetMapDl.lean`):

  * `(12, null)` denotes the triset `uniSetMap` itself, and
  * `(13, b)` denotes the singleton triset `{ b.toExpr.encoding }`.

  Unlike the "proper" expression encodings, these do not correspond to
  any `BasicExpr`, so the theorems below are stated in terms of the
  pair-based `uniSetMapIndexEnc` instead of `uniSetMapIndex`.
-/
module
public import Etst.WFC.Utils.SelfDefinability.UniSetMapHelpers

public section
namespace Etst.uniSetMapDl
open SingleLaneExpr
open uniSetMapDl

/-
  ## The `(12, null)` encoding
-/

theorem uniSetMapEnc_ins {p lane dl n fv}
  (ins: p ∈ uniSetMap.getLane lane)
:
  p ∈ (uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 12) .null))).getLane lane
:=
  let ins:
    p ∈ ((uniSetMapDl.dl.wfm (cst "uniSetMap")).getLane lane)
  := ins
  let isAt :=
    isAtUniSetMap
      (dl := dl) (n := n) (fv := fv)
      (b := uniSetMapDl.dl.wfm) (c := uniSetMapDl.dl.wfm)
      ins
  let inDef :=
    isInMapEnc
      (fvI := [])
      (b := uniSetMapDl.dl.wfm) (c := uniSetMapDl.dl.wfm)
      isAt
  Set3.inCall (DefList.InWfm.of_in_def_no_fv inDef)

theorem uniSetMapEnc_elim {p lane dl n fv}
  (ins:
    p ∈ (uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 12) .null))).getLane lane)
:
  p ∈ uniSetMap.getLane lane
:=
  let ins := Set3.inCallElim ins
  let ins := DefList.InWfm.in_def_no_fv ins
  let isAt:
    InUniSetMapAtEnc
      dl n fv
      uniSetMapDl.dl.wfm uniSetMapDl.dl.wfm
      (.pair (.nat 12) .null)
      lane p
  := isAtOfInsDefEnc ins
  exprEncListElim
    isAt
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
    (isAtArbUnNope · (by decide))
    (fun insList =>
      let ⟨_, inMap⟩ := inIrElim insList
      show p ∈ (uniSetMapDl.dl.wfm (cst "uniSetMap")).getLane lane from
      inToggle2Elim 13 inMap)
    (isAtToEncodingNope · (by decide))

theorem uniSetMapIndexEnc_uniSetMapEnc
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
:
  uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 12) .null)) = uniSetMap
:=
  Set3.eq4
    (fun p h => uniSetMapEnc_elim (p := p) (lane := .defLane) h)
    (fun p h => uniSetMapEnc_ins (p := p) (lane := .defLane) h)
    (fun p h => uniSetMapEnc_elim (p := p) (lane := .posLane) h)
    (fun p h => uniSetMapEnc_ins (p := p) (lane := .posLane) h)

/-
  ## The `(13, b)` encoding
-/

/-
  The `(13, b)` clause evaluates `b` while building the encoding of the
  expression it denotes, recursing through `uniSetMap` itself on the
  sub-pairs. `toEncodingNullElim` and `toEncodingPairElim` below are the
  two branches of that computation, read backwards.
-/

theorem toEncodingNullElim {dl n fv bm c lane p}
  (insList:
    p ∈ (exprEncToEncodingRaw.toLane (toggle2N lane 13)).intp
      (.pair (.nat 13) .null :: Pair.listEncoding fv
        :: DefList.prefixEncoding dl n :: []) bm c)
:
  p = .pair (.nat 4) .null
:=
  let ⟨pBound, insBody⟩ := inArbUnElim insList
  let ⟨inGuard, inBig⟩ := inIrElim insBody
  let ⟨_, inGuardBody⟩ := inSomeElim inGuard
  let ⟨inProd13, inExprVar⟩ := inIrElim inGuardBody
  let exprVarEq := inVarElim inExprVar rfl
  let ⟨_, inBVar⟩ := inProdElim (exprVarEq ▸ inProd13)
  let bEq: pBound = .null := (inVarElim inBVar rfl).symm
  match inUnElim inBig with
  | .inl inA =>
    let ⟨_, inRightA⟩ := inIrElim inA
    let ⟨_, _, pEq, in4, inNull⟩ := inProdElimEx inRightA
    pEq.trans (Pair.eq (inNatElim in4) (inNullElim inNull))
  | .inr inB =>
    let ⟨_, inB1⟩ := inArbUnElim inB
    let ⟨_, inB2⟩ := inArbUnElim inB1
    let ⟨inSomeB, _⟩ := inIrElim inB2
    let ⟨_, inSomeBody⟩ := inSomeElim inSomeB
    let ⟨inQVar, inProdLr⟩ := inIrElim inSomeBody
    let qEq := inVarElim inQVar rfl
    let ⟨_, _, pBoundEq, _, _⟩ := inProdElimEx (qEq ▸ inProdLr)
    Pair.noConfusion (bEq.symm.trans pBoundEq)

-- TODO improve perf
-- set_option maxHeartbeats 300000 in
theorem toEncodingPairElim {dl n fv lane l r p}
  (insList:
    p ∈ (exprEncToEncodingRaw.toLane (toggle2N lane 13)).intp
      (.pair (.nat 13) (.pair l r) :: Pair.listEncoding fv
        :: DefList.prefixEncoding dl n :: [])
      uniSetMapDl.dl.wfm uniSetMapDl.dl.wfm)
  (ihL:
    ∀ {ln q},
      q ∈ (uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 13) l))).getLane ln →
      q = l.toExpr.encoding)
  (ihR:
    ∀ {ln q},
      q ∈ (uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 13) r))).getLane ln →
      q = r.toExpr.encoding)
:
  p = .pair (.nat 5) (.pair l.toExpr.encoding r.toExpr.encoding)
:=
  let ⟨pBound, insBody⟩ := inArbUnElim insList
  let ⟨inGuard, inBig⟩ := inIrElim insBody
  let ⟨_, inGuardBody⟩ := inSomeElim inGuard
  let ⟨inProd13, inExprVar⟩ := inIrElim inGuardBody
  let exprVarEq := inVarElim inExprVar rfl
  let ⟨_, inBVar⟩ := inProdElim (exprVarEq ▸ inProd13)
  let bEq: pBound = .pair l r := (inVarElim inBVar rfl).symm
  match inUnElim inBig with
  | .inl inA =>
    let ⟨inSomeA, _⟩ := inIrElim inA
    let ⟨_, inABody⟩ := inSomeElim inSomeA
    let ⟨inBVar0, inNullVar⟩ := inIrElim inABody
    Pair.noConfusion ((inVarElim inBVar0 rfl).symm.trans (inNullElim inNullVar)
      |>.symm.trans bEq)
  | .inr inB =>
    let ⟨lVal, inB1⟩ := inArbUnElim inB
    let ⟨rVal, inB2⟩ := inArbUnElim inB1
    let ⟨inSomeB, inRightB⟩ := inIrElim inB2
    let ⟨_, inSomeBody⟩ := inSomeElim inSomeB
    let ⟨inQVar, inProdLr⟩ := inIrElim inSomeBody
    let qEq := inVarElim inQVar rfl
    let ⟨_, _, pBoundEq, inLVar, inRVar⟩ := inProdElimEx (qEq ▸ inProdLr)
    let lrEq := Pair.noConfusion (pBoundEq.symm.trans bEq) And.intro
    let lValEq: lVal = l :=
      (inVarElim inLVar rfl).symm.trans lrEq.left
    let rValEq: rVal = r :=
      (inVarElim inRVar rfl).symm.trans lrEq.right
    let ⟨_, _, pEq, in5, inQR⟩ := inProdElimEx inRightB
    let ⟨qL, qR, pQREq, inAppL, inAppR⟩ := inProdElimEx inQR
    let ⟨aFnL, inFnL, inArgL⟩ := inCallElim inAppL
    let ⟨_, _, aEq1, inDlVar, inRest1⟩ := inProdElimEx inArgL
    let ⟨_, _, aEq2, inFvVar, inRest2⟩ := inProdElimEx inRest1
    let ⟨_, _, aEq3, in13L, inLVar2⟩ := inProdElimEx inRest2
    let idxLEq: aFnL = uniSetMapIndexEnc dl n fv (.pair (.nat 13) lVal) :=
      aEq1.trans (Pair.eq (inVarElim inDlVar rfl)
        (aEq2.trans (Pair.eq (inVarElim inFvVar rfl)
          (aEq3.trans (Pair.eq (inNatElim in13L) (inVarElim inLVar2 rfl))))))
    let qLEq: qL = l.toExpr.encoding :=
      ihL (lValEq ▸ (idxLEq ▸ Set3.inCall inFnL))
    let ⟨aFnR, inFnR, inArgR⟩ := inCallElim inAppR
    let ⟨_, _, bEq1, inDlVar2, inRest3⟩ := inProdElimEx inArgR
    let ⟨_, _, bEq2, inFvVar2, inRest4⟩ := inProdElimEx inRest3
    let ⟨_, _, bEq3, in13R, inLVar3⟩ := inProdElimEx inRest4
    let idxREq: aFnR = uniSetMapIndexEnc dl n fv (.pair (.nat 13) rVal) :=
      bEq1.trans (Pair.eq (inVarElim inDlVar2 rfl)
        (bEq2.trans (Pair.eq (inVarElim inFvVar2 rfl)
          (bEq3.trans (Pair.eq (inNatElim in13R) (inVarElim inLVar3 rfl))))))
    let qREq: qR = r.toExpr.encoding :=
      ihR (rValEq ▸ (idxREq ▸ Set3.inCall inFnR))
    pEq.trans (pQREq ▸ Pair.eq (inNatElim in5) (Pair.eq qLEq qREq))

theorem toEncodingEnc_ins {dl n fv lane}:
  (b: Pair) →
    b.toExpr.encoding ∈
      (uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 13) b))).getLane lane
| .null =>
  Set3.inCall <|
  DefList.InWfm.of_in_def_no_fv <|
  isInMapEnc (fvI := []) <|
  isAtToEncodingNull
    (dl := dl) (n := n) (fv := fv)
    (b := uniSetMapDl.dl.wfm) (c := uniSetMapDl.dl.wfm) (lane := lane)
| .pair l r =>
  Set3.inCall <|
  DefList.InWfm.of_in_def_no_fv <|
  isInMapEnc (fvI := []) <|
  isAtToEncodingPair
    (dl := dl) (n := n) (fv := fv)
    (b := uniSetMapDl.dl.wfm) (c := uniSetMapDl.dl.wfm) (lane := lane)
    (Set3.inCallElim (toEncodingEnc_ins (dl := dl) (n := n) (fv := fv) (lane := lane) l))
    (Set3.inCallElim (toEncodingEnc_ins (dl := dl) (n := n) (fv := fv) (lane := lane) r))

theorem toEncodingEnc_elim {dl n fv lane}:
  (b: Pair) → ∀ {p},
    p ∈ (uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 13) b))).getLane lane →
    p = b.toExpr.encoding
| .null, p, ins =>
  let ins := Set3.inCallElim ins
  let ins := DefList.InWfm.in_def_no_fv ins
  let isAt:
    InUniSetMapAtEnc dl n fv
      uniSetMapDl.dl.wfm uniSetMapDl.dl.wfm
      (.pair (.nat 13) .null) lane p :=
    isAtOfInsDefEnc ins
  exprEncListElim
    isAt
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
    (isAtArbUnNope · (by decide))
    (isAtUniSetMapNope · (by decide))
    toEncodingNullElim
| .pair l r, p, ins =>
  let ins := Set3.inCallElim ins
  let ins := DefList.InWfm.in_def_no_fv ins
  let isAt:
    InUniSetMapAtEnc dl n fv
      uniSetMapDl.dl.wfm uniSetMapDl.dl.wfm
      (.pair (.nat 13) (.pair l r)) lane p :=
    isAtOfInsDefEnc ins
  exprEncListElim
    isAt
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
    (isAtArbUnNope · (by decide))
    (isAtUniSetMapNope · (by decide))
    (toEncodingPairElim
      (ihL := fun {ln} {q} h => toEncodingEnc_elim (lane := ln) l h)
      (ihR := fun {ln} {q} h => toEncodingEnc_elim (lane := ln) r h))

theorem uniSetMapIndexEnc_toEncodingEnc
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (b: Pair)
:
  uniSetMap.call (uniSetMapIndexEnc dl n fv (.pair (.nat 13) b)) =
    Set3.just b.toExpr.encoding
:=
  Set3.eq4
    (fun _ h => toEncodingEnc_elim (lane := .defLane) b h)
    (fun _ h => (Set3.just.inDefToEq h).symm ▸
      toEncodingEnc_ins (dl := dl) (n := n) (fv := fv) (lane := .defLane) b)
    (fun _ h => toEncodingEnc_elim (lane := .posLane) b h)
    (fun _ h => (Set3.just.inPosToEq h).symm ▸
      toEncodingEnc_ins (dl := dl) (n := n) (fv := fv) (lane := .posLane) b)

end Etst.uniSetMapDl
