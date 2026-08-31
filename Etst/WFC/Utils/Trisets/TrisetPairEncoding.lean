/-
  The re-encoding map used by the `Triset → TrisetPair` embedding.

  A `TrisetPair` triset (see TrisetPair.lean) contains *encodings*
  of TrisetPairs, while a `Triset` (BisimQuotient.lean) contains
  raw pairs. To embed the latter into the former, each triset `t`
  must be mapped to a triset `g t` whose members are the encodings
  `(1, g e)` of the re-encoded members of `t`:

      uniSetMap.call (g t) = { (1, g e) | e ∈ uniSetMap.call t }

  (lane-wise). This file defines such a `g` within WFC, using the
  same diagonalization machinery as `trisetFixIndex` in
  Ch7_Polymorphism.lean:

  - `encStep` is a function-triset mapping an operator index `iFn`
    to the triset of pairs `(t, (1, callEnc iFn e))` with
    `e ∈ uniSetMap.call t`;
  - `encOp` maps `iFn` to the index `callEnc encStepIndex iFn`;
  - `gFix := indexFixIndex encOpIndex` is then a fixed point:
    `uniSetMap.call gFix = (uniSetMap.call encStepIndex).call gFix`;
  - `g t := gFix.callEnc t` satisfies the equation above.
-/

import Etst.WFC.Ch7_Polymorphism

namespace Etst


/-
  `encStep` is the triset of tuples `(iFn, (t, (1, r)))` such that
  `e ∈ uniSetMap.call t` and `r = iFn.callEnc e` for some `e`.

  Intuitively, `(vals.encStep.call iFn).call t` is the image of
  `uniSetMap.call t` under the map `e ↦ (1, iFn.callEnc e)`.
-/
pairDefList trisetPairEncHelpersDl extends opFixDl
  s3 encStep :=
    Ex iFn t e,
      (uniSetMap t & e) then (iFn × t × 1 × callEnc iFn e)
pairDefList.


namespace Pair
  /--
    An index that denotes the `encStep` triset (via the constant
    of its definition list).
  -/
  def encStepIndex: Pair :=
    uniSetMapIndex
      trisetPairEncHelpersDl.toDefList
      trisetPairEncHelpersDl.size
      []
      (.const trisetPairEncHelpersDl.consts.encStep)
  
end Pair


/-
  `encOp` is the triset of pairs `(iFn, encStepIndex.callEnc iFn)`,
  ie the function mapping an operator index to the index of the
  `encStep`-image under that operator.
-/
set_option maxRecDepth 8192 in
pairDefList trisetPairEncDl extends trisetPairEncHelpersDl
  s3 encOp :=
    Ex iFn, iFn × callEnc <[Pair.encStepIndex.toExpr]> iFn
pairDefList.


namespace Pair
  /-- An index that denotes the `encOp` triset. -/
  def encOpIndex: Pair :=
    uniSetMapIndex
      trisetPairEncDl.toDefList
      trisetPairEncDl.size
      []
      (.const trisetPairEncDl.consts.encOp)
  
end Pair


/-- The pointwise image of a triset under a function. -/
def Set3.image (f: Pair → Pair) (s: Set3 Pair): Set3 Pair where
  defMem := f '' s.defMem
  posMem := f '' s.posMem
  defLePos := fun _ ⟨x, hx, eq⟩ => ⟨x, hx.toPos, eq⟩


namespace trisetPairEncHelpersDl
  open SingleLaneExpr
  
  /-- The `uniSetMap` constant of this deflist denotes `uniSetMap`. -/
  def wfm_uniSetMap_eq:
    trisetPairEncHelpersDl.wfm consts.uniSetMap = uniSetMap
  :=
    Eq.symm <|
      (uniSetMapDl.extend_wfm_eq_of_lt
        opFixHelpersDl rfl rfl (by decide)).trans
        ((opFixHelpersDl.extend_wfm_eq_of_lt
          opFixDl rfl rfl (by decide)).trans
          (opFixDl.extend_wfm_eq_of_lt
            trisetPairEncHelpersDl rfl rfl (by decide)))
  
  /-- The `callEnc` constant of this deflist denotes `callEnc`. -/
  def wfm_callEnc_eq:
    trisetPairEncHelpersDl.wfm consts.callEnc = opFixDl.vals.callEnc
  :=
    (opFixDl.extend_wfm_eq_of_lt
      trisetPairEncHelpersDl rfl rfl (by decide)).symm
  
  /-
    If `e` is a member of `t`, then `(1, iFn.callEnc e)` is a
    member of the `encStep`-image of `t` under `iFn`.
  -/
  def encStep_ins_def {iFn t e: Pair}
    (ins: (uniSetMap.call t).defMem e)
  :
    ((vals.encStep.call iFn).call t).defMem
      (.pair (.nat 1) (iFn.callEnc e))
  :=
    let inUsmWfm:
      (trisetPairEncHelpersDl.wfm consts.uniSetMap).defMem (.pair t e)
    :=
      wfm_uniSetMap_eq ▸ Set3.inCallElim (lane := .defLane) ins
    let inUsm:
      ((BasicExpr.const consts.uniSetMap).toLane .defLane).intp2
        [e, e, t, iFn]
        trisetPairEncHelpersDl.wfm
        trisetPairEncHelpersDl.wfm
        (.pair t e)
    :=
      inUsmWfm
    let inCallEncWfm:
      (trisetPairEncHelpersDl.wfm consts.callEnc).defMem
        (.pair iFn (.pair e (iFn.callEnc e)))
    :=
      wfm_callEnc_eq ▸ opFixDl.callEnc_ins iFn e
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .defLane).intp2
        [.pair e (iFn.callEnc e), iFn.callEnc e, e, t, iFn]
        trisetPairEncHelpersDl.wfm
        trisetPairEncHelpersDl.wfm
        (.pair iFn (.pair e (iFn.callEnc e)))
    :=
      inCallEncWfm
    Set3.inCall (lane := .defLane) <| Set3.inCall (lane := .defLane) <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <| inArbUn t <| inArbUn e <|
    inIfThen
      (inIr
        (inCall (pA := t) (pB := e) inUsm (inVar rfl))
        (inVar rfl))
      (inProd (inVar rfl)
        (inProd (inVar rfl)
          (inProd (inNat 1)
            (inCall (pA := e) (pB := iFn.callEnc e)
              (inCall (pA := iFn) (pB := .pair e (iFn.callEnc e))
                inCallEnc
                (inVar rfl))
              (inVar rfl)))))
  
  /-
    The possible-membership variant of `encStep_ins_def`.
  -/
  def encStep_ins_pos {iFn t e: Pair}
    (ins: (uniSetMap.call t).posMem e)
  :
    ((vals.encStep.call iFn).call t).posMem
      (.pair (.nat 1) (iFn.callEnc e))
  :=
    let inUsmWfm:
      (trisetPairEncHelpersDl.wfm consts.uniSetMap).posMem (.pair t e)
    :=
      wfm_uniSetMap_eq ▸ Set3.inCallElim (lane := .posLane) ins
    let inUsm:
      ((BasicExpr.const consts.uniSetMap).toLane .posLane).intp2
        [e, e, t, iFn]
        trisetPairEncHelpersDl.wfm
        trisetPairEncHelpersDl.wfm
        (.pair t e)
    :=
      inUsmWfm
    let inCallEncWfm:
      (trisetPairEncHelpersDl.wfm consts.callEnc).posMem
        (.pair iFn (.pair e (iFn.callEnc e)))
    :=
      wfm_callEnc_eq ▸ (opFixDl.callEnc_ins iFn e).toPos
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .posLane).intp2
        [.pair e (iFn.callEnc e), iFn.callEnc e, e, t, iFn]
        trisetPairEncHelpersDl.wfm
        trisetPairEncHelpersDl.wfm
        (.pair iFn (.pair e (iFn.callEnc e)))
    :=
      inCallEncWfm
    Set3.inCall (lane := .posLane) <| Set3.inCall (lane := .posLane) <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <| inArbUn t <| inArbUn e <|
    inIfThen
      (inIr
        (inCall (pA := t) (pB := e) inUsm (inVar rfl))
        (inVar rfl))
      (inProd (inVar rfl)
        (inProd (inVar rfl)
          (inProd (inNat 1)
            (inCall (pA := e) (pB := iFn.callEnc e)
              (inCall (pA := iFn) (pB := .pair e (iFn.callEnc e))
                inCallEnc
                (inVar rfl))
              (inVar rfl)))))
  
  /-- Lane-polymorphic form of `encStep_ins`. -/
  def encStep_ins {iFn t e: Pair} {lane: Set3.Lane}
    (ins: (uniSetMap.call t).getLane lane e)
  :
    ((vals.encStep.call iFn).call t).getLane lane
      (.pair (.nat 1) (iFn.callEnc e))
  :=
    match lane with
    | .defLane => encStep_ins_def ins
    | .posLane => encStep_ins_pos ins
  
  /-
    If `(1, r)` is a definitive member of the `encStep`-image of
    `t` under `iFn`, then `r = iFn.callEnc e` for some definitive
    member `e` of `t`.
  -/
  def encStep_elim_def {iFn t p: Pair}
    (ins: ((vals.encStep.call iFn).call t).defMem p)
  :
    ∃ e,
      (uniSetMap.call t).defMem e
        ∧
      p = .pair (.nat 1) (iFn.callEnc e)
  :=
    let ins :=
      Set3.inCallElim (lane := .defLane)
        (Set3.inCallElim (lane := .defLane) ins)
    let ins := DefList.InWfm.in_def_no_fv (lane := .defLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨tA, ins⟩ := inArbUnElim ins
    let ⟨eA, ins⟩ := inArbUnElim ins
    let ⟨⟨pC, inCond⟩, inOut⟩ := inIfThenElim ins
    let ⟨inIFnV, inRest⟩ := inProdElim inOut
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let ⟨inTV, inRest2⟩ := inProdElim inRest
    let tEq: t = tA := inVarElim inTV rfl
    let ⟨pL, pR, pEq, inNat1, inApp⟩ := inProdElimEx inRest2
    let pLEq: pL = .nat 1 := inNatElim inNat1
    let pREq: pR = iFnA.callEnc eA :=
      let h1 :=
        inCallElimSingle inApp (intp2_var_eq_singleton rfl)
      let h2 :=
        inCallElimSingle h1 (intp2_var_eq_singleton rfl)
      let h2w:
        (trisetPairEncHelpersDl.wfm consts.callEnc).defMem
          (.pair iFnA (.pair eA pR))
      :=
        h2
      let h3: (opFixDl.vals.callEnc).posMem (.pair iFnA (.pair eA pR)) :=
        (wfm_callEnc_eq ▸ h2w).toPos
      (opFixDl.callEnc_elim h3).symm
    let ⟨inCallPart, inVarPart⟩ := inIrElim inCond
    let pCEq: pC = eA := inVarElim inVarPart rfl
    let inUsmConst :=
      inCallElimSingle inCallPart (intp2_var_eq_singleton rfl)
    let inUsmWfm: uniSetMap.defMem (.pair tA pC) :=
      wfm_uniSetMap_eq ▸ inUsmConst
    let inUsmCall: (uniSetMap.call tA).defMem eA :=
      pCEq ▸ Set3.inCall (lane := .defLane) inUsmWfm
    ⟨eA, tEq ▸ inUsmCall, by
      rw [pEq, pLEq, pREq, ←iFnEq]⟩
  
  /-- The possible-membership variant of `encStep_elim_def`. -/
  def encStep_elim_pos {iFn t p: Pair}
    (ins: ((vals.encStep.call iFn).call t).posMem p)
  :
    ∃ e,
      (uniSetMap.call t).posMem e
        ∧
      p = .pair (.nat 1) (iFn.callEnc e)
  :=
    let ins :=
      Set3.inCallElim (lane := .posLane)
        (Set3.inCallElim (lane := .posLane) ins)
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨tA, ins⟩ := inArbUnElim ins
    let ⟨eA, ins⟩ := inArbUnElim ins
    let ⟨⟨pC, inCond⟩, inOut⟩ := inIfThenElim ins
    let ⟨inIFnV, inRest⟩ := inProdElim inOut
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let ⟨inTV, inRest2⟩ := inProdElim inRest
    let tEq: t = tA := inVarElim inTV rfl
    let ⟨pL, pR, pEq, inNat1, inApp⟩ := inProdElimEx inRest2
    let pLEq: pL = .nat 1 := inNatElim inNat1
    let pREq: pR = iFnA.callEnc eA :=
      let h1 :=
        inCallElimSingle inApp (intp2_var_eq_singleton rfl)
      let h2 :=
        inCallElimSingle h1 (intp2_var_eq_singleton rfl)
      let h2w:
        (trisetPairEncHelpersDl.wfm consts.callEnc).posMem
          (.pair iFnA (.pair eA pR))
      :=
        h2
      let h3: (opFixDl.vals.callEnc).posMem (.pair iFnA (.pair eA pR)) :=
        (wfm_callEnc_eq ▸ h2w)
      (opFixDl.callEnc_elim h3).symm
    let ⟨inCallPart, inVarPart⟩ := inIrElim inCond
    let pCEq: pC = eA := inVarElim inVarPart rfl
    let inUsmConst :=
      inCallElimSingle inCallPart (intp2_var_eq_singleton rfl)
    let inUsmWfm: uniSetMap.posMem (.pair tA pC) :=
      wfm_uniSetMap_eq ▸ inUsmConst
    let inUsmCall: (uniSetMap.call tA).posMem eA :=
      pCEq ▸ Set3.inCall (lane := .posLane) inUsmWfm
    ⟨eA, tEq ▸ inUsmCall, by
      rw [pEq, pLEq, pREq, ←iFnEq]⟩
  
  /-- Lane-polymorphic form of `encStep_elim`. -/
  def encStep_elim {iFn t p: Pair} {lane: Set3.Lane}
    (ins: ((vals.encStep.call iFn).call t).getLane lane p)
  :
    ∃ e,
      (uniSetMap.call t).getLane lane e
        ∧
      p = .pair (.nat 1) (iFn.callEnc e)
  :=
    match lane with
    | .defLane => encStep_elim_def ins
    | .posLane => encStep_elim_pos ins
  
  /-- The characteristic equation of `encStep`. -/
  def encStep_call_eq (iFn t: Pair):
    Eq
      ((vals.encStep.call iFn).call t)
      (Set3.image
        (fun e => .pair (.nat 1) (iFn.callEnc e))
        (uniSetMap.call t))
  :=
    Set3.eq4
      (fun _ inp =>
        let ⟨e, hin, eq⟩ := encStep_elim_def inp
        ⟨e, hin, eq.symm⟩)
      (fun _ ⟨_, hin, eq⟩ =>
        eq ▸ encStep_ins_def hin)
      (fun _ inp =>
        let ⟨e, hin, eq⟩ := encStep_elim_pos inp
        ⟨e, hin, eq.symm⟩)
      (fun _ ⟨_, hin, eq⟩ =>
        eq ▸ encStep_ins_pos hin)
  
end trisetPairEncHelpersDl


namespace Pair
  /-- Calling `encStepIndex` yields the `encStep` triset. -/
  def encStepIndex_call:
    uniSetMap.call encStepIndex
      =
    trisetPairEncHelpersDl.vals.encStep
  :=
    FiniteDefList.uniSetMapAt_eq
      trisetPairEncHelpersDl
      []
      (.const trisetPairEncHelpersDl.consts.encStep)
  
end Pair


namespace trisetPairEncDl
  open SingleLaneExpr
  
  /-- The `callEnc` constant of this deflist denotes `callEnc`. -/
  def wfm_callEnc_eq:
    trisetPairEncDl.wfm consts.callEnc = opFixDl.vals.callEnc
  :=
    ((opFixDl.extend_wfm_eq_of_lt
        trisetPairEncHelpersDl rfl rfl (by decide)).trans
      (trisetPairEncHelpersDl.extend_wfm_eq_of_lt
        trisetPairEncDl rfl rfl (by decide))).symm
  
  /-- `encOp` maps `iFn` to `encStepIndex.callEnc iFn` (intro). -/
  def encOp_ins_def {iFn: Pair}:
    (vals.encOp.call iFn).defMem (Pair.encStepIndex.callEnc iFn)
  :=
    let inCallEncWfm:
      (trisetPairEncDl.wfm consts.callEnc).defMem
        (.pair Pair.encStepIndex
          (.pair iFn (Pair.encStepIndex.callEnc iFn)))
    :=
      wfm_callEnc_eq ▸ opFixDl.callEnc_ins Pair.encStepIndex iFn
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .defLane).intp2
        [.pair iFn (Pair.encStepIndex.callEnc iFn),
         Pair.encStepIndex.callEnc iFn,
         iFn]
        trisetPairEncDl.wfm
        trisetPairEncDl.wfm
        (.pair Pair.encStepIndex
          (.pair iFn (Pair.encStepIndex.callEnc iFn)))
    :=
      inCallEncWfm
    Set3.inCall (lane := .defLane) <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl)
      (inCall (pA := iFn) (pB := Pair.encStepIndex.callEnc iFn)
        (inCall
          (pA := Pair.encStepIndex)
          (pB := .pair iFn (Pair.encStepIndex.callEnc iFn))
          inCallEnc
          (inToExpr Pair.encStepIndex))
        (inVar rfl))
  
  /-- The possible-membership variant of `encOp_ins_def`. -/
  def encOp_ins_pos {iFn: Pair}:
    (vals.encOp.call iFn).posMem (Pair.encStepIndex.callEnc iFn)
  :=
    let inCallEncWfm:
      (trisetPairEncDl.wfm consts.callEnc).posMem
        (.pair Pair.encStepIndex
          (.pair iFn (Pair.encStepIndex.callEnc iFn)))
    :=
      wfm_callEnc_eq ▸ (opFixDl.callEnc_ins Pair.encStepIndex iFn).toPos
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .posLane).intp2
        [.pair iFn (Pair.encStepIndex.callEnc iFn),
         Pair.encStepIndex.callEnc iFn,
         iFn]
        trisetPairEncDl.wfm
        trisetPairEncDl.wfm
        (.pair Pair.encStepIndex
          (.pair iFn (Pair.encStepIndex.callEnc iFn)))
    :=
      inCallEncWfm
    Set3.inCall (lane := .posLane) <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl)
      (inCall (pA := iFn) (pB := Pair.encStepIndex.callEnc iFn)
        (inCall
          (pA := Pair.encStepIndex)
          (pB := .pair iFn (Pair.encStepIndex.callEnc iFn))
          inCallEnc
          (inToExpr Pair.encStepIndex))
        (inVar rfl))
  
  /-- `encOp` is functional (elim, definitive lane). -/
  def encOp_elim_def {iFn s: Pair}
    (ins: (vals.encOp.call iFn).defMem s)
  :
    s = Pair.encStepIndex.callEnc iFn
  :=
    let ins := Set3.inCallElim (lane := .defLane) ins
    let ins := DefList.InWfm.in_def_no_fv (lane := .defLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨inIFnV, inApp⟩ := inProdElim ins
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let h1 := inCallElimSingle inApp (intp2_var_eq_singleton rfl)
    let h2 :=
      inCallElimSingle h1 (intp2_toExpr_eq_singleton Pair.encStepIndex)
    let h2w:
      (trisetPairEncDl.wfm consts.callEnc).defMem
        (.pair Pair.encStepIndex (.pair iFnA s))
    :=
      h2
    let encEq :=
      opFixDl.callEnc_elim (wfm_callEnc_eq ▸ h2w).toPos
    iFnEq ▸ encEq.symm
  
  /-- `encOp` is functional (elim, possible lane). -/
  def encOp_elim_pos {iFn s: Pair}
    (ins: (vals.encOp.call iFn).posMem s)
  :
    s = Pair.encStepIndex.callEnc iFn
  :=
    let ins := Set3.inCallElim (lane := .posLane) ins
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨inIFnV, inApp⟩ := inProdElim ins
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let h1 := inCallElimSingle inApp (intp2_var_eq_singleton rfl)
    let h2 :=
      inCallElimSingle h1 (intp2_toExpr_eq_singleton Pair.encStepIndex)
    let h2w:
      (trisetPairEncDl.wfm consts.callEnc).posMem
        (.pair Pair.encStepIndex (.pair iFnA s))
    :=
      h2
    let encEq :=
      opFixDl.callEnc_elim (wfm_callEnc_eq ▸ h2w)
    iFnEq ▸ encEq.symm
  
  /-- `encOp` denotes the function `callEnc encStepIndex`. -/
  def encOp_call_eq (iFn: Pair):
    Eq
      (vals.encOp.call iFn)
      (Set3.just (Pair.encStepIndex.callEnc iFn))
  :=
    Set3.eq4
      (fun _ din => encOp_elim_def din)
      (fun _ din => din ▸ encOp_ins_def)
      (fun _ din => encOp_elim_pos din)
      (fun _ din => din ▸ encOp_ins_pos)
  
end trisetPairEncDl


namespace Pair
  /-- Calling `encOpIndex` yields the `encOp` triset. -/
  def encOpIndex_call:
    uniSetMap.call encOpIndex = trisetPairEncDl.vals.encOp
  :=
    FiniteDefList.uniSetMapAt_eq
      trisetPairEncDl
      []
      (.const trisetPairEncDl.consts.encOp)
  
  def encOpIndex_call_eq (iFn: Pair):
    Eq
      ((uniSetMap.call encOpIndex).call iFn)
      (Set3.just (encStepIndex.callEnc iFn))
  :=
    (congrArg (·.call iFn) encOpIndex_call).trans
      (trisetPairEncDl.encOp_call_eq iFn)
  
  /-- The fixed point of the re-encoding operator. -/
  def gFix: Pair := indexFixIndex encOpIndex
  
  /-- The fixed point equation of `gFix`. -/
  def gFix_call_eq:
    uniSetMap.call gFix
      =
    uniSetMap.call (encStepIndex.callEnc gFix)
  :=
    indexFixIndex_fix_of_fn
      encOpIndex
      (fun x => encStepIndex.callEnc x)
      encOpIndex_call_eq
  
  /--
    The re-encoding map on triset indices: `g t` is a triset
    whose members are the encodings `(1, g e)` of the re-encoded
    members of `t`.
  -/
  def g (t: Pair): Pair := gFix.callEnc t
  
  /-- The characteristic equation of `g`. -/
  def g_call_eq (t: Pair):
    uniSetMap.call (g t)
      =
    Set3.image (fun e => .pair (.nat 1) (g e)) (uniSetMap.call t)
  :=
    (opFixDl.callEnc_correct gFix t).trans
      ((congrArg (·.call t) gFix_call_eq).trans
        ((congrArg
            (·.call t)
            (opFixDl.callEnc_correct encStepIndex gFix)).trans
          ((congrArg
              (fun s => (s.call gFix).call t)
              encStepIndex_call).trans
            (trisetPairEncHelpersDl.encStep_call_eq gFix t))))
  
  /-- Definitive members of `t` encode to definitive members of
  `g t`. -/
  def g_ins {t e: Pair}
    (ins: (uniSetMap.call t).defMem e)
  :
    (uniSetMap.call (g t)).defMem (.pair (.nat 1) (g e))
  :=
    g_call_eq t ▸ ⟨e, ins, rfl⟩
  
  /-- Possible members of `t` encode to possible members of
  `g t`. -/
  def g_inw {t e: Pair}
    (inw: (uniSetMap.call t).posMem e)
  :
    (uniSetMap.call (g t)).posMem (.pair (.nat 1) (g e))
  :=
    g_call_eq t ▸ ⟨e, inw, rfl⟩
  
  /-- Definitive members of `g t` are encodings of definitive
  members of `t`. -/
  def g_elim_def {t p: Pair}
    (mem: (uniSetMap.call (g t)).defMem p)
  :
    ∃ e, (uniSetMap.call t).defMem e ∧ p = .pair (.nat 1) (g e)
  :=
    let ⟨e, hin, heq⟩ := g_call_eq t ▸ mem
    ⟨e, hin, heq.symm⟩
  
  /-- Possible members of `g t` are encodings of possible members
  of `t`. -/
  def g_elim_pos {t p: Pair}
    (mem: (uniSetMap.call (g t)).posMem p)
  :
    ∃ e, (uniSetMap.call t).posMem e ∧ p = .pair (.nat 1) (g e)
  :=
    let ⟨e, hin, heq⟩ := g_call_eq t ▸ mem
    ⟨e, hin, heq.symm⟩
  
end Pair
