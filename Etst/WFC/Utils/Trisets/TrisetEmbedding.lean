/-
  The embedding map used by the `Triset → TrisetPair` and
  `Triset → TrisetFn` embeddings.
  
  A `TrisetPair` (or `TrisetFn`) triset is coded by `(0, i)` where `i`
  is an index of `uniSetMap`, while a `Triset` element is coded by `i`
  directly. To embed the latter into the former, each triset `t` must
  be mapped to a triset `embed t` whose members are the codes
  `(0, embed e)` of the embedded members of `t`:
  
      uniSetMap.call (embed t)
        =
      { (0, embed e) | e ∈ uniSetMap.call t }
  
  (lane-wise). This file defines such an `embed` within WFC.
-/

import Etst.WFC.Ch7_Polymorphism

namespace Etst


/-
  `embedStep` is the triset of tuples `(iFn, (t, (0, r)))` such that
  `e ∈ uniSetMap.call t` and `r = iFn.callEnc e` for some `e`.

  Intuitively, `(vals.embedStep.call iFn).call t` is the image of
  `uniSetMap.call t` under the map `e ↦ (0, iFn.callEnc e)`.
-/
pairDefList trisetEmbedHelpersDl extends opFixDl
  s3 embedStep :=
    Ex iFn t e,
      (uniSetMap t & e) then (iFn × t × 0 × callEnc iFn e)
pairDefList.


namespace TrisetEmbedding
  /--
    An index that denotes the `embedStep` triset (via the constant
    of its definition list).
  -/
  def embedStepIndex: Pair :=
    uniSetMapIndex
      trisetEmbedHelpersDl.toDefList
      trisetEmbedHelpersDl.size
      []
      (.const trisetEmbedHelpersDl.consts.embedStep)
  
end TrisetEmbedding


/-
  `embedOp` is the triset of pairs `(iFn, embedStepIndex.callEnc iFn)`,
  ie the function mapping an operator index to the index of the
  `embedStep`-image under that operator.
-/
pairDefList trisetEmbedDl extends trisetEmbedHelpersDl
  s3 embedOp :=
    Ex iFn, iFn × callEnc <[TrisetEmbedding.embedStepIndex.toExpr]> iFn
pairDefList.


namespace TrisetEmbedding
  /-- An index that denotes the `embedOp` triset. -/
  def embedOpIndex: Pair :=
    uniSetMapIndex
      trisetEmbedDl.toDefList
      trisetEmbedDl.size
      []
      (.const trisetEmbedDl.consts.embedOp)
  
end TrisetEmbedding


namespace trisetEmbedHelpersDl
  open SingleLaneExpr
  
  /-- The `uniSetMap` constant of this deflist denotes `uniSetMap`. -/
  def wfm_uniSetMap_eq:
    trisetEmbedHelpersDl.wfm consts.uniSetMap = uniSetMap
  :=
    Eq.symm <|
      (uniSetMapDl.extend_wfm_eq_of_lt
        opFixHelpersDl rfl rfl (by decide)).trans
        ((opFixHelpersDl.extend_wfm_eq_of_lt
          opFixDl rfl rfl (by decide)).trans
          (opFixDl.extend_wfm_eq_of_lt
            trisetEmbedHelpersDl rfl rfl (by decide)))
  
  /-- The `callEnc` constant of this deflist denotes `callEnc`. -/
  def wfm_callEnc_eq:
    trisetEmbedHelpersDl.wfm consts.callEnc = opFixDl.vals.callEnc
  :=
    (opFixDl.extend_wfm_eq_of_lt
      trisetEmbedHelpersDl rfl rfl (by decide)).symm
  
  /-
    If `e` is a member of `t`, then `(0, iFn.callEnc e)` is a
    member of the `embedStep`-image of `t` under `iFn`.
  -/
  def embedStep_ins_def {iFn t e: Pair}
    (ins: (uniSetMap.call t).defMem e)
  :
    ((vals.embedStep.call iFn).call t).defMem
      (.pair (.nat 0) (iFn.callEnc e))
  :=
    let inUsmWfm:
      (trisetEmbedHelpersDl.wfm consts.uniSetMap).defMem (.pair t e)
    :=
      wfm_uniSetMap_eq ▸ Set3.inCallElim (lane := .defLane) ins
    let inUsm:
      ((BasicExpr.const consts.uniSetMap).toLane .defLane).intp2
        [e, e, t, iFn]
        trisetEmbedHelpersDl.wfm
        trisetEmbedHelpersDl.wfm
        (.pair t e)
    :=
      inUsmWfm
    let inCallEncWfm:
      (trisetEmbedHelpersDl.wfm consts.callEnc).defMem
        (.pair iFn (.pair e (iFn.callEnc e)))
    :=
      wfm_callEnc_eq ▸ opFixDl.callEnc_ins iFn e
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .defLane).intp2
        [.pair e (iFn.callEnc e), iFn.callEnc e, e, t, iFn]
        trisetEmbedHelpersDl.wfm
        trisetEmbedHelpersDl.wfm
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
          (inProd (inNat 0)
            (inCall (pA := e) (pB := iFn.callEnc e)
              (inCall (pA := iFn) (pB := .pair e (iFn.callEnc e))
                inCallEnc
                (inVar rfl))
              (inVar rfl)))))
  
  /-
    The possible-membership variant of `embedStep_ins_def`.
  -/
  def embedStep_ins_pos {iFn t e: Pair}
    (ins: (uniSetMap.call t).posMem e)
  :
    ((vals.embedStep.call iFn).call t).posMem
      (.pair (.nat 0) (iFn.callEnc e))
  :=
    let inUsmWfm:
      (trisetEmbedHelpersDl.wfm consts.uniSetMap).posMem (.pair t e)
    :=
      wfm_uniSetMap_eq ▸ Set3.inCallElim (lane := .posLane) ins
    let inUsm:
      ((BasicExpr.const consts.uniSetMap).toLane .posLane).intp2
        [e, e, t, iFn]
        trisetEmbedHelpersDl.wfm
        trisetEmbedHelpersDl.wfm
        (.pair t e)
    :=
      inUsmWfm
    let inCallEncWfm:
      (trisetEmbedHelpersDl.wfm consts.callEnc).posMem
        (.pair iFn (.pair e (iFn.callEnc e)))
    :=
      wfm_callEnc_eq ▸ (opFixDl.callEnc_ins iFn e).toPos
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .posLane).intp2
        [.pair e (iFn.callEnc e), iFn.callEnc e, e, t, iFn]
        trisetEmbedHelpersDl.wfm
        trisetEmbedHelpersDl.wfm
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
          (inProd (inNat 0)
            (inCall (pA := e) (pB := iFn.callEnc e)
              (inCall (pA := iFn) (pB := .pair e (iFn.callEnc e))
                inCallEnc
                (inVar rfl))
              (inVar rfl)))))
  
  /-- Lane-polymorphic form of `embedStep_ins`. -/
  def embedStep_ins {iFn t e: Pair} {lane: Set3.Lane}
    (ins: (uniSetMap.call t).getLane lane e)
  :
    ((vals.embedStep.call iFn).call t).getLane lane
      (.pair (.nat 0) (iFn.callEnc e))
  :=
    match lane with
    | .defLane => embedStep_ins_def ins
    | .posLane => embedStep_ins_pos ins
  
  /-
    If `(0, r)` is a definitive member of the `embedStep`-image of
    `t` under `iFn`, then `r = iFn.callEnc e` for some definitive
    member `e` of `t`.
  -/
  def embedStep_elim_def {iFn t p: Pair}
    (ins: ((vals.embedStep.call iFn).call t).defMem p)
  :
    ∃ e,
      And
        ((uniSetMap.call t).defMem e)
        (p = .pair (.nat 0) (iFn.callEnc e))
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
    let ⟨pL, pR, pEq, inTag, inApp⟩ := inProdElimEx inRest2
    let pLEq: pL = .nat 0 := inNatElim inTag
    let pREq: pR = iFnA.callEnc eA :=
      let h1 :=
        inCallElimSingle inApp (intp2_var_eq_singleton rfl)
      let h2 :=
        inCallElimSingle h1 (intp2_var_eq_singleton rfl)
      let h2w:
        (trisetEmbedHelpersDl.wfm consts.callEnc).defMem
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
  
  /-- The possible-membership variant of `embedStep_elim_def`. -/
  def embedStep_elim_pos {iFn t p: Pair}
    (ins: ((vals.embedStep.call iFn).call t).posMem p)
  :
    ∃ e,
      (uniSetMap.call t).posMem e
        ∧
      p = .pair (.nat 0) (iFn.callEnc e)
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
    let ⟨pL, pR, pEq, inTag, inApp⟩ := inProdElimEx inRest2
    let pLEq: pL = .nat 0 := inNatElim inTag
    let pREq: pR = iFnA.callEnc eA :=
      let h1 :=
        inCallElimSingle inApp (intp2_var_eq_singleton rfl)
      let h2 :=
        inCallElimSingle h1 (intp2_var_eq_singleton rfl)
      let h2w:
        (trisetEmbedHelpersDl.wfm consts.callEnc).posMem
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
  
  /-- Lane-polymorphic form of `embedStep_elim`. -/
  def embedStep_elim {iFn t p: Pair} {lane: Set3.Lane}
    (ins: ((vals.embedStep.call iFn).call t).getLane lane p)
  :
    ∃ e,
      (uniSetMap.call t).getLane lane e
        ∧
      p = .pair (.nat 0) (iFn.callEnc e)
  :=
    match lane with
    | .defLane => embedStep_elim_def ins
    | .posLane => embedStep_elim_pos ins
  
  /-- The characteristic equation of `embedStep`. -/
  def embedStep_call_eq (iFn t: Pair):
    Eq
      ((vals.embedStep.call iFn).call t)
      (Set3.image
        (fun e => .pair (.nat 0) (iFn.callEnc e))
        (uniSetMap.call t))
  :=
    Set3.eq4
      (fun _ inp =>
        let ⟨e, hin, eq⟩ := embedStep_elim_def inp
        ⟨e, hin, eq.symm⟩)
      (fun _ ⟨_, hin, eq⟩ =>
        eq ▸ embedStep_ins_def hin)
      (fun _ inp =>
        let ⟨e, hin, eq⟩ := embedStep_elim_pos inp
        ⟨e, hin, eq.symm⟩)
      (fun _ ⟨_, hin, eq⟩ =>
        eq ▸ embedStep_ins_pos hin)
  
end trisetEmbedHelpersDl


namespace TrisetEmbedding
  /-- Calling `embedStepIndex` yields the `embedStep` triset. -/
  def embedStepIndex_call:
    uniSetMap.call embedStepIndex
      =
    trisetEmbedHelpersDl.vals.embedStep
  :=
    FiniteDefList.uniSetMapAt_eq
      trisetEmbedHelpersDl
      []
      (.const trisetEmbedHelpersDl.consts.embedStep)
  
end TrisetEmbedding


namespace trisetEmbedDl
  open SingleLaneExpr
  
  /-- The `callEnc` constant of this deflist denotes `callEnc`. -/
  def wfm_callEnc_eq:
    trisetEmbedDl.wfm consts.callEnc = opFixDl.vals.callEnc
  :=
    ((opFixDl.extend_wfm_eq_of_lt
        trisetEmbedHelpersDl rfl rfl (by decide)).trans
      (trisetEmbedHelpersDl.extend_wfm_eq_of_lt
        trisetEmbedDl rfl rfl (by decide))).symm
  
  /-- `embedOp` maps `iFn` to `embedStepIndex.callEnc iFn` (intro). -/
  def embedOp_ins_def {iFn: Pair}:
    (vals.embedOp.call iFn).defMem
      (TrisetEmbedding.embedStepIndex.callEnc iFn)
  :=
    let inCallEncWfm:
      (trisetEmbedDl.wfm consts.callEnc).defMem
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn)))
    :=
      wfm_callEnc_eq ▸
        opFixDl.callEnc_ins TrisetEmbedding.embedStepIndex iFn
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .defLane).intp2
        [.pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn),
         TrisetEmbedding.embedStepIndex.callEnc iFn,
         iFn]
        trisetEmbedDl.wfm
        trisetEmbedDl.wfm
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn)))
    :=
      inCallEncWfm
    Set3.inCall (lane := .defLane) <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl)
      (inCall
        (pA := iFn)
        (pB := TrisetEmbedding.embedStepIndex.callEnc iFn)
        (inCall
          (pA := TrisetEmbedding.embedStepIndex)
          (pB := .pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn))
          inCallEnc
          (inToExpr TrisetEmbedding.embedStepIndex))
        (inVar rfl))
  
  /-- The possible-membership variant of `embedOp_ins_def`. -/
  def embedOp_ins_pos {iFn: Pair}:
    (vals.embedOp.call iFn).posMem
      (TrisetEmbedding.embedStepIndex.callEnc iFn)
  :=
    let inCallEncWfm:
      (trisetEmbedDl.wfm consts.callEnc).posMem
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn)))
    :=
      wfm_callEnc_eq ▸
        (opFixDl.callEnc_ins TrisetEmbedding.embedStepIndex iFn).toPos
    let inCallEnc:
      ((BasicExpr.const consts.callEnc).toLane .posLane).intp2
        [.pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn),
         TrisetEmbedding.embedStepIndex.callEnc iFn,
         iFn]
        trisetEmbedDl.wfm
        trisetEmbedDl.wfm
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn)))
    :=
      inCallEncWfm
    Set3.inCall (lane := .posLane) <|
    DefList.InWfm.of_in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl)
      (inCall
        (pA := iFn)
        (pB := TrisetEmbedding.embedStepIndex.callEnc iFn)
        (inCall
          (pA := TrisetEmbedding.embedStepIndex)
          (pB := .pair iFn (TrisetEmbedding.embedStepIndex.callEnc iFn))
          inCallEnc
          (inToExpr TrisetEmbedding.embedStepIndex))
        (inVar rfl))
  
  /-- `embedOp` is functional (elim, definitive lane). -/
  def embedOp_elim_def {iFn s: Pair}
    (ins: (vals.embedOp.call iFn).defMem s)
  :
    s = TrisetEmbedding.embedStepIndex.callEnc iFn
  :=
    let ins := Set3.inCallElim (lane := .defLane) ins
    let ins := DefList.InWfm.in_def_no_fv (lane := .defLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨inIFnV, inApp⟩ := inProdElim ins
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let h1 := inCallElimSingle inApp (intp2_var_eq_singleton rfl)
    let h2 :=
      inCallElimSingle
        h1
        (intp2_toExpr_eq_singleton TrisetEmbedding.embedStepIndex)
    let h2w:
      (trisetEmbedDl.wfm consts.callEnc).defMem
        (.pair TrisetEmbedding.embedStepIndex (.pair iFnA s))
    :=
      h2
    let encEq :=
      opFixDl.callEnc_elim (wfm_callEnc_eq ▸ h2w).toPos
    iFnEq ▸ encEq.symm
  
  /-- `embedOp` is functional (elim, possible lane). -/
  def embedOp_elim_pos {iFn s: Pair}
    (ins: (vals.embedOp.call iFn).posMem s)
  :
    s = TrisetEmbedding.embedStepIndex.callEnc iFn
  :=
    let ins := Set3.inCallElim (lane := .posLane) ins
    let ins := DefList.InWfm.in_def_no_fv (lane := .posLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨inIFnV, inApp⟩ := inProdElim ins
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let h1 := inCallElimSingle inApp (intp2_var_eq_singleton rfl)
    let h2 :=
      inCallElimSingle
        h1
        (intp2_toExpr_eq_singleton TrisetEmbedding.embedStepIndex)
    let h2w:
      (trisetEmbedDl.wfm consts.callEnc).posMem
        (.pair TrisetEmbedding.embedStepIndex (.pair iFnA s))
    :=
      h2
    let encEq :=
      opFixDl.callEnc_elim (wfm_callEnc_eq ▸ h2w)
    iFnEq ▸ encEq.symm
  
  /-- `embedOp` denotes the function `callEnc embedStepIndex`. -/
  def embedOp_call_eq (iFn: Pair):
    Eq
      (vals.embedOp.call iFn)
      (Set3.just (TrisetEmbedding.embedStepIndex.callEnc iFn))
  :=
    Set3.eq4
      (fun _ din => embedOp_elim_def din)
      (fun _ din => din ▸ embedOp_ins_def)
      (fun _ din => embedOp_elim_pos din)
      (fun _ din => din ▸ embedOp_ins_pos)
  
end trisetEmbedDl


namespace TrisetEmbedding
  /-- Calling `embedOpIndex` yields the `embedOp` triset. -/
  def embedOpIndex_call:
    uniSetMap.call embedOpIndex = trisetEmbedDl.vals.embedOp
  :=
    FiniteDefList.uniSetMapAt_eq
      trisetEmbedDl
      []
      (.const trisetEmbedDl.consts.embedOp)
  
  def embedOpIndex_call_eq (iFn: Pair):
    Eq
      ((uniSetMap.call embedOpIndex).call iFn)
      (Set3.just (embedStepIndex.callEnc iFn))
  :=
    (congrArg (·.call iFn) embedOpIndex_call).trans
      (trisetEmbedDl.embedOp_call_eq iFn)
  
  /-- The fixed point of the embedding operator. -/
  def embedFixIndex: Pair := indexFixIndex embedOpIndex
  
  /-- The fixed point equation of `embedFixIndex`. -/
  def embedFixIndex_call_eq:
    uniSetMap.call embedFixIndex
      =
    uniSetMap.call (embedStepIndex.callEnc embedFixIndex)
  :=
    indexFixIndex_fix_of_fn
      embedOpIndex
      (fun x => embedStepIndex.callEnc x)
      embedOpIndex_call_eq
  
  /--
    The embedding map on triset indices: `embed t` is a triset whose
    members are the codes `(0, embed e)` of the embedded members of `t`.
  -/
  def embed (t: Pair): Pair := embedFixIndex.callEnc t
  
  /-- The characteristic equation of `embed`. -/
  def embed_call_eq (t: Pair):
    uniSetMap.call (embed t)
      =
    Set3.image (fun e => .pair (.nat 0) (embed e)) (uniSetMap.call t)
  :=
    (opFixDl.callEnc_correct embedFixIndex t).trans
      ((congrArg (·.call t) embedFixIndex_call_eq).trans
        ((congrArg
            (·.call t)
            (opFixDl.callEnc_correct embedStepIndex embedFixIndex)).trans
          ((congrArg
              (fun s => (s.call embedFixIndex).call t)
              embedStepIndex_call).trans
            (trisetEmbedHelpersDl.embedStep_call_eq embedFixIndex t))))
  
  /-- Definitive members of `t` embed to definitive members of
  `embed t`. -/
  def embed_ins {t e: Pair}
    (ins: (uniSetMap.call t).defMem e)
  :
    (uniSetMap.call (embed t)).defMem (.pair (.nat 0) (embed e))
  :=
    embed_call_eq t ▸ ⟨e, ins, rfl⟩
  
  /-- Possible members of `t` embed to possible members of
  `embed t`. -/
  def embed_inw {t e: Pair}
    (inw: (uniSetMap.call t).posMem e)
  :
    (uniSetMap.call (embed t)).posMem (.pair (.nat 0) (embed e))
  :=
    embed_call_eq t ▸ ⟨e, inw, rfl⟩
  
  /-- Definitive members of `embed t` are embeddings of definitive
  members of `t`. -/
  def embed_elim_def {t p: Pair}
    (mem: (uniSetMap.call (embed t)).defMem p)
  :
    ∃ e, (uniSetMap.call t).defMem e ∧ p = .pair (.nat 0) (embed e)
  :=
    let ⟨e, hin, heq⟩ := embed_call_eq t ▸ mem
    ⟨e, hin, heq.symm⟩
  
  /-- Possible members of `embed t` are embeddings of possible
  members of `t`. -/
  def embed_elim_pos {t p: Pair}
    (mem: (uniSetMap.call (embed t)).posMem p)
  :
    ∃ e, (uniSetMap.call t).posMem e ∧ p = .pair (.nat 0) (embed e)
  :=
    let ⟨e, hin, heq⟩ := embed_call_eq t ▸ mem
    ⟨e, hin, heq.symm⟩
  
end TrisetEmbedding
