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
module
public import Etst.WFC.Ch6_SelfDefinability
public import Etst.WFC.Ch7_Polymorphism
import Etst.BasicUtils

public section
namespace Etst


/-
  `embedStep` is the triset of tuples `(iFn, (t, (0, r)))` such that
  `e ∈ uniSetMap.call t` and `r = iFn.indexCall e` for some `e`.

  Intuitively, `embedStep iFn t` is the image of `uniSetMap t` under
  the map `e ↦ (0, iFn.indexCall e)`.
-/
exposed pairDefList trisetEmbedHelpersDl extends opFixDl
  p3 embedStep :=
    Ex iFn t e,
      (uniSetMap t & e) then (iFn × t × 0 × indexCall iFn e)
pairDefList.


namespace TrisetEmbedding
  /-
    An index that denotes the `embedStep` triset (via the constant
    of its definition list).
  -/
  exposed def embedStepIndex: Pair :=
    uniSetMapIndex
      trisetEmbedHelpersDl.dl.toDefList
      trisetEmbedHelpersDl.dl.size
      []
      (.const () (trisetEmbedHelpersDl.const "embedStep"))
  
end TrisetEmbedding


/-
  `embedOp` is the triset of pairs `(iFn, embedStepIndex.indexCall iFn)`,
  ie the function mapping an operator index to the index of the
  `embedStep`-image under that operator.
-/
exposed pairDefList trisetEmbedDl extends trisetEmbedHelpersDl
  p3 embedOp :=
    Ex iFn, iFn × indexCall <[TrisetEmbedding.embedStepIndex.toNamedExpr]> iFn
pairDefList.


namespace TrisetEmbedding
  /- An index that denotes the `embedOp` triset. -/
  exposed def embedOpIndex: Pair :=
    uniSetMapIndex
      trisetEmbedDl.dl.toDefList
      trisetEmbedDl.dl.size
      []
      (.const () (trisetEmbedDl.const "embedOp"))
  
end TrisetEmbedding


namespace trisetEmbedHelpersDl
  open Expr
  
  /-- The `uniSetMap` constant of this deflist denotes `uniSetMap`. -/
  theorem wfm_uniSetMap_eq:
    trisetEmbedHelpersDl.val "uniSetMap" = uniSetMap
  :=
    trisetEmbedHelpersDl.extend_wfm_eq uniSetMapDl "uniSetMap"
  
  /-- The `indexCall` constant of this deflist denotes `indexCall`. -/
  theorem wfm_indexCall_eq:
    trisetEmbedHelpersDl.val "indexCall" = opFixDl.val "indexCall"
  :=
    trisetEmbedHelpersDl.extend_wfm_eq opFixDl "indexCall"
  
  /-
    If `e` is a member of `t`, then `(0, iFn.indexCall e)` is a
    member of the `embedStep`-image of `t` under `iFn`.
  -/
  theorem embedStep_ins_def {iFn t e: Pair}
    (ins: e ∈ (uniSetMap.call t).defMem)
  :
    (((trisetEmbedHelpersDl.val "embedStep").call iFn).call t).defMem.Mem
      (.pair (.nat 0) (iFn.indexCall e))
  :=
    let inUsmWfm:
      .pair t e ∈ (trisetEmbedHelpersDl.val "uniSetMap").defMem
    :=
      wfm_uniSetMap_eq ▸ Set3.inCallElim (lane := .defLane) ins
    let inUsm:
      Set.Mem
        (Expr.intp
          (const .basic (trisetEmbedHelpersDl.const "uniSetMap"))
          .defLane
          trisetEmbedHelpersDl.dl.wfm
          trisetEmbedHelpersDl.dl.wfm
          [e, e, t, iFn])
        (.pair t e)
    :=
      inUsmWfm
    let inIndexCallWfm:
      (trisetEmbedHelpersDl.val "indexCall").defMem.Mem
        (.pair iFn (.pair e (iFn.indexCall e)))
    :=
      wfm_indexCall_eq ▸
        opFixDl.indexCall_ins (tag := ()) (lane := .defLane)
          iFn e
    let inIndexCall:
      Set.Mem
        (Expr.intp
          (const .basic (trisetEmbedHelpersDl.const "indexCall"))
          .defLane
          trisetEmbedHelpersDl.dl.wfm
          trisetEmbedHelpersDl.dl.wfm
          [.pair e (iFn.indexCall e), iFn.indexCall e, e, t, iFn])
        (.pair iFn (.pair e (iFn.indexCall e)))
    :=
      inIndexCallWfm
    Set3.inCall (lane := .defLane) <|
    Set3.inCall <|
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inArbUn t <|
    inArbUn e <|
    inIfThen
      (inIr
        (inCall (pA := t) (pB := e) inUsm (inVar rfl))
        (inVar rfl))
      (inProd (inVar rfl)
        (inProd (inVar rfl)
          (inProd (inNat 0)
            (inCall (pA := e) (pB := iFn.indexCall e)
              (inCall (pA := iFn) (pB := .pair e (iFn.indexCall e))
                inIndexCall
                (inVar rfl))
              (inVar rfl)))))
  
  /-
    The possible-membership variant of `embedStep_ins_def`.
  -/
  theorem embedStep_ins_pos {iFn t e: Pair}
    (ins: e ∈ (uniSetMap.call t).posMem)
  :
    (((trisetEmbedHelpersDl.val "embedStep").call iFn).call t).posMem.Mem
      (.pair (.nat 0) (iFn.indexCall e))
  :=
    let inUsmWfm:
      .pair t e ∈ (trisetEmbedHelpersDl.val "uniSetMap").posMem
    :=
      wfm_uniSetMap_eq ▸ Set3.inCallElim (lane := .posLane) ins
    let inUsm:
      Set.Mem
        ((Expr.const .basic
          (trisetEmbedHelpersDl.const "uniSetMap")).intp
          .posLane
          trisetEmbedHelpersDl.dl.wfm
          trisetEmbedHelpersDl.dl.wfm
          [e, e, t, iFn])
        (.pair t e)
    :=
      inUsmWfm
    let inIndexCallWfm:
      (trisetEmbedHelpersDl.val "indexCall").posMem.Mem
        (.pair iFn (.pair e (iFn.indexCall e)))
    :=
      wfm_indexCall_eq ▸
        Set3.defToPos
          (opFixDl.indexCall_ins (tag := ()) (lane := .defLane)
            iFn e)
    let inIndexCall:
      Set.Mem
        ((Expr.const .basic
          (trisetEmbedHelpersDl.const "indexCall")).intp
          .posLane
          trisetEmbedHelpersDl.dl.wfm
          trisetEmbedHelpersDl.dl.wfm
          [.pair e (iFn.indexCall e), iFn.indexCall e, e, t, iFn])
        (.pair iFn (.pair e (iFn.indexCall e)))
    :=
      inIndexCallWfm
    Set3.inCall (lane := .posLane) <|
    Set3.inCall <|
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inArbUn t <|
    inArbUn e <|
    inIfThen
      (inIr
        (inCall (pA := t) (pB := e) inUsm (inVar rfl))
        (inVar rfl))
      (inProd (inVar rfl)
        (inProd (inVar rfl)
          (inProd (inNat 0)
            (inCall
              (inCall
                inIndexCall
                (inVar rfl))
              (inVar rfl)))))
  
  /- Lane-polymorphic form of `embedStep_ins`. -/
  theorem embedStep_ins {iFn t e: Pair} {lane: Set3.Lane}
    (ins: e ∈ (uniSetMap.call t).getLane lane)
  :
    ((((trisetEmbedHelpersDl.val "embedStep").call iFn).call t).getLane lane).Mem
      (.pair (.nat 0) (iFn.indexCall e))
  :=
    match lane with
    | .defLane => embedStep_ins_def ins
    | .posLane => embedStep_ins_pos ins
  
  /-
    If `(0, r)` is a definitive member of the `embedStep`-image of
    `t` under `iFn`, then `r = iFn.indexCall e` for some definitive
    member `e` of `t`.
  -/
  theorem embedStep_elim_def {iFn t p: Pair}
    (ins: p ∈ (((trisetEmbedHelpersDl.val "embedStep").call iFn).call t).defMem)
  :
    ∃ e,
      And
        (e ∈ (uniSetMap.call t).defMem)
        (p = .pair (.nat 0) (iFn.indexCall e))
  :=
    let ins :=
      Set3.inCallElim (lane := .defLane)
        (Set3.inCallElim (lane := .defLane) ins)
    let ins := DefList.in_def_body_no_fv (lane := .defLane) ins
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
    let pREq: pR = iFnA.indexCall eA :=
      let h1 :=
        inCallElimSingle inApp (intp_var_eq_singleton rfl)
      let h2 :=
        inCallElimSingle h1 (intp_var_eq_singleton rfl)
      let h2w:
        (trisetEmbedHelpersDl.val "indexCall").defMem.Mem
          (.pair iFnA (.pair eA pR))
      :=
        h2
      let h3:
        .pair iFnA (.pair eA pR) ∈ (opFixDl.val "indexCall").posMem
      :=
        Set3.defToPos (wfm_indexCall_eq ▸ h2w)
      (opFixDl.indexCall_elim h3).symm
    let ⟨inCallPart, inVarPart⟩ := inIrElim inCond
    let pCEq: pC = eA := inVarElim inVarPart rfl
    let inUsmConst :=
      inCallElimSingle inCallPart (intp_var_eq_singleton rfl)
    let inUsmWfm: .pair tA pC ∈ uniSetMap.defMem :=
      wfm_uniSetMap_eq ▸ inUsmConst
    let inUsmCall: eA ∈ (uniSetMap.call tA).defMem :=
      pCEq ▸ Set3.inCall (lane := .defLane) inUsmWfm
    ⟨eA, tEq ▸ inUsmCall, by
      rw [pEq, pLEq, pREq, ←iFnEq]⟩
  
  /-- The possible-membership variant of `embedStep_elim_def`. -/
  theorem embedStep_elim_pos {iFn t p: Pair}
    (ins: p ∈ (((trisetEmbedHelpersDl.val "embedStep").call iFn).call t).posMem)
  :
    ∃ e,
      And
        (e ∈ (uniSetMap.call t).posMem)
        (p = .pair (.nat 0) (iFn.indexCall e))
  :=
    let ins :=
      Set3.inCallElim (lane := .posLane)
        (Set3.inCallElim (lane := .posLane) ins)
    let ins := DefList.in_def_body_no_fv (lane := .posLane) ins
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
    let pREq: pR = iFnA.indexCall eA :=
      let h1 :=
        inCallElimSingle inApp (intp_var_eq_singleton rfl)
      let h2 :=
        inCallElimSingle h1 (intp_var_eq_singleton rfl)
      let h2w:
        (trisetEmbedHelpersDl.val "indexCall").posMem.Mem
          (.pair iFnA (.pair eA pR))
      :=
        h2
      let h3:
        .pair iFnA (.pair eA pR) ∈ (opFixDl.val "indexCall").posMem
      :=
        (wfm_indexCall_eq ▸ h2w)
      (opFixDl.indexCall_elim h3).symm
    let ⟨inCallPart, inVarPart⟩ := inIrElim inCond
    let pCEq: pC = eA := inVarElim inVarPart rfl
    let inUsmConst :=
      inCallElimSingle inCallPart (intp_var_eq_singleton rfl)
    let inUsmWfm: .pair tA pC ∈ uniSetMap.posMem :=
      wfm_uniSetMap_eq ▸ inUsmConst
    let inUsmCall: eA ∈ (uniSetMap.call tA).posMem :=
      pCEq ▸ Set3.inCall (lane := .posLane) inUsmWfm
    ⟨eA, tEq ▸ inUsmCall, by
      rw [pEq, pLEq, pREq, ←iFnEq]⟩
  
  /-- Lane-polymorphic form of `embedStep_elim`. -/
  theorem embedStep_elim {iFn t p: Pair} {lane: Set3.Lane}
    (ins: p ∈ (((trisetEmbedHelpersDl.val "embedStep").call iFn).call t).getLane lane)
  :
    ∃ e,
      And
        (e ∈ (uniSetMap.call t).getLane lane)
        (p = .pair (.nat 0) (iFn.indexCall e))
  :=
    match lane with
    | .defLane => embedStep_elim_def ins
    | .posLane => embedStep_elim_pos ins
  
  /-- The characteristic equation of `embedStep`. -/
  theorem embedStep_call_eq (iFn t: Pair):
    Eq
      (((trisetEmbedHelpersDl.val "embedStep").call iFn).call t)
      (Set3.image
        (fun e => .pair (.nat 0) (iFn.indexCall e))
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
  theorem embedStepIndex_call:
    uniSetMap.call embedStepIndex
      =
    trisetEmbedHelpersDl.val "embedStep"
  :=
    trisetEmbedHelpersDl.dl.uniSetMapAt_eq
      []
      (.const () (trisetEmbedHelpersDl.const "embedStep"))
  
end TrisetEmbedding


namespace trisetEmbedDl
  open Expr
  
  /-- The `indexCall` constant of this deflist denotes `indexCall`. -/
  theorem wfm_indexCall_eq:
    trisetEmbedDl.val "indexCall" = opFixDl.val "indexCall"
  :=
    trisetEmbedDl.extend_wfm_eq opFixDl "indexCall"
  
  /-- `embedOp` maps `iFn` to `embedStepIndex.indexCall iFn` (intro). -/
  theorem embedOp_ins_def {iFn: Pair}:
    ((trisetEmbedDl.val "embedOp").call iFn).defMem.Mem
      (TrisetEmbedding.embedStepIndex.indexCall iFn)
  :=
    let inIndexCallWfm:
      (trisetEmbedDl.val "indexCall").defMem.Mem
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn)))
    :=
      wfm_indexCall_eq ▸
        opFixDl.indexCall_ins (tag := ()) (lane := .defLane)
          TrisetEmbedding.embedStepIndex iFn
    let inIndexCall:
      Set.Mem
        ((Expr.const .basic (trisetEmbedDl.const "indexCall")).intp
          .defLane
          trisetEmbedDl.dl.wfm
          trisetEmbedDl.dl.wfm
          [.pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn),
          TrisetEmbedding.embedStepIndex.indexCall iFn,
          iFn])
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn)))
    :=
      inIndexCallWfm
    Set3.inCall (lane := .defLane) <|
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl)
      (inCall
        (pA := iFn)
        (pB := TrisetEmbedding.embedStepIndex.indexCall iFn)
        (inCall
          (pA := TrisetEmbedding.embedStepIndex)
          (pB := .pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn))
          inIndexCall
          (inToNamedExpr TrisetEmbedding.embedStepIndex))
        (inVar rfl))
  
  /-- The possible-membership variant of `embedOp_ins_def`. -/
  theorem embedOp_ins_pos {iFn: Pair}:
    ((trisetEmbedDl.val "embedOp").call iFn).posMem.Mem
      (TrisetEmbedding.embedStepIndex.indexCall iFn)
  :=
    let inIndexCallWfm:
      (trisetEmbedDl.val "indexCall").posMem.Mem
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn)))
    :=
      wfm_indexCall_eq ▸
      Set3.defToPos
        (opFixDl.indexCall_ins (tag := ()) (lane := .defLane)
          TrisetEmbedding.embedStepIndex iFn)
    let inIndexCall:
      Set.Mem
        ((Expr.const .basic (trisetEmbedDl.const "indexCall")).intp
          .posLane
          trisetEmbedDl.dl.wfm
          trisetEmbedDl.dl.wfm
          [.pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn),
          TrisetEmbedding.embedStepIndex.indexCall iFn,
          iFn])
        (.pair TrisetEmbedding.embedStepIndex
          (.pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn)))
    :=
      inIndexCallWfm
    Set3.inCall (lane := .posLane) <|
    DefList.in_def_no_fv <|
    inArbUn iFn <|
    inProd (inVar rfl)
      (inCall
        (pA := iFn)
        (pB := TrisetEmbedding.embedStepIndex.indexCall iFn)
        (inCall
          (pA := TrisetEmbedding.embedStepIndex)
          (pB := .pair iFn (TrisetEmbedding.embedStepIndex.indexCall iFn))
          inIndexCall
          (inToNamedExpr TrisetEmbedding.embedStepIndex))
        (inVar rfl))
  
  /-- `embedOp` is functional (elim, definitive lane). -/
  theorem embedOp_elim_def {iFn s: Pair}
    (ins: s ∈ ((trisetEmbedDl.val "embedOp").call iFn).defMem)
  :
    s = TrisetEmbedding.embedStepIndex.indexCall iFn
  :=
    let ins := Set3.inCallElim (lane := .defLane) ins
    let ins := DefList.in_def_body_no_fv (lane := .defLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨inIFnV, inApp⟩ := inProdElim ins
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let h1 := inCallElimSingle inApp (intp_var_eq_singleton rfl)
    let h2 :=
      inCallElimSingle
        h1
        (intp_toNamedExpr_eq_singleton TrisetEmbedding.embedStepIndex)
    let h2w:
      (trisetEmbedDl.val "indexCall").defMem.Mem
        (.pair TrisetEmbedding.embedStepIndex (.pair iFnA s))
    :=
      h2
    let encEq :=
      opFixDl.indexCall_elim (Set3.defToPos (wfm_indexCall_eq ▸ h2w))
    iFnEq ▸ encEq.symm
  
  /-- `embedOp` is functional (elim, possible lane). -/
  theorem embedOp_elim_pos {iFn s: Pair}
    (ins: s ∈ ((trisetEmbedDl.val "embedOp").call iFn).posMem)
  :
    s = TrisetEmbedding.embedStepIndex.indexCall iFn
  :=
    let ins := Set3.inCallElim (lane := .posLane) ins
    let ins := DefList.in_def_body_no_fv (lane := .posLane) ins
    let ⟨iFnA, ins⟩ := inArbUnElim ins
    let ⟨inIFnV, inApp⟩ := inProdElim ins
    let iFnEq: iFn = iFnA := inVarElim inIFnV rfl
    let h1 := inCallElimSingle inApp (intp_var_eq_singleton rfl)
    let h2 :=
      inCallElimSingle
        h1
        (intp_toNamedExpr_eq_singleton TrisetEmbedding.embedStepIndex)
    let h2w:
      (trisetEmbedDl.val "indexCall").posMem.Mem
        (.pair TrisetEmbedding.embedStepIndex (.pair iFnA s))
    :=
      h2
    let encEq :=
      opFixDl.indexCall_elim (wfm_indexCall_eq ▸ h2w)
    iFnEq ▸ encEq.symm
  
  /-- `embedOp` denotes the function `indexCall embedStepIndex`. -/
  theorem embedOp_call_eq (iFn: Pair):
    Eq
      ((trisetEmbedDl.val "embedOp").call iFn)
      (Set3.just (TrisetEmbedding.embedStepIndex.indexCall iFn))
  :=
    Set3.eq4
      (fun _ din => embedOp_elim_def din)
      (fun _ din => din ▸ embedOp_ins_def)
      (fun _ din => embedOp_elim_pos din)
      (fun _ din => din ▸ embedOp_ins_pos)
  
end trisetEmbedDl


namespace TrisetEmbedding
  /-- Calling `embedOpIndex` yields the `embedOp` triset. -/
  theorem embedOpIndex_call:
    uniSetMap.call embedOpIndex = trisetEmbedDl.val "embedOp"
  :=
    trisetEmbedDl.dl.uniSetMapAt_eq
      []
      (.const () (trisetEmbedDl.const "embedOp"))
  
  theorem embedOpIndex_call_eq (iFn: Pair):
    Eq
      ((uniSetMap.call embedOpIndex).call iFn)
      (Set3.just (embedStepIndex.indexCall iFn))
  :=
    (congrArg (·.call iFn) embedOpIndex_call).trans
      (trisetEmbedDl.embedOp_call_eq iFn)
  
  /- The fixed point of the embedding operator. -/
  exposed def embedFixIndex: Pair := indexFixIndex embedOpIndex
  
  /-- The fixed point equation of `embedFixIndex`. -/
  theorem embedFixIndex_call_eq:
    uniSetMap.call embedFixIndex
      =
    uniSetMap.call (embedStepIndex.indexCall embedFixIndex)
  :=
    indexFixIndex_fix_of_fn
      embedOpIndex
      (fun x => embedStepIndex.indexCall x)
      embedOpIndex_call_eq
  
  /--
    The embedding map on triset indices: `embed t` is a triset whose
    members are the codes `(0, embed e)` of the embedded members of `t`.
  -/
  def embed (t: Pair): Pair := embedFixIndex.indexCall t
  
  /-- The characteristic equation of `embed`. -/
  theorem embed_call_eq (t: Pair):
    uniSetMap.call (embed t)
      =
    Set3.image (fun e => .pair (.nat 0) (embed e)) (uniSetMap.call t)
  :=
    (opFixDl.indexCall_correct embedFixIndex t).trans
      ((congrArg (·.call t) embedFixIndex_call_eq).trans
        ((congrArg
            (·.call t)
            (opFixDl.indexCall_correct embedStepIndex embedFixIndex)).trans
          ((congrArg
              (fun s => (s.call embedFixIndex).call t)
              embedStepIndex_call).trans
            (trisetEmbedHelpersDl.embedStep_call_eq embedFixIndex t))))
  
  /-- Definitive members of `t` embed to definitive members of
  `embed t`. -/
  theorem embed_ins {t e: Pair}
    (ins: e ∈ (uniSetMap.call t).defMem)
  :
    .pair (.nat 0) (embed e) ∈ (uniSetMap.call (embed t)).defMem
  :=
    embed_call_eq t ▸ ⟨e, ins, rfl⟩
  
  /-- Possible members of `t` embed to possible members of
  `embed t`. -/
  theorem embed_inw {t e: Pair}
    (inw: e ∈ (uniSetMap.call t).posMem)
  :
    .pair (.nat 0) (embed e) ∈ (uniSetMap.call (embed t)).posMem
  :=
    embed_call_eq t ▸ ⟨e, inw, rfl⟩
  
  /-- Definitive members of `embed t` are embeddings of definitive
  members of `t`. -/
  theorem embed_elim_def {t p: Pair}
    (mem: p ∈ (uniSetMap.call (embed t)).defMem)
  :
    ∃ e, e ∈ (uniSetMap.call t).defMem ∧ p = .pair (.nat 0) (embed e)
  :=
    let ⟨e, hin, heq⟩ := embed_call_eq t ▸ mem
    ⟨e, hin, heq.symm⟩
  
  /-- Possible members of `embed t` are embeddings of possible
  members of `t`. -/
  theorem embed_elim_pos {t p: Pair}
    (mem: p ∈ (uniSetMap.call (embed t)).posMem)
  :
    ∃ e, e ∈ (uniSetMap.call t).posMem ∧ p = .pair (.nat 0) (embed e)
  :=
    let ⟨e, hin, heq⟩ := embed_call_eq t ▸ mem
    ⟨e, hin, heq.symm⟩
  
end TrisetEmbedding
