module
public import Etst.WFC.Ch2_Interpretation
public import Etst.WFC.Utils.Expr.ExpandsInto
import Etst.WFC.Utils.Expr.FreeVars
import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst


exposed def Expr.replaceDepthEvenConsts {kind}
  (e: Expr kind)
  (depth: Nat) -- number of quantifiers crossed so far
  (ed: Bool) -- "even depth", number of complements crossed so far
  (replacer: (depth: Nat) → kind.ConstTag → Nat → Expr kind)
:
  Expr kind
:=
  match e with
  | const i x => if ed then replacer depth i x else .const i x
  | var x => .var x
  | null => null
  | prod left rite =>
    prod
      (left.replaceDepthEvenConsts depth ed replacer)
      (rite.replaceDepthEvenConsts depth ed replacer)
  | ir left rite =>
    ir
      (left.replaceDepthEvenConsts depth ed replacer)
      (rite.replaceDepthEvenConsts depth ed replacer)
  | full body =>
    full (body.replaceDepthEvenConsts depth ed replacer)
  | compl body =>
    compl (body.replaceDepthEvenConsts depth (!ed) replacer)
  | arbIr body =>
    arbIr (body.replaceDepthEvenConsts (depth + 1) ed replacer)

-- Represents an inductive proof of `const lane x ⊆ expr`
structure InductionDescriptor (dl: DefList) where
  lane: Set3.Lane
  x: Nat
  expr: Expr .lane
  expansion: Expr .basic
  expandsInto: dl.ExpandsInto true (dl.getDef x) expansion

exposed def InductionDescriptor.hypothesis
  (depth: Nat)
  (lane: Set3.Lane)
  (x: Nat)
  {dl} (desc: InductionDescriptor dl)
  (expr: Expr .lane)
:
  Expr .lane
:=
  if lane.Le desc.lane ∧ desc.x = x
  then .ir (desc.expr.lift 0 depth) expr
  else expr

abbrev MutIndDescriptor (dl: DefList) := List (InductionDescriptor dl)

exposed def MutIndDescriptor.hypothesis
  {dl} (desc: MutIndDescriptor dl)
  (depth: Nat)
  (lane: Set3.Lane)
  (x: Nat)
:
  Expr .lane
:=
  desc.foldr
    (InductionDescriptor.hypothesis depth lane x)
    (.const lane x)

exposed def MutIndDescriptor.hypothesify
  {dl} (desc: MutIndDescriptor dl)
  (depth := 0)
  (expr: Expr .lane)
:
  Expr .lane
:=
  expr.replaceDepthEvenConsts depth true desc.hypothesis


theorem DefList.lfpStage_le_wfm_std
  (dl: DefList)
  (n: Ordinal)
:
  let _ := Valuation.ordStdLattice
  (operatorC dl dl.wfm).lfpStage n ≤ dl.wfm
:= by
  intro
  conv => rhs; rw [dl.wfm_eq_lfpC]
  exact (operatorC dl dl.wfm).lfpStage_le_lfp n

exposed def InductionDescriptor.Invariant {dl}
  (desc: InductionDescriptor dl)
  (wfm v: Valuation Pair)
  (fv: List Pair)
:=
  Set.Subset
    ((v desc.x).getLane desc.lane)
    (desc.expr.intp () wfm wfm fv)

open Expr in
theorem MutIndDescriptor.var_le_hypothesify {dl v x lane}
  (desc: MutIndDescriptor dl)
  -- `fv` represent the bound variables of the induction itself,
  -- `fvDepth` represent the bound variables introduced by the
  -- quantifiers of the hypothesified expression.
  (fv fvDepth: List Pair)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v fv)
  (v_le: v ≤ dl.wfm)
:
  Set.Subset
    ((v x).getLane lane)
    ((desc.hypothesify fvDepth.length (.const lane x)).intp
      ()
      dl.wfm
      dl.wfm
      (fvDepth ++ fv))
:=
  match desc with
  | [] =>
    match lane with
    | .posLane => (v_le x).posLe
    | .defLane => (v_le x).defLe
  | head :: (rest: MutIndDescriptor dl) =>
    show
      Set.Subset _
        ((if (_: Prop) then _ else _: Expr .lane).intp _ _ _ _)
    from
    let invTail := List.Index.indexedTail
      (P :=
        fun (desc: InductionDescriptor dl) =>
          desc.Invariant dl.wfm v fv)
      inv
    if h: lane.Le head.lane ∧ head.x = x then
      let ⟨laneLe, xEq⟩ := h
      ite_eq_left h ▸
      fun p inXLane =>
        let inXHeadLane: p ∈ (v head.x).getLane head.lane :=
          xEq ▸ laneLe.liftMem inXLane
        let inRite :=
          inv
            ⟨0, Nat.zero_lt_succ _⟩
            inXHeadLane
        inIr
          (head.expr.intp_lift_eq () dl.wfm dl.wfm fv fvDepth ▸
          inRite)
          (rest.var_le_hypothesify fv fvDepth invTail v_le inXLane)
    else
      ite_eq_right h ▸
      rest.var_le_hypothesify fv fvDepth invTail v_le

mutual
  theorem MutIndDescriptor.le_hypothesify {dl v}
    (desc: MutIndDescriptor dl)
    -- The bound variables of the induction itself.
    (fv: List Pair)
    -- `fvDepth` is an internal matter of this function and is only
    -- good for the recursive calls. It represents the bound variables
    -- introduced by the quantifiers of the hypothesified expression.
    (fvDepth: List Pair := [])
    (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v fv)
    {expr: Expr .lane}
    (v_le: v ≤ dl.wfm)
  :
    let exprHypothesified: Expr .lane :=
      expr.replaceDepthEvenConsts fvDepth.length true desc.hypothesis
    Set.Subset
      (expr.intp () dl.wfm v (fvDepth ++ fv))
      (exprHypothesified.intp () dl.wfm dl.wfm (fvDepth ++ fv))
  :=
    open Expr in
    match expr with
    | .const _ _ =>
      var_le_hypothesify desc fv fvDepth inv v_le
    | .var _ => Set.Subset.refl _
    | .null => Set.Subset.refl _
    | .prod _ _ =>
      intp_mono_std_prod
        (desc.le_hypothesify fv fvDepth inv v_le)
        (desc.le_hypothesify fv fvDepth inv v_le)
    | .ir _ _ =>
      intp_mono_std_ir
        (desc.le_hypothesify fv fvDepth inv v_le)
        (desc.le_hypothesify fv fvDepth inv v_le)
    | .full _ =>
      intp_mono_std_full (desc.le_hypothesify fv fvDepth inv v_le)
    | .compl _ =>
      intp_antimono_std_compl
        (desc.ge_hypothesify fv fvDepth inv v_le)
    | .arbIr _ =>
      intp_mono_std_arbIr fun p =>
        desc.le_hypothesify fv (p :: fvDepth) inv v_le

  theorem MutIndDescriptor.ge_hypothesify {dl v}
    (desc: MutIndDescriptor dl)
    (fv: List Pair)
    (fvDepth: List Pair := [])
    (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v fv)
    {expr: Expr .lane}
    (v_le: v ≤ dl.wfm)
  :
    let exprHypothesified: Expr .lane :=
      expr.replaceDepthEvenConsts fvDepth.length false desc.hypothesis
    Set.Subset
      (exprHypothesified.intp () dl.wfm dl.wfm (fvDepth ++ fv))
      (expr.intp () v dl.wfm (fvDepth ++ fv))
  :=
    open Expr in
    match expr with
    | .const _ _ => Set.Subset.refl _
    | .var _ => Set.Subset.refl _
    | .null => Set.Subset.refl _
    | .prod _ _ =>
      intp_mono_std_prod
        (desc.ge_hypothesify fv fvDepth inv v_le)
        (desc.ge_hypothesify fv fvDepth inv v_le)
    | .ir _ _ =>
      intp_mono_std_ir
        (desc.ge_hypothesify fv fvDepth inv v_le)
        (desc.ge_hypothesify fv fvDepth inv v_le)
    | .full _ =>
      intp_mono_std_full (desc.ge_hypothesify fv fvDepth inv v_le)
    | .compl _ =>
      intp_antimono_std_compl
        (desc.le_hypothesify fv fvDepth inv v_le)
    | .arbIr _ =>
      intp_mono_std_arbIr fun p =>
        desc.ge_hypothesify fv (p :: fvDepth) inv v_le
end

theorem MutIndDescriptor.isSound {dl}
  (desc: MutIndDescriptor dl)
  (fv: List Pair)
  (premisesHold:
    (i: desc.Index) →
    let expansion := desc[i].expansion.toLane desc[i].lane
    Set.Subset
      ((desc.hypothesify 0 expansion).intp () dl.wfm dl.wfm fv)
      (desc[i].expr.intp () dl.wfm dl.wfm fv))
  (i: desc.Index)
:
  let expr: Expr .lane := .const desc[i].lane desc[i].x
  Set.Subset
    (expr.intp () dl.wfm dl.wfm fv)
    (desc[i].expr.intp () dl.wfm dl.wfm fv)
:=
  let := Valuation.ordStdLattice
  let opC := operatorC dl dl.wfm
  let eq: dl.wfm = opC.lfp := dl.wfm_eq_lfpC
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      opC
      (fun v => ∀ (i: desc.Index), desc[i].Invariant dl.wfm v fv)
      (fun n isLim ih i p inSup =>
        let ⟨m, isMem⟩:
          ∃ m: ↑n,
            p ∈ (opC.lfpStage m desc[i].x).getLane desc[i].lane
        :=
          match h: desc[i].lane with
          | .posLane =>
            let ⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩, isMem⟩ := h ▸ inSup
            let vEq: opC.lfpStage m = v := vEq
            let s3Eq: v _ = s3 := s3Eq
            ⟨m, h ▸ vEq ▸ s3Eq ▸ isMem⟩
          | .defLane =>
            let ⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩, isMem⟩ := h ▸ inSup
            let vEq: opC.lfpStage m = v := vEq
            let s3Eq: v _ = s3 := s3Eq
            ⟨m, h ▸ vEq ▸ s3Eq ▸ isMem⟩
        ih m i isMem)
      (fun n notLim predLt ih i p isMem =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let predStage := opC.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std n.pred
        let lePremise :=
          desc.le_hypothesify fv [] ihPred predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std fv n.pred
        let isMemFv:
          Set.Mem
            (Set3.getLane
              ((dl.getDef desc[i].x).triIntp dl.wfm predStage fv)
              desc[i].lane)
            p
        :=
          dl.triIntp_getDef_eq_fv desc[i].x dl.wfm predStage [] fv ▸ isMem
        let inExpansion :=
          (Expr.toLane_intp desc[i].expansion desc[i].lane dl.wfm
            predStage fv).symm ▸
          Expr.triIntp_getLane_eq desc[i].expansion ▸
          leExp.memLe isMemFv
        premisesHold i (lePremise inExpansion))
  
  by rw [←eq] at isDefSub; exact isDefSub i
