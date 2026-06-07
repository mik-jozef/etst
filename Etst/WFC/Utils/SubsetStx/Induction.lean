import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.Expr.ExpandsInto

namespace Etst


def Expr.replaceDepthEvenConsts {E}
  (e: Expr E)
  (depth: Nat) -- number of quantifiers crossed so far
  (ed: Bool) -- "even depth", number of complements crossed so far
  (replacer: (depth: Nat) → E → Nat → Expr E)
:
  Expr E
:=
  match e with
  | const i x => if ed then replacer depth i x else .const i x
  | oracle i x => .oracle i x
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
  expr: SingleLaneExpr
  expansion: BasicExpr
  expandsInto: dl.ExpandsInto true (dl.getDef x) expansion

def InductionDescriptor.hypothesis
  (depth: Nat)
  (lane: Set3.Lane)
  (x: Nat)
  {dl} (desc: InductionDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  if lane.Le desc.lane && desc.x = x
  then .ir (desc.expr.lift 0 depth) expr
  else expr

abbrev MutIndDescriptor (dl: DefList) := List (InductionDescriptor dl)

def MutIndDescriptor.hypothesis
  {dl} (desc: MutIndDescriptor dl)
  (depth: Nat)
  (lane: Set3.Lane)
  (x: Nat)
:
  SingleLaneExpr
:=
  desc.foldr
    (InductionDescriptor.hypothesis depth lane x)
    (.const lane x)

def MutIndDescriptor.hypothesify
  {dl} (desc: MutIndDescriptor dl)
  (depth := 0)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  expr.replaceDepthEvenConsts depth true desc.hypothesis


def DefList.lfpStage_le_wfm_std
  (dl: DefList)
  (o: Valuation Pair)
  (n: Ordinal)
:
  let _ := Valuation.ordStdLattice
  (operatorC dl (dl.wfm o) o).lfpStage n ≤ dl.wfm o
:= by
  intro
  conv => rhs; rw [dl.wfm_eq_lfpC o]
  exact (operatorC dl (dl.wfm o) o).lfpStage_le_lfp n

def InductionDescriptor.Invariant {dl}
  (desc: InductionDescriptor dl)
  (wfm v o: Valuation Pair)
  (fv: List Pair)
:=
  Set.Subset ((v desc.x).getLane desc.lane) (desc.expr.intp fv wfm o)

open SingleLaneExpr in
def MutIndDescriptor.var_le_hypothesify {dl v x lane o}
  (desc: MutIndDescriptor dl)
  -- `fv` represent the bound variables of the induction itself,
  -- `fvDepth` represent the bound variables introduced by the
  -- quantifiers of the hypothesified expression.
  (fv fvDepth: List Pair)
  (inv: ∀ (i: desc.Index), desc[i].Invariant (dl.wfm o) v o fv)
  (v_le: v ≤ dl.wfm o)
:
  Set.Subset
    ((v x).getLane lane)
    (intp
      (desc.hypothesify fvDepth.length (.const lane x))
      (fvDepth ++ fv)
      (dl.wfm o)
      o)
:=
  match desc with
  | [] =>
    match lane with
    | .posLane => (v_le x).posLe
    | .defLane => (v_le x).defLe
  | head :: (rest: MutIndDescriptor dl) =>
    show _ ≤ intp (if _ then _ else _) _ (dl.wfm o) o from
    let invTail := List.Index.indexedTail
      (P :=
        fun (desc: InductionDescriptor dl) =>
          desc.Invariant (dl.wfm o) v o fv)
      inv
    if h: lane.Le head.lane && head.x = x then
      let ⟨laneLe, xEq⟩ := Bool.and_eq_true_iff.mp h
      let laneLe := of_decide_eq_true laneLe
      let xEq := of_decide_eq_true xEq
      if_pos h ▸
      fun p inXLane =>
        let inXHeadLane: (v head.x).getLane head.lane p :=
          xEq ▸ laneLe.liftMem inXLane
        let inRite :=
          inv
            ⟨0, Nat.zero_lt_succ _⟩
            inXHeadLane
        inIr
          (show intp2 _ _ _ _ _ _ from
          head.expr.intp2_lift_eq fv fvDepth (dl.wfm o) (dl.wfm o) o ▸
          inRite)
          (rest.var_le_hypothesify fv fvDepth invTail v_le inXLane)
    else
      if_neg h ▸
      rest.var_le_hypothesify fv fvDepth invTail v_le

mutual
  def MutIndDescriptor.le_hypothesify {dl v lane o}
    (desc: MutIndDescriptor dl)
    -- The bound variables of the induction itself.
    (fv: List Pair)
    -- `fvDepth` is an internal matter of this function and is only
    -- good for the recursive calls. It represents the bound variables
    -- introduced by the quantifiers of the hypothesified expression.
    (fvDepth: List Pair := [])
    (inv: ∀ (i: desc.Index), desc[i].Invariant (dl.wfm o) v o fv)
    {expr: SingleLaneExpr}
    (laneEq: expr.LaneEq (.some lane) (.some lane.toggle))
    (v_le: v ≤ dl.wfm o)
  :
    let exprHypothesified: SingleLaneExpr :=
      expr.replaceDepthEvenConsts fvDepth.length true desc.hypothesis
    Set.Subset
      (expr.intp2 (fvDepth ++ fv) (dl.wfm o) v o)
      (exprHypothesified.intp (fvDepth ++ fv) (dl.wfm o) o)
  :=
    open SingleLaneExpr in
    match expr with
    | .const _ _ =>
      var_le_hypothesify desc fv fvDepth inv v_le
    | .oracle _ _ => le_refl ((intp2 _ _ _ _ _))
    | .var _ => le_refl ((intp2 _ _ _ _ _))
    | .null => le_refl ((intp2 _ _ _ _ _))
    | .prod _ _ =>
      intp2_mono_std_prod
        (desc.le_hypothesify fv fvDepth inv laneEq.elimProdLeft v_le)
        (desc.le_hypothesify fv fvDepth inv laneEq.elimProdRite v_le)
    | .ir _ _ =>
      intp2_mono_std_ir
        (desc.le_hypothesify fv fvDepth inv laneEq.elimIrLeft v_le)
        (desc.le_hypothesify fv fvDepth inv laneEq.elimIrRite v_le)
    | .full _ =>
      intp2_mono_std_full
        (desc.le_hypothesify fv fvDepth inv laneEq.elimFull v_le)
    | .compl _ =>
      intp2_mono_std_compl
        (desc.ge_hypothesify fv fvDepth inv laneEq.elimCompl v_le)
    | .arbIr _ =>
      intp2_mono_std_arbIr fun p =>
        desc.le_hypothesify fv (p :: fvDepth) inv laneEq.elimArbIr v_le

  def MutIndDescriptor.ge_hypothesify {dl v lane o}
    (desc: MutIndDescriptor dl)
    (fv: List Pair)
    (fvDepth: List Pair := [])
    (inv: ∀ (i: desc.Index), desc[i].Invariant (dl.wfm o) v o fv)
    {expr: SingleLaneExpr}
    (laneEq: expr.LaneEq (.some lane.toggle) (.some lane))
    (v_le: v ≤ dl.wfm o)
  :
    let exprHypothesified: SingleLaneExpr :=
      expr.replaceDepthEvenConsts fvDepth.length false desc.hypothesis
    Set.Subset
      (exprHypothesified.intp (fvDepth ++ fv) (dl.wfm o) o)
      (expr.intp2 (fvDepth ++ fv) v (dl.wfm o) o)
  :=
    open SingleLaneExpr in
    match expr with
    | .const _ _ => le_refl ((intp2 _ _ _ _ _))
    | .oracle _ _ => le_refl ((intp2 _ _ _ _ _))
    | .var _ => le_refl ((intp2 _ _ _ _ _))
    | .null => le_refl ((intp2 _ _ _ _ _))
    | .prod _ _ =>
      intp2_mono_std_prod
        (desc.ge_hypothesify fv fvDepth inv laneEq.elimProdLeft v_le)
        (desc.ge_hypothesify fv fvDepth inv laneEq.elimProdRite v_le)
    | .ir _ _ =>
      intp2_mono_std_ir
        (desc.ge_hypothesify fv fvDepth inv laneEq.elimIrLeft v_le)
        (desc.ge_hypothesify fv fvDepth inv laneEq.elimIrRite v_le)
    | .full _ =>
      intp2_mono_std_full
        (desc.ge_hypothesify fv fvDepth inv laneEq.elimFull v_le)
    | .compl _ =>
      intp2_mono_std_compl
        (desc.le_hypothesify fv fvDepth inv laneEq.elimCompl v_le)
    | .arbIr _ =>
      intp2_mono_std_arbIr fun p =>
        desc.ge_hypothesify fv (p :: fvDepth) inv laneEq.elimArbIr v_le
end

open SingleLaneExpr in
def MutIndDescriptor.isSound {dl}
  (desc: MutIndDescriptor dl)
  (fv: List Pair)
  (o: Valuation Pair)
  (premisesHold:
    (i: desc.Index) →
    let expansion := desc[i].expansion.toLane desc[i].lane
    Set.Subset
      (intp (desc.hypothesify 0 expansion) fv (dl.wfm o) o)
      (intp desc[i].expr fv (dl.wfm o) o))
  (i: desc.Index)
:
  Set.Subset
    (intp (.const desc[i].lane desc[i].x) fv (dl.wfm o) o)
    (intp desc[i].expr fv (dl.wfm o) o)
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm o = (operatorC dl (dl.wfm o) o).lfp := dl.wfm_eq_lfpC o
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC dl (dl.wfm o) o)
      (fun v =>
        ∀ (i: desc.Index), desc[i].Invariant (dl.wfm o) v o fv)
      (fun n isLim ih i p inSup =>
        let ⟨m, isMem⟩:
          ∃ m: ↑n,
            ((operatorC dl (dl.wfm o) o).lfpStage m desc[i].x).getLane
              desc[i].lane p
        :=
          match h: desc[i].lane with
          | .posLane =>
            let ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, isMem⟩ := h ▸ inSup
            let vEq: (operatorC dl (dl.wfm o) o).lfpStage m = v := vEq
            let s3Eq: v _ = s3 := s3Eq
            ⟨m, h ▸ vEq ▸ s3Eq ▸ isMem⟩
          | .defLane =>
            let ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, isMem⟩ := h ▸ inSup
            let vEq: (operatorC dl (dl.wfm o) o).lfpStage m = v := vEq
            let s3Eq: v _ = s3 := s3Eq
            ⟨m, h ▸ vEq ▸ s3Eq ▸ isMem⟩
        ih m i isMem)
      (fun n notLim predLt ih i x isMem =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC dl (dl.wfm o) o
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std o n.pred
        let laneEq := desc[i].expansion.laneEq desc[i].lane
        let lePremise :=
          desc.le_hypothesify fv [] ihPred laneEq predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std fv n.pred o
        let isMemFv:
          ((dl.getDef desc[i].x).triIntp2 _ _ _ _).getLane _ x
        := by
          rw [←dl.intpDefs2_eq_fv desc[i].x [] fv (dl.wfm o) predStage o]
          exact isMem
        let inExpansion :=
          desc[i].expansion.triIntp2_getLane_eq ▸ leExp.memLe isMemFv
        premisesHold i (lePremise inExpansion))
  
  by rw [←eq] at isDefSub; exact isDefSub i
