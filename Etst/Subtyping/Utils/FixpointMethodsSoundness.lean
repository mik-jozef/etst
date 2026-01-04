import Etst.Subtyping.SubsetStx

namespace Etst
open Expr
open SingleLaneExpr


def DefList.lfpStage_le_wfm_std
  (dl: DefList)
  (n: Ordinal)
:
  let _ := Valuation.ordStdLattice
  (operatorC dl dl.wfm).lfpStage n ≤ dl.wfm
:= by
  intro
  conv => rhs; rw [dl.wfm_eq_lfpC]
  exact (operatorC dl (dl.wfm)).lfpStage_le_lfp n


def InductionDescriptor.Invariant
  (desc: InductionDescriptor dl)
  (wfm v: Valuation Pair)
  (bv: List Pair)
:=
  Set.Subset (v desc.x).posMem (desc.expr.intp bv wfm)

def MutIndDescriptor.var_le_hypothesify
  (desc: MutIndDescriptor dl)
  -- `bv` represent the bound variables of the induction itself,
  -- `bvDepth` represent the bound variables introduced by the
  -- quantifiers of the hypothesified expression.
  (bv bvDepth: List Pair)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v bv)
  (v_le: v ≤ dl.wfm)
:
  Set.Subset
    (v x).posMem
    (SingleLaneExpr.intp
      (desc.hypothesify bvDepth.length (.var .posLane x))
      (bvDepth ++ bv)
      dl.wfm)
:=
  match desc with
  | [] => (v_le x).posLe
  | head :: (rest: MutIndDescriptor dl) =>
    show _ ≤ SingleLaneExpr.intp (if _ then _ else _) _ dl.wfm from
    let invTail := List.Index.indexedTail
      (P :=
        fun (desc: InductionDescriptor dl) =>
          desc.Invariant dl.wfm v bv)
      inv
    if h: head.x = x then
      if_pos h ▸
      fun _ inX =>
        let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ (h ▸ inX)
        inIr
          (show intp2 _ _ _ _ _ from
          head.expr.intp2_lift_eq bv bvDepth dl.wfm dl.wfm ▸
          inRite)
          (rest.var_le_hypothesify bv bvDepth invTail v_le inX)
    else
      if_neg h ▸
      rest.var_le_hypothesify bv bvDepth invTail v_le

def MutIndDescriptor.le_hypothesify
  (desc: MutIndDescriptor dl)
  -- The bound variables of the induction itself.
  (bv: List Pair)
  -- `bvDepth` is an internal matter of this function and is only
  -- good for the recursive calls. It represents the bound variables
  -- introduced by the quantifiers of the hypothesified expression.
  (bvDepth: List Pair := [])
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v bv)
  {expr: SingleLaneExpr}
  (laneEq: expr.LaneEqEven .posLane ed)
  (v_le: v ≤ dl.wfm)
:
  if ed then
    Set.Subset
      (expr.intp2 (bvDepth ++ bv) dl.wfm v)
      ((desc.hypothesify bvDepth.length expr).intp (bvDepth ++ bv) dl.wfm)
  else
    Set.Subset
      (intp
        (expr.replaceDepthEvenVars bvDepth.length false desc.hypothesis)
        (bvDepth ++ bv)
        dl.wfm)
      (expr.intp2 (bvDepth ++ bv) v dl.wfm)
:=
  match expr, ed with
  | .var .posLane _, true => var_le_hypothesify desc bv bvDepth inv v_le
  | .var _ _, false => le_refl ((intp2 _ _ _ _))
  | .bvar _, true => le_refl ((intp2 _ _ _ _))
  | .bvar _, false => le_refl ((intp2 _ _ _ _))
  | .null, true => le_refl ((intp2 _ _ _ _))
  | .null, false => le_refl ((intp2 _ _ _ _))
  | .pair _ _, true =>
    intp2_mono_std_pair
      (desc.le_hypothesify bv bvDepth inv laneEq.elimPairLeft v_le)
      (desc.le_hypothesify bv bvDepth inv laneEq.elimPairRite v_le)
  | .pair _ _, false =>
    intp2_mono_std_pair
      (desc.le_hypothesify bv bvDepth inv laneEq.elimPairLeft v_le)
      (desc.le_hypothesify bv bvDepth inv laneEq.elimPairRite v_le)
  | .ir _ _, true =>
    intp2_mono_std_ir
      (desc.le_hypothesify bv bvDepth inv laneEq.elimIrLeft v_le)
      (desc.le_hypothesify bv bvDepth inv laneEq.elimIrRite v_le)
  | .ir _ _, false =>
    intp2_mono_std_ir
      (desc.le_hypothesify bv bvDepth inv laneEq.elimIrLeft v_le)
      (desc.le_hypothesify bv bvDepth inv laneEq.elimIrRite v_le)
  | .condFull _, true =>
    intp2_mono_std_condFull
      (desc.le_hypothesify bv bvDepth inv laneEq.elimCondFull v_le)
  | .condFull _, false =>
    intp2_mono_std_condFull
      (desc.le_hypothesify bv bvDepth inv laneEq.elimCondFull v_le)
  | .compl _, true =>
    inter_mono_std_compl
      (desc.le_hypothesify bv bvDepth inv laneEq.elimCompl v_le)
  | .compl _, false =>
    inter_mono_std_compl
      (desc.le_hypothesify bv bvDepth inv laneEq.elimCompl v_le)
  | .arbIr _, true =>
    inter_mono_std_arbIr fun d =>
      desc.le_hypothesify bv (d :: bvDepth) inv laneEq.elimArbIr v_le
  | .arbIr _, false =>
    inter_mono_std_arbIr fun d =>
      desc.le_hypothesify bv (d :: bvDepth) inv laneEq.elimArbIr v_le


def MutIndDescriptor.isSound
  (desc: MutIndDescriptor dl)
  (bv: List Pair)
  (premisesHold:
    (i: desc.Index) →
    dl.SubsetBv bv
      (desc.hypothesify 0 (desc[i].expansion.toLane .posLane))
      desc[i].expr)
  (i: desc.Index)
:
  dl.SubsetBv bv (.var .posLane desc[i].x) desc[i].expr
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm = (operatorC dl dl.wfm).lfp := dl.wfm_eq_lfpC
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC dl dl.wfm)
      (fun v =>
        ∀ (i: desc.Index), desc[i].Invariant dl.wfm v bv)
      (fun n isLim ih i p ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, atStage⟩ =>
        let vEq: (operatorC dl dl.wfm).lfpStage m = v := vEq
        let s3Eq: v _ = s3 := s3Eq
        let pIn:
          p ∈ ((operatorC dl dl.wfm).lfpStage m desc[i].x).posMem
        :=
          vEq ▸ s3Eq ▸ atStage
        ih m i pIn)
      (fun n notLim predLt ih i _ isPos =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std n.pred
        let laneEq := desc[i].expansion.laneEqEven .posLane true
        let lePremiseL := desc.le_hypothesify bv [] ihPred laneEq predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std bv n.pred
        let isPosBv:
          (BasicExpr.triIntp2 (dl.getDef desc[i].x) bv dl.wfm predStage).posMem _
        := by
          rw [←dl.interp_eq_bv desc[i].x [] bv dl.wfm predStage]
          exact isPos
        premisesHold i (lePremiseL (leExp.posLe isPosBv)))
  
  by rw [←eq] at isDefSub; exact isDefSub i


-- ## Coinduction section (TBD)
-- note: before fixing this, generalize induction to arbitrary
-- variables, not just positive lanes.

-- Represents a coinductive proof of `left ⊆ var .defLane rite`
structure CoinductionDescriptor (dl: DefList) where
  left: SingleLaneExpr
  rite: Nat
  expansion: BasicExpr
  expandsInto: ExpandsInto dl true (dl.getDef rite) expansion

def CoinductionDescriptor.toInduction
  (desc: CoinductionDescriptor dl)
:
  InductionDescriptor dl
:= {
  x := desc.rite
  expr := .compl desc.left
  expansion := desc.expansion
  expandsInto := desc.expandsInto
}

abbrev MutCoindDescriptor (dl: DefList) := List (CoinductionDescriptor dl)

def CoinductionDescriptor.hypothesis
  (depth: Nat)
  (x: Nat)
  (desc: CoinductionDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  if desc.rite = x then .ir (.compl (desc.left.lift 0 depth)) expr else expr

def MutCoindDescriptor.hypothesis
  (desc: MutCoindDescriptor dl)
  (depth: Nat)
  -- We can ignore the lane analogously to `MutIndDescriptor.hypothesis`.
  (_: Set3.Lane)
  (x: Nat)
:
  SingleLaneExpr
:=
  desc.foldr (CoinductionDescriptor.hypothesis depth x) (.var .posLane x)

def MutCoindDescriptor.hypothesify
  (desc: MutCoindDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  .compl (expr.replaceDepthEvenVars 0 true desc.hypothesis)

def MutCoindDescriptor.sub_hypothesify
  (desc: MutCoindDescriptor dl)
  (sub: dl.SubsetStx ctx (Expr.replaceDepthEvenVars expr 0 true desc.hypothesis) b)
:
  let descMap: MutIndDescriptor dl :=
    desc.map CoinductionDescriptor.toInduction
  
  dl.SubsetStx ctx (Expr.replaceDepthEvenVars expr 0 true descMap.hypothesis) b
:=
  let rec helper := 4
  match expr with
  | .var _ x => sorry
  | .bvar x => sub
  | .null => sub
  | .pair l r => sorry
  | .ir l r =>
      -- let subL := sub_hypothesify desc sub.subIrSwapL
      -- let subR := sub_hypothesify desc sub.subIrSwapR
      sorry
  | .condFull body => sorry
  | .compl body => sorry
  | .arbIr body => sorry

-- TODO we should be aiming for mutCoinduction here, not subMutInduction.
def subMutCoinduction
  (desc: MutCoindDescriptor dl)
  (premises:
    (i: desc.Index) →
    dl.SubsetStx
      ctx
      desc[i].left
      (desc.hypothesify (desc[i].expansion.toLane .posLane)))
  (i: desc.Index)
:
  dl.SubsetStx ctx desc[i].left (.compl (.var .posLane desc[i].rite))
:=
  let descMap := desc.map CoinductionDescriptor.toInduction
  let iMap := i.map CoinductionDescriptor.toInduction
  let listEq i: List.get _ _ = _ :=
    desc.getElem_map CoinductionDescriptor.toInduction
  let eqMap: descMap[iMap] = desc[i].toInduction := by
    show descMap.get iMap = (desc.get i).toInduction
    rw [listEq]
    rfl
  let ind :=
    DefList.SubsetStx.subMutInduction
      (ctx := ctx)
      descMap
      (fun i =>
        let eqMap: descMap[i] = desc[i.unmap].toInduction := by
          show descMap.get i = (desc.get i.unmap).toInduction
          rw [listEq]
          rfl
        eqMap ▸
        .subComplElim
          (.dniCtx
            (.complSwap
              (MutCoindDescriptor.sub_hypothesify
                desc
                (.complSwap
                  (premises
                    i.unmap))))))
      iMap
  by
  rw [eqMap] at ind
  exact .subComplElim (.dniCtx ind)


  def coinduction
    (desc: CoinductionDescriptor dl)
    (premise:
      dl.SubsetStx
        ctx
        desc.left
        (.compl
          ((desc.expansion.toLane .posLane).replaceDepthEvenVars 0 true fun depth _ x =>
            desc.hypothesis depth x (.var .posLane x))))
  :
    dl.SubsetStx ctx desc.left (.compl (.var .posLane desc.rite))
  :=
    subMutCoinduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def simpleCoinduction
    (rite: Nat)
    (left: SingleLaneExpr)
    (premise:
      DefList.SubsetStx
        dl
        ctx
        left
        (.compl
          (((dl.getDef rite).toLane .posLane).replaceDepthEvenVars 0 true fun depth _ x =>
            if rite = x then .ir (.compl (left.lift 0 depth)) (.var .posLane x) else (.var .posLane x))))
  :
    dl.SubsetStx ctx left (.compl (.var .posLane rite))
  :=
    coinduction
      {
        left,
        rite,
        expansion := dl.getDef rite,
        expandsInto := .rfl
      }
      premise
