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
:=
  ∀ bv, Set.Subset (v desc.left).posMem (desc.rite.intp bv wfm)

def MutIndDescriptor.var_le_hypothesify
  (desc: MutIndDescriptor dl)
  -- `bv` represent the bound variables of the induction itself,
  -- `bvDepth` represent the bound variables introduced by the
  -- quantifiers of the hypothesified expression.
  (bv bvDepth: List Pair)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
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
          desc.Invariant dl.wfm v)
      inv
    if h: head.left = x then
      if_pos h ▸
      fun _ inX =>
        let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ bv (h ▸ inX)
        Expr.inIr
          (show intp2 _ _ _ _ _ from
          head.rite.intp2_lift_eq bv bvDepth dl.wfm dl.wfm ▸
          inRite)
          (rest.var_le_hypothesify bv bvDepth invTail v_le inX)
    else
      if_neg h ▸
      rest.var_le_hypothesify bv bvDepth invTail v_le

def MutIndDescriptor.le_hypothesify
  (desc: MutIndDescriptor dl)
  -- The bound variables of the induction itself.
  (bv: List Pair)
  -- `bvDepth` are an internal matter of this function and are
  -- only good for the recirsive calls. They represent the bound
  -- variables introduced by the quantifiers of the hypothesified
  -- expression.
  (bvDepth: List Pair := [])
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (isConstrained: expr.LaneEqCtx .posLane)
  (v_le: v ≤ dl.wfm)
:
  expr.intp2 (bvDepth ++ bv) dl.wfm v
    ≤
  (desc.hypothesify bvDepth.length expr).intp (bvDepth ++ bv) dl.wfm
:=
  match expr with
  | .var .posLane _ => var_le_hypothesify desc bv bvDepth inv v_le
  | .bvar _ => le_rfl
  | .null => le_rfl
  | .pair _ _ =>
    intp2_mono_std_pair
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimPairLeft v_le)
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimPairRite v_le)
  | .un _ _ =>
    intp2_mono_std_un
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimUnLeft v_le)
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimUnRite v_le)
  | .ir _ _ =>
    intp2_mono_std_ir
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimIrLeft v_le)
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimIrRite v_le)
  | .condSome _ => 
    intp2_mono_std_condSome
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimCondSome v_le)
  | .condFull _ =>
    intp2_mono_std_condFull
      (desc.le_hypothesify bv bvDepth inv isConstrained.elimCondFull v_le)
  | .compl _ => le_rfl
  | .arbUn _ =>
    inter_mono_std_arbUn fun d =>
      desc.le_hypothesify bv (d :: bvDepth) inv isConstrained.elimArbUn v_le
  | .arbIr _ =>
    inter_mono_std_arbIr fun d =>
      desc.le_hypothesify bv (d :: bvDepth) inv isConstrained.elimArbIr v_le


def MutIndDescriptor.isSound
  (desc: MutIndDescriptor dl)
  (premisesHold:
    (i: desc.Index) →
    (bv: List Pair) →
    dl.SubsetBv bv
      (desc.hypothesify 0 (desc[i].expansion.toLane .posLane))
      desc[i].rite)
  (i: desc.Index)
:
  ∀ bv,
  dl.SubsetBv bv (.var .posLane desc[i].left) desc[i].rite
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm = (operatorC dl dl.wfm).lfp := dl.wfm_eq_lfpC
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC dl dl.wfm)
      (fun v =>
        ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
      (fun n isLim ih i bv p ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, atStage⟩ =>
        let vEq: (operatorC dl dl.wfm).lfpStage m = v := vEq
        let s3Eq: v _ = s3 := s3Eq
        let pIn:
          p ∈ ((operatorC dl dl.wfm).lfpStage m desc[i].left).posMem
        :=
          vEq ▸ s3Eq ▸ atStage
        ih m i bv pIn)
      (fun n notLim predLt ih i bv _ isPos =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std n.pred
        let laneEq := desc[i].expansion.laneEqCtx .posLane
        let lePremiseL := desc.le_hypothesify bv [] ihPred laneEq predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std bv n.pred
        let isPosBv:
          (BasicExpr.triIntp2 (dl.getDef desc[i].left) bv dl.wfm predStage).posMem _
        :=
          dl.interp_eq_bv desc[i].left [] bv dl.wfm predStage ▸
          isPos
        premisesHold i bv (lePremiseL (leExp.posLe isPosBv)))
  
  by rw [←eq] at isDefSub; exact isDefSub i

-- def test {a b: Nat} (eq: a = b)
-- ## Coinduction section

-- Represents a coinductive proof of `left ⊆ var .defLane rite`
structure CoinductionDescriptor (dl: DefList) where
  left: SingleLaneExpr
  rite: Nat
  expansion: BasicExpr
  expandsInto: ExpandsInto dl (dl.getDef rite) expansion

def CoinductionDescriptor.toInduction
  (desc: CoinductionDescriptor dl)
:
  InductionDescriptor dl
:= {
  left := desc.rite
  rite := .compl desc.left
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
  (_: SingleLaneVarType)
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
  .compl (expr.replaceComplZeroVars 0 desc.hypothesis)

def MutCoindDescriptor.sub_hypothesify
  (desc: MutCoindDescriptor dl)
  (sub: dl.SubsetStx ctx (replaceComplZeroVars expr 0 desc.hypothesis) b)
:
  let descMap: MutIndDescriptor dl :=
    desc.map CoinductionDescriptor.toInduction
  
  dl.SubsetStx ctx (replaceComplZeroVars expr 0 descMap.hypothesis) b
:=
  let rec helper := 4
  match expr with
  | .var _ x => sorry
  | .bvar x => sub
  | .null => sub
  | .pair l r => sorry
  | .un l r =>
      .subUn
        (sub_hypothesify desc sub.subUnElimL)
        (sub_hypothesify desc sub.subUnElimR)
  | .ir l r =>
      -- let subL := sub_hypothesify desc sub.subIrSwapL
      -- let subR := sub_hypothesify desc sub.subIrSwapR
      sorry
  | .condSome body => sorry
  | .condFull body => sorry
  | .compl body => sub
  | .arbUn body => sorry
  | .arbIr body => sorry
  
def mutCoinduction
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
    DefList.SubsetStx.mutInduction
      (ctx := ctx)
      descMap
      (fun i =>
        let eqMap: descMap[i] = desc[i.unmap].toInduction := by
          show descMap.get i = (desc.get i.unmap).toInduction
          rw [listEq]
          rfl
        eqMap ▸
        .subComplElim
          (.complComplA
            (.complSwapB
              (MutCoindDescriptor.sub_hypothesify
                desc
                (.complSwapB
                  (premises
                    i.unmap))))))
      iMap
  by
  rw [eqMap] at ind
  exact
    .subComplElim
      (.complComplA
        ind)


  def coinduction
    (desc: CoinductionDescriptor dl)
    (premise:
      dl.SubsetStx
        ctx
        desc.left
        (.compl
          ((desc.expansion.toLane .posLane).replaceComplZeroVars 0 fun depth _ x =>
            desc.hypothesis depth x (.var .posLane x))))
  :
    dl.SubsetStx ctx desc.left (.compl (.var .posLane desc.rite))
  :=
    mutCoinduction
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
          (((dl.getDef rite).toLane .posLane).replaceComplZeroVars 0 fun depth _ x =>
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
