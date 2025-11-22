import Etst.Subtyping.SubsetStx

namespace Etst
open Expr
open SingleLaneExpr


def DefList.lfpStage_le_wfm_std
  (dl: DefList)
  (n: Ordinal)
:
  let _ := Valuation.ordStdLattice
  (operatorC dl (dl.wfm)).lfpStage n ≤ dl.wfm
:= by
  intro
  conv => rhs; rw [dl.wfm_eq_lfpC]
  exact (operatorC dl (dl.wfm)).lfpStage_le_lfp n


def InductionDescriptor.Invariant
  (desc: InductionDescriptor dl)
  (wfm v: Valuation Pair)
:=
  Set.Subset (v desc.left).posMem (desc.rite.intp [] wfm)

def MutIndDescriptor.var_le_hypothesify
  (desc: MutIndDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  (v x).posMem ≤ (desc.hypothesify (.var .posLane x)).intp bv dl.wfm
:=
  match desc with
  | [] => (v_le x).posLe
  | head :: (rest: MutIndDescriptor dl) =>
    show _ ≤ SingleLaneExpr.intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail
      (P := fun (desc: InductionDescriptor dl) => desc.Invariant dl.wfm v)
      inv
    if h: head.left = x then
      if_pos h ▸
      fun _ inX =>
        let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ (h ▸ inX)
        Expr.inIr
          (IsClean.changeBv head.riteIsClean inRite)
          (rest.var_le_hypothesify invTail v_le inX)
    else
      if_neg h ▸
      rest.var_le_hypothesify invTail v_le

def MutIndDescriptor.le_hypothesify
  (desc: MutIndDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (isConstrained: expr.LaneEqCtx .posLane)
  (v_le: v ≤ dl.wfm)
:
  expr.intp2 bv dl.wfm v
    ≤
  (desc.hypothesify expr).intp bv dl.wfm
:=
  match expr with
  | .var .posLane _ => var_le_hypothesify desc inv v_le
  | .bvar _ => le_rfl
  | .null => le_rfl
  | .pair _ _ =>
    intp2_mono_std_pair
      (desc.le_hypothesify inv isConstrained.elimPairLeft v_le)
      (desc.le_hypothesify inv isConstrained.elimPairRite v_le)
  | .un _ _ =>
    intp2_mono_std_un
      (desc.le_hypothesify inv isConstrained.elimUnLeft v_le)
      (desc.le_hypothesify inv isConstrained.elimUnRite v_le)
  | .ir _ _ =>
    intp2_mono_std_ir
      (desc.le_hypothesify inv isConstrained.elimIrLeft v_le)
      (desc.le_hypothesify inv isConstrained.elimIrRite v_le)
  | .condSome _ => 
    intp2_mono_std_condSome
      (desc.le_hypothesify inv isConstrained.elimCondSome v_le)
  | .condFull _ =>
    intp2_mono_std_condFull
      (desc.le_hypothesify inv isConstrained.elimCondFull v_le)
  | .compl _ => le_rfl
  | .arbUn _ =>
    inter_mono_std_arbUn fun _d =>
      desc.le_hypothesify inv isConstrained.elimArbUn v_le
  | .arbIr _ =>
    inter_mono_std_arbIr fun _d =>
      desc.le_hypothesify inv isConstrained.elimArbIr v_le


def MutIndDescriptor.isSound
  (desc: MutIndDescriptor dl)
  (premisesHold:
    (i: desc.Index) →
    dl.Subset
      (desc.hypothesify (desc[i].expansion.toLane .posLane))
      desc[i].rite)
  (i: desc.Index)
:
  dl.Subset (.var .posLane desc[i].left) desc[i].rite
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm = (operatorC dl dl.wfm).lfp := dl.wfm_eq_lfpC
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC dl dl.wfm)
      (fun v =>
        ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
      (fun n isLim ih i p ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, atStage⟩ =>
        let vEq: (operatorC dl dl.wfm).lfpStage m = v := vEq
        let s3Eq: v _ = s3 := s3Eq
        let pIn:
          p ∈ ((operatorC dl dl.wfm).lfpStage m desc[i].left).posMem
        :=
          vEq ▸ s3Eq ▸ atStage
        ih m i pIn)
      (fun n notLim predLt ih i _ isPos =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std n.pred
        let laneEq := desc[i].expansion.laneEqCtx .posLane
        let lePremiseL := desc.le_hypothesify ihPred laneEq predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std [] n.pred
        premisesHold i (lePremiseL (leExp.posLe isPos)))
  
  by rw [←eq] at isDefSub; exact isDefSub i


-- ## Coinduction section

-- Represents a coinductive proof of `left ⊆ var .defLane rite`
structure CoinductionDescriptor (dl: DefList) where
  left: SingleLaneExpr
  rite: Nat
  leftIsClean: left.IsClean
  expansion: BasicExpr
  expandsInto: ExpandsInto dl (dl.getDef rite) expansion

def CoinductionDescriptor.toInduction
  (desc: CoinductionDescriptor dl)
:
  InductionDescriptor dl
:= {
  left := desc.rite
  rite := .compl desc.left
  riteIsClean := by
    unfold IsClean clearBvars
    exact congr rfl desc.leftIsClean
  expansion := desc.expansion
  expandsInto := desc.expandsInto
}

abbrev MutCoindDescriptor (dl: DefList) := List (CoinductionDescriptor dl)

def CoinductionDescriptor.hypothesis
  (x: Nat)
  (desc: CoinductionDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  if desc.rite = x then .ir (.compl desc.left) expr else expr

def MutCoindDescriptor.hypothesis
  (desc: MutCoindDescriptor dl)
  -- We can ignore the lane analogously to `MutIndDescriptor.hypothesis`.
  (_: SingleLaneVarType)
  (x: Nat)
:
  SingleLaneExpr
:=
  desc.foldr (CoinductionDescriptor.hypothesis x) (.var .posLane x)

def MutCoindDescriptor.hypothesify
  (desc: MutCoindDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  .compl (expr.replaceComplZeroVars desc.hypothesis)

def MutCoindDescriptor.sub_hypothesify
  (desc: MutCoindDescriptor dl)
  (sub: dl.SubsetStx ctx (replaceComplZeroVars expr desc.hypothesis) b)
:
  let descMap: MutIndDescriptor dl :=
    desc.map CoinductionDescriptor.toInduction
  
  dl.SubsetStx ctx (replaceComplZeroVars expr descMap.hypothesis) b
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
          ((desc.expansion.toLane .posLane).replaceComplZeroVars fun _ x =>
            desc.hypothesis x (.var .posLane x))))
  :
    dl.SubsetStx ctx desc.left (.compl (.var .posLane desc.rite))
  :=
    mutCoinduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def simpleCoinduction
    (rite: Nat)
    (leftIsClean: Expr.IsClean left)
    (premise:
      DefList.SubsetStx
        dl
        ctx
        left
        (.compl
          (((dl.getDef rite).toLane .posLane).replaceComplZeroVars fun _ x =>
            if rite = x then .ir (.compl left) (.var .posLane x) else (.var .posLane x))))
  :
    dl.SubsetStx ctx left (.compl (.var .posLane rite))
  :=
    coinduction
      {
        left,
        rite,
        leftIsClean,
        expansion := dl.getDef rite,
        expandsInto := .rfl
      }
      premise
