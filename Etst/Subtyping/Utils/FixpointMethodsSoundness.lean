import Etst.Subtyping.SubsetStx
import Etst.Subtyping.Utils.IsLaneConstrained

namespace Etst
open PairExpr
open SingleLaneExpr


def DefList.lfpStage_le_wfm_std
  (salg: Salgebra sig)
  (dl: DefList sig)
  (n: Ordinal)
:
  let _ := Valuation.ordStdLattice
  (operatorC salg dl (dl.wfm salg)).lfpStage n ≤ dl.wfm salg
:= by
  intro
  conv => rhs; rw [dl.wfm_eq_lfpC salg]
  exact (operatorC salg dl (dl.wfm salg)).lfpStage_le_lfp n


def InductionDescriptor.Invariant
  (desc: InductionDescriptor dl)
  (wfm v: Valuation Pair)
:=
  Set.Subset (v desc.left).posMem (desc.rite.intp [] wfm)

def CoinductionDescriptor.Invariant
  (desc: CoinductionDescriptor dl)
  (wfm v: Valuation Pair)
:=
  Set.Subset (desc.left.intp [] wfm) (v desc.rite).defMem.compl


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
        inIr
          (IsClean.changeBv head.riteIsClean inRite)
          (rest.var_le_hypothesify invTail v_le inX)
    else
      if_neg h ▸
      rest.var_le_hypothesify invTail v_le

def MutIndDescriptor.le_hypothesify
  (desc: MutIndDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (isConstrained: expr.IsPosVarLaneOnly .posLane)
  (v_le: v ≤ dl.wfm)
:
  expr.intp2 bv dl.wfm v
    ≤
  (desc.hypothesify expr).intp bv dl.wfm
:=
  match expr with
  | .var .posLane _ => var_le_hypothesify desc inv v_le
  | .bvar _ => le_rfl
  | .op _ _ =>
    inter_mono_std_op fun param =>
      desc.le_hypothesify inv (isConstrained.elimOp param) v_le
  | .compl _ => le_rfl
  | .arbUn _ =>
    inter_mono_std_arbUn fun _d =>
      desc.le_hypothesify inv isConstrained.elimArbUn v_le
  | .arbIr _ =>
    inter_mono_std_arbIr fun _d =>
      desc.le_hypothesify inv isConstrained.elimArbIr v_le


def MutCoindDescriptor.var_hypothesify_le
  (desc: MutCoindDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  (v x).defMem ≤ intp (desc.hypothesis .defLane x) bv dl.wfm
:=
  match desc with
  | [] => (v_le x).defLe
  | desc :: (rest: MutCoindDescriptor dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail
      (P := fun (desc: CoinductionDescriptor dl) => desc.Invariant dl.wfm v)
      inv
    if h: desc.rite = x then
      if_pos h ▸
      fun _ inX =>
        inIr
          (fun inLeft =>
            let inLeft := IsClean.changeBv desc.leftIsClean inLeft
            inv ⟨0, Nat.zero_lt_succ _⟩ inLeft (h ▸ inX))
          (rest.var_hypothesify_le invTail v_le inX)
    else
      if_neg h ▸
      rest.var_hypothesify_le invTail (fun _ => v_le _)

def MutCoindDescriptor.hypothesify_le
  (desc: MutCoindDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (isConstrained: IsPosVarLaneOnly .defLane expr)
  (v_le: v ≤ dl.wfm)
:
  (intp (expr.replaceComplZeroVars desc.hypothesis) bv dl.wfm).compl
    ≤
  (expr.intp2 bv dl.wfm v).compl
:=
  let rec helper
    (bv: List Pair)
    {expr: SingleLanePairExpr}
    (isConstrained: IsPosVarLaneOnly .defLane expr)
  :
    Set.Subset
      (expr.intp2 bv dl.wfm v)
      (intp (expr.replaceComplZeroVars desc.hypothesis) bv dl.wfm)
  :=
    match expr with
    | .var .defLane _ => desc.var_hypothesify_le inv v_le
    | .bvar _ => fun _ => id
    | .op _ _ =>
      inter_mono_std_op fun param =>
        helper bv (isConstrained.elimOp param)
    | .compl _ => fun _ => id
    | .arbUn _ =>
      inter_mono_std_arbUn fun d =>
        helper (d :: bv) isConstrained.elimArbUn
    | .arbIr _ =>
      inter_mono_std_arbIr fun d =>
        helper (d :: bv) isConstrained.elimArbIr
  
  compl_le_compl (helper bv isConstrained)


def MutIndDescriptor.isSound
  (desc: MutIndDescriptor dl)
  (premisesHold:
    (i: desc.Index) →
    dl.Subset
      (desc.hypothesify (desc[i].expansion.toLane .posLane))
      desc[i].rite)
  (i: desc.Index)
:
  dl.Subset desc[i].exprLeft desc[i].exprRite
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm = (operatorC pairSalgebra dl dl.wfm).lfp :=
    dl.wfm_eq_lfpC pairSalgebra
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC pairSalgebra dl dl.wfm)
      (fun v =>
        ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
      (fun n isLim ih i p ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, atStage⟩ =>
        let vEq: (operatorC pairSalgebra dl dl.wfm).lfpStage m = v := vEq
        let s3Eq: v _ = s3 := s3Eq
        let pIn:
          p ∈ ((operatorC _ dl dl.wfm).lfpStage m desc[i].left).posMem
        :=
          vEq ▸ s3Eq ▸ atStage
        ih m i pIn)
      (fun n notLim predLt ih i _ isPos =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC pairSalgebra dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std pairSalgebra n.pred
        let isLaneOnly := BasicExpr.toIsLaneOnly _
        let lePremiseL := desc.le_hypothesify ihPred isLaneOnly predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std [] n.pred
        premisesHold i (lePremiseL (leExp.posLe isPos)))
  
  by rw [←eq] at isDefSub; exact isDefSub i

def MutCoindDescriptor.isSound
  (desc: MutCoindDescriptor dl)
  (premisesHold:
    (i: desc.Index) →
    dl.Subset
      desc[i].left
      (desc.hypothesify (desc[i].expansion.toLane .defLane)))
  (i: desc.Index)
:
  dl.Subset desc[i].exprLeft desc[i].exprRite
:=
  let := Valuation.ordStdLattice
  let eq: dl.wfm = (operatorC pairSalgebra dl dl.wfm).lfp :=
    dl.wfm_eq_lfpC pairSalgebra
  
  let isDefSub :=
    OrderHom.lfpStage_induction
      (operatorC pairSalgebra dl dl.wfm)
      (fun v =>
        ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
      (fun n isLim ih i p isPos ⟨⟨s3, ⟨v, ⟨m, vEq⟩, s3Eq⟩⟩, atStage⟩ =>
        let vEq: (operatorC pairSalgebra dl dl.wfm).lfpStage m = v := vEq
        let s3Eq: v _ = s3 := s3Eq
        let pIn:
          p ∈ ((operatorC _ dl dl.wfm).lfpStage m desc[i].rite).defMem
        :=
          vEq ▸ s3Eq ▸ atStage
        ih m i isPos pIn)
      (fun n notLim predLt ih i _ isPos =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC pairSalgebra dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std pairSalgebra n.pred
        let expLe := desc[i].expandsInto.lfpStage_le_std [] n.pred
        let isLaneOnly := BasicExpr.toIsLaneOnly _
        let lePremiseR := desc.hypothesify_le ihPred isLaneOnly predStageLe
        expLe.notDefLe (lePremiseR (premisesHold i isPos))
      )
  
  by rw [←eq] at isDefSub; exact isDefSub i
