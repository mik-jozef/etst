import Etst.Subtyping.ProofSystem

namespace Etst
open PairExpr


def InductionDescriptor.Invariant
  (desc: InductionDescriptor dl)
  (wfm v: Valuation Pair)
:=
  IsDefSubset (v desc.left) (desc.rite.intp [] wfm)

def CoinductionDescriptor.Invariant
  (desc: CoinductionDescriptor dl)
  (wfm v: Valuation Pair)
:=
  IsDefSubset (desc.left.intp [] wfm) (v desc.rite).cpl


def MutIndDescriptor.var_le_hypothesify
  (desc: MutIndDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  v x ≤ (desc.hypothesify (var x)).intp bv dl.wfm
:=
  match desc with
  | [] => v_le x
  | head :: (rest: MutIndDescriptor dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail
      (P := fun (desc: InductionDescriptor dl) => desc.Invariant dl.wfm v)
      inv
    if h: head.left = x then
      if_pos h ▸
      {
        defLe := fun _ inX =>
          let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ (h ▸ inX.toPos)
          insIr
            (head.riteIsClean.changeBvDefMem inRite)
            ((rest.var_le_hypothesify invTail v_le).defLe inX)
        posLe := fun _ inX =>
          let inRite := inv ⟨0, Nat.zero_lt_succ _⟩ (h ▸ inX)
          inwIr
            (head.riteIsClean.changeBvPosMem inRite.toPos)
            ((rest.var_le_hypothesify invTail v_le).posLe inX)
      }
    else
      if_neg h ▸
      rest.var_le_hypothesify invTail v_le

def MutIndDescriptor.le_hypothesify
  (desc: MutIndDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  expr.intp2 bv dl.wfm v
    ≤
  (desc.hypothesify expr).intp bv dl.wfm
:=
  let _ := Set3.ordStdLattice
  match expr with
  | .var _ => var_le_hypothesify desc inv v_le
  | .bvar _ => le_rfl
  | .op _o _args =>
    Expr.inter_mono_std_op fun _param =>
      desc.le_hypothesify inv v_le
  | .cpl _ => le_rfl
  | .arbUn _ =>
    Expr.inter_mono_std_arbUn fun _d =>
      desc.le_hypothesify inv v_le
  | .arbIr _ =>
    Expr.inter_mono_std_arbIr fun _d =>
      desc.le_hypothesify inv v_le


def MutCoindDescriptor.var_hypothesify_le
  (desc: MutCoindDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
:
  v x ≤ intp (desc.hypothesis x) bv dl.wfm
:=
  match desc with
  | [] => v_le x
  | desc :: (rest: MutCoindDescriptor dl) =>
    show _ ≤ intp (if _ then _ else _) bv dl.wfm from
    let invTail := List.Index.indexedTail
      (P := fun (desc: CoinductionDescriptor dl) => desc.Invariant dl.wfm v)
      inv
    if h: desc.rite = x then
      if_pos h ▸
      {
        defLe := fun _ insX =>
          insIr
            (fun inwLeft =>
              let inwLeft := desc.leftIsClean.changeBvPosMem inwLeft
              inv ⟨0, Nat.zero_lt_succ _⟩ inwLeft (h ▸ insX.toPos))
            ((rest.var_hypothesify_le invTail v_le).defLe insX)
        posLe := fun _ insX =>
          inwIr
            (fun insLeft =>
              let insLeft := desc.leftIsClean.changeBvDefMem insLeft
              inv ⟨0, Nat.zero_lt_succ _⟩ insLeft.toPos (h ▸ insX))
            ((rest.var_hypothesify_le invTail v_le).posLe insX)
      }
    else
      if_neg h ▸
      rest.var_hypothesify_le invTail (fun _ => v_le _)

def MutCoindDescriptor.hypothesify_le
  (desc: MutCoindDescriptor dl)
  (inv: ∀ (i: desc.Index), desc[i].Invariant dl.wfm v)
  (v_le: v ≤ dl.wfm)
  {expr: PairExpr}
:
  (intp (expr.replacePosVars desc.hypothesis) bv dl.wfm).cpl
    ≤
  (expr.intp2 bv dl.wfm v).cpl
:=
  let _ := Set3.ordStdLattice
  let rec helper (bv: List Pair): (expr: PairExpr) →
    expr.intp2 bv dl.wfm v
      ≤
    intp (expr.replacePosVars desc.hypothesis) bv dl.wfm

  | .var _ => desc.var_hypothesify_le inv v_le
  | .bvar _x => le_rfl
  | .op _o args =>
    Expr.inter_mono_std_op fun param =>
      helper bv (args param)
  | .cpl _ => le_rfl
  | .arbUn body =>
    Expr.inter_mono_std_arbUn fun d =>
      helper (d :: bv) body
  | .arbIr body =>
    Expr.inter_mono_std_arbIr fun d =>
      helper (d :: bv) body
  
  Set3.LeStd.compl_le_compl (helper bv expr)


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

def MutIndDescriptor.isSound
  (desc: MutIndDescriptor dl)
  (premisesHold:
    (i: desc.Index) →
    dl.IsDefSubset (desc.hypothesify desc[i].expansion) desc[i].rite)
  (i: desc.Index)
:
  dl.IsDefSubset desc[i].exprLeft desc[i].exprRite
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
        let lePremiseL := desc.le_hypothesify ihPred predStageLe
        let leExp := desc[i].expandsInto.lfpStage_le_std [] n.pred
        premisesHold i (lePremiseL.posLe (leExp.posLe isPos)))
  
  by rw [←eq] at isDefSub; exact isDefSub i

def MutCoindDescriptor.isSound
  (desc: MutCoindDescriptor dl)
  (premisesHold:
    (i: desc.Index) →
    dl.IsDefSubset desc[i].left (desc.hypothesify desc[i].expansion))
  (i: desc.Index)
:
  dl.IsDefSubset desc[i].exprLeft desc[i].exprRite
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
          p ∈ ((operatorC _ dl dl.wfm).lfpStage m desc[i].rite).posMem
        :=
          vEq ▸ s3Eq ▸ atStage
        ih m i isPos pIn)
      (fun n notLim predLt ih i _ isPos =>
        let ihPred := ih ⟨n.pred, predLt⟩
        let op := operatorC pairSalgebra dl dl.wfm
        let predStage := op.lfpStage n.pred
        let predStageLe := dl.lfpStage_le_wfm_std pairSalgebra n.pred
        let expLe := desc[i].expandsInto.lfpStage_le_std [] n.pred
        let lePremiseR := desc.hypothesify_le ihPred predStageLe
        expLe.notPosLe (lePremiseR.defLe (premisesHold i isPos))
      )

  by rw [←eq] at isDefSub; exact isDefSub i
