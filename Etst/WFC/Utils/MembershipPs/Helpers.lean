import Mathlib.Logic.Basic

import Etst.WFC.Ch4_S0_MembershipPs
import Etst.WFC.Utils.Cause

namespace Etst

variable
  {dl: DefList}
  {cycle cycleA cycleB: Nat → Set Pair}
  {cause causeA causeB: Cause Pair}


def every_cause_inapplicable_preserves_definitive_nonmember
  (b c: Valuation Pair)
  (expr: BasicExpr)
  (d: Pair)
  (outSet: Nat → Set Pair)
  (isEveryCauseInapplicable:
    {cause: Cause Pair} →
    cause.IsWeakCause expr d →
    cause.IsInapplicable outSet b.defMembers)
  (outSetIsEmpty:
    ∀ {x d}, outSet x d → ¬ (c x).posMem d)
:
  ¬(expr.triIntp2 [] b c).posMem d
:=
  let isSat := Cause.IsWeaklySatisfiedBy.ofValPos b c
  let isApp := isSat.toIsApplicable outSet outSetIsEmpty
  
  isApp ∘ isEveryCauseInapplicable ∘ Cause.IsWeakCauseFv.ofValPos

def empty_cycle_is_out
  (dl: DefList)
  (cycle: Nat → Set Pair)
  (isEmptyCycle:
    ∀ {x d},
    cycle x d →
    (cause: Cause Pair) →
    cause.IsWeakCause (dl.getDef x) d →  
    cause.IsInapplicable cycle dl.wfm.defMembers)
  {x d} (inCycle: cycle x d)
:
  ¬(dl.wfm x).posMem d
:=
  let _ := Valuation.ordStdLattice
  let wfm := dl.wfm
  let ⟨isFp, _⟩ := DefList.wfm_isLfpB dl
  
  isFp ▸
  OrderHom.lfpStage_induction
    (operatorC dl wfm)
    (fun v => ∀ {x d}, cycle x d → ¬(v x).posMem d)
    (fun _n _isLim ih _ _ inCycle =>
      (Valuation.ordStd.in_set_in_sup_posMem isLUB_iSup).nmp
        fun ⟨prev, ⟨⟨i, eqAtI⟩, dInPrev⟩⟩ =>
          let eq: (operatorC dl wfm).lfpStage i = prev := eqAtI
          ih i inCycle (eq ▸ dInPrev))
    (fun n _notLim predLt ih x d inCycle =>
      every_cause_inapplicable_preserves_definitive_nonmember
        wfm
        _
        (dl.getDef x)
        d
        cycle
        (isEmptyCycle inCycle _)
        (ih ⟨n.pred, predLt⟩))
    inCycle


structure InsOutComplete
  (dl: DefList)
  (v: Valuation Pair)
:
  Prop
where
  insIsComplete:
    ∀ {x d}, (v x).defMem d → DefList.Ins dl x d
  outIsComplete:
    ∀ {x d}, ¬(v x).posMem d → DefList.Out dl x d

open DefList in
def completenessProofC {dl b}
  (isComplete: InsOutComplete dl b)
:
  InsOutComplete dl (operatorC.lfp dl b)
:=
  let _ := Valuation.ordStdLattice
  let opC := operatorC dl b
  {
    insIsComplete :=
      opC.lfpStage_induction
        (fun v => ∀ {x d}, (v x).defMem d → Ins dl x d)
        (fun _n _isLim ih _x _d isDefN =>
          let ⟨_v, ⟨m, (vEq: opC.lfpStage _ = _)⟩, inDefV⟩ :=
            (Valuation.ordStd.in_set_in_sup_defMem isLUB_iSup).mpr isDefN
          ih m (vEq ▸ inDefV))
        (fun n _notLim predLt ih x d isDefN =>
          let c := opC.lfpStage n.pred
          
          let cause: Cause Pair := {
            cins x d := (c x).defMem d
            bout x d := ¬(b x).posMem d
          }
          
          let isCause: cause.IsStrongCause (dl.getDef x) d :=
            fun _ _ isSat =>
              BasicExpr.triIntp2_mono_std_defMem
                (fun _ _ isDef =>
                  byContradiction (isSat.boutSat · isDef))
                (fun _ _ => isSat.cinsSat)
                isDefN
          
          Ins.intro x d cause isCause
            (ih ⟨n.pred, predLt⟩)
            isComplete.outIsComplete)
    outIsComplete :=
      Out.intro
        (fun x d => ¬(operatorC.lfp dl b x).posMem d)
        (fun {xx dd} notPos _cause isCause =>
          let opC := operatorC dl b
          let lfp := operatorC.lfp dl b
          let isFp: _ = _ := (operatorC dl b).isFixedPt_lfp
          
          let notPos: ¬((opC lfp) xx).posMem dd := isFp ▸ notPos
          
          match isCause.isInapplicableOfIsNonmember notPos with
          | .blockedCins inCins inCycle =>
            .blockedCins _ inCins inCycle
          | .blockedBout inBout isDef =>
            .blockedBout _ inBout (isComplete.insIsComplete isDef))
  }

def completenessProofB
  (dl: DefList)
:
  InsOutComplete dl dl.wfm
:=
  let _ := Valuation.ordApx
  let opB := operatorB dl
  
  opB.lfpStageCc_induction
    isCcApx
    (InsOutComplete dl)
    (fun _n _isLim ih isChain => {
      insIsComplete isDefN :=
        let isLub := (isCcApx isChain).choose_spec
        let ⟨_v, ⟨m, (vEq: opB.lfpStageCc _ _ = _)⟩, dInV⟩ :=
          (Valuation.ordApx.in_set_in_sup_defMem isLub).mpr
            isDefN
        (ih m).insIsComplete (vEq ▸ dInV)
      outIsComplete notPosN :=
        let isSup := (isCcApx isChain).choose_spec
        let notAllPos :=
          (Valuation.ordApx.in_set_in_sup_posMem isSup).nmpr notPosN
        let ⟨_v, ⟨m, (vEq: opB.lfpStageCc _ _ = _)⟩, dNpos⟩ :=
          notAllPos.toEx fun _ p => Classical.not_imp.mp p
        (ih m).outIsComplete (vEq ▸ dNpos)
    })
    (fun n _notLim predLt ih =>
      completenessProofC (ih ⟨n.pred, predLt⟩))
