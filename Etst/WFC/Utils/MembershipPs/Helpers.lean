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
  (p: Pair)
  (outSet: Nat → Set Pair)
  (isEveryCauseInapplicable:
    {cause: Cause Pair} →
    cause.IsWeakCause expr p →
    cause.IsInapplicable outSet b.defMembers)
  (outSetIsEmpty:
    ∀ {x p}, outSet x p → ¬ (c x).posMem p)
:
  ¬(expr.triIntp2 [] b c).posMem p
:=
  let isSat := Cause.IsWeaklySatisfiedBy.ofValPos b c
  let isApp := isSat.toIsApplicable outSet outSetIsEmpty
  
  isApp ∘ isEveryCauseInapplicable ∘ Cause.IsWeakCauseFv.ofValPos

def empty_cycle_is_out
  (dl: DefList)
  (cycle: Nat → Set Pair)
  (isEmptyCycle:
    ∀ {x p},
    cycle x p →
    (cause: Cause Pair) →
    cause.IsWeakCause (dl.getDef x) p →
    cause.IsInapplicable cycle dl.wfm.defMembers)
  {x p} (inCycle: cycle x p)
:
  ¬(dl.wfm x).posMem p
:=
  let _ := Valuation.ordStdLattice
  let wfm := dl.wfm
  let ⟨isFp, _⟩ := DefList.wfm_isLfpB dl
  
  isFp ▸
  OrderHom.lfpStage_induction
    (operatorC dl wfm)
    (fun v => ∀ {x p}, cycle x p → ¬(v x).posMem p)
    (fun _n _isLim ih _ _ inCycle =>
      (Valuation.ordStd.in_set_in_sup_posMem isLUB_iSup).nmp
        fun ⟨prev, ⟨⟨i, eqAtI⟩, pInPrev⟩⟩ =>
          let eq: (operatorC dl wfm).lfpStage i = prev := eqAtI
          ih i inCycle (eq ▸ pInPrev))
    (fun n _notLim predLt ih x p inCycle =>
      every_cause_inapplicable_preserves_definitive_nonmember
        wfm
        _
        (dl.getDef x)
        p
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
    ∀ {x p}, (v x).defMem p → DefList.Ins dl x p
  outIsComplete:
    ∀ {x p}, ¬(v x).posMem p → DefList.Out dl x p

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
        (fun v => ∀ {x p}, (v x).defMem p → Ins dl x p)
        (fun _n _isLim ih _x _p isDefN =>
          let ⟨_v, ⟨m, (vEq: opC.lfpStage _ = _)⟩, inDefV⟩ :=
            (Valuation.ordStd.in_set_in_sup_defMem isLUB_iSup).mpr isDefN
          ih m (vEq ▸ inDefV))
        (fun n _notLim predLt ih x p isDefN =>
          let c := opC.lfpStage n.pred
          
          let cause: Cause Pair := {
            cins x p := (c x).defMem p
            bout x p := ¬(b x).posMem p
          }
          
          let isCause: cause.IsStrongCause (dl.getDef x) p :=
            fun _ _ isSat =>
              BasicExpr.triIntp2_mono_std_defMem
                (fun _ _ isDef =>
                  byContradiction (isSat.boutSat · isDef))
                (fun _ _ => isSat.cinsSat)
                isDefN
          
          Ins.intro x p cause isCause
            (ih ⟨n.pred, predLt⟩)
            isComplete.outIsComplete)
    outIsComplete :=
      Out.intro
        (fun x p => ¬(operatorC.lfp dl b x).posMem p)
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
