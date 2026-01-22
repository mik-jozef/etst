import Mathlib.Logic.Basic

import Etst.WFC.Ch4_S0_MembershipPS
import Etst.WFC.Utils.Cause

namespace Etst

variable
  {dl: DefList}
  {cycle cycleA cycleB: Set (ValConst Pair)}
  {cause causeA causeB: Cause Pair}


def ValConst.eq {D} {d0 d1: D} {x0 x1}:
  d0 = d1 → x0 = x1 → ValConst.mk d0 x0 = ⟨d1, x1⟩
| rfl, rfl => rfl

def ValConst.eqX {D} {d0 d1: D} {x0 x1} :
  @Eq (ValConst D) ⟨d0, x0⟩ ⟨d1, x1⟩ → x0 = x1
| rfl => rfl


def every_cause_inapplicable_preserves_definitive_nonmember
  (b c: Valuation Pair)
  (d: Pair)
  (expr: BasicExpr)
  (outSet: Set (ValConst Pair))
  (isEveryCauseInapplicable:
    {cause: Cause Pair} →
    IsWeakCause cause d expr →
    cause.IsInapplicable outSet b)
  (outSetIsEmpty:
    ∀ {d x}, ⟨d, x⟩ ∈ outSet → ¬ (c x).posMem d)
:
  ¬(expr.triIntp2 [] b c).posMem d
:=
  let isSat := Cause.IsWeaklySatisfiedBy.ofValPos b c
  let isApp := isSat.toIsApplicable outSet outSetIsEmpty
  
  isApp ∘ isEveryCauseInapplicable ∘ IsWeakCause.ofValPos

def empty_cycle_is_out
  (dl: DefList)
  (cycle: Set (ValConst Pair))
  (isEmptyCycle:
    ∀ {d x},
    ⟨d, x⟩ ∈ cycle →
    (cause: Cause Pair) →
    IsWeakCause cause d (dl.getDef x) →  
    cause.IsInapplicable cycle (dl.wfm))
  {d x}
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  ¬(dl.wfm x).posMem d
:=
  let _ := Valuation.ordStdLattice
  let wfm := dl.wfm
  let ⟨isFp, _⟩ := DefList.wfm_isLfpB dl
  
  isFp ▸
  OrderHom.lfpStage_induction
    (operatorC dl wfm)
    (fun v => ∀ vv ∈ cycle, ¬(v vv.x).posMem vv.d)
    (fun _n _isLim ih ⟨d, x⟩ inCycle =>
      (Valuation.ordStd.in_set_in_sup_posMem isLUB_iSup).nmp
        fun ⟨prev, ⟨⟨i, eqAtI⟩, dInPrev⟩⟩ =>
          let eq: (operatorC dl wfm).lfpStage i = prev := eqAtI
          ih i ⟨d, x⟩ inCycle (eq ▸ dInPrev))
    (fun n _notLim predLt ih ⟨d, x⟩ inCycle =>
      every_cause_inapplicable_preserves_definitive_nonmember
        wfm _ d
        (dl.getDef x)
        cycle
        (isEmptyCycle inCycle _)
        (ih ⟨n.pred, predLt⟩ _))
    ⟨d, x⟩
    inCycle


structure InsOutComplete
  (dl: DefList)
  (v: Valuation Pair)
:
  Prop
where
  insIsComplete:
    ∀ {d x}, (v x).defMem d → Ins dl d x
  outIsComplete:
    ∀ {d x}, ¬(v x).posMem d → Out dl d x

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
        (fun v => ∀ {d x}, (v x).defMem d → Ins dl d x)
        (fun _n _isLim ih _d _x isDefN =>
          let ⟨_v, ⟨m, (vEq: opC.lfpStage _ = _)⟩, inDefV⟩ :=
            (Valuation.ordStd.in_set_in_sup_defMem isLUB_iSup).mpr isDefN
          ih m (vEq ▸ inDefV))
        (fun n _notLim predLt ih d x isDefN =>
          let c := opC.lfpStage n.pred
          
          let cause: Cause Pair := {
            contextIns := fun ⟨d, x⟩ => (c x).defMem d
            backgroundIns := fun ⟨d, x⟩ => (b x).defMem d
            backgroundOut := fun ⟨d, x⟩ => ¬(b x).posMem d
          }
          
          let isCause: IsStrongCause cause d (dl.getDef x) :=
            fun {b1 _c1} isSat =>
              let isLe: b ⊑ b1 := fun _ => {
                defLe := fun _ => isSat.backgroundInsHold
                posLe := fun _ isPos =>
                  byContradiction (isSat.backgroundOutHold · isPos)
              }
              
              BasicExpr.triIntp2_mono_apx_defMem
                isLe
                (fun _ _ => isSat.contextInsHold)
                isDefN
          
          Ins.intro d x cause isCause
            (ih ⟨n.pred, predLt⟩)
            isComplete.insIsComplete
            isComplete.outIsComplete)
    outIsComplete :=
      Out.intro
        (fun ⟨d, x⟩ => ¬(operatorC.lfp dl b x).posMem d)
        (fun {dd xx} notPos _cause isCause =>
          let opC := operatorC dl b
          let lfp := operatorC.lfp dl b
          let isFp: _ = _ := (operatorC dl b).isFixedPt_lfp
          
          let notPos: ¬((opC lfp) xx).posMem dd := isFp ▸ notPos
          
          match isCause.isInapplicableOfIsNonmember notPos with
          | Cause.IsInapplicable.blockedContextIns inCins inCycle =>
            IsCauseInapplicable.blockedContextIns _ inCins inCycle
          | Cause.IsInapplicable.blockedBackgroundIns inBins notPos =>
            let isOut := isComplete.outIsComplete notPos
            IsCauseInapplicable.blockedBackgroundIns _ inBins isOut
          | Cause.IsInapplicable.blockedBackgroundOut inBout isIns =>
            let isIns := isComplete.insIsComplete isIns
            IsCauseInapplicable.blockedBackgroundOut _ inBout isIns)
  }

def completenessProofB
  (dl: DefList)
:
  InsOutComplete dl (dl.wfm)
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


def IsCauseInapplicable.toSuperCause
  (isInapp: IsCauseInapplicable dl cycle causeA)
  (isSuper: causeA ⊆ causeB)
:
  IsCauseInapplicable dl cycle causeB
:=
  match isInapp with
  | blockedContextIns _ inCins inCycle =>
    blockedContextIns _ (isSuper.cinsLe inCins) inCycle
  | blockedBackgroundIns _ inBins isOut =>
    blockedBackgroundIns _ (isSuper.binsLe inBins) isOut
  | blockedBackgroundOut _ inBout isIns =>
    blockedBackgroundOut _ (isSuper.boutLe inBout) isIns

def IsCauseInapplicable.toSuperCycle
  (isInapp: IsCauseInapplicable dl cycleA cause)
  (isSuper: cycleA ⊆ cycleB)
:
  IsCauseInapplicable dl cycleB cause
:=
  match isInapp with
  | blockedContextIns _ inCins inCycle =>
    blockedContextIns _ inCins (isSuper inCycle)
  | blockedBackgroundIns _ inBins isOut =>
    blockedBackgroundIns _ inBins isOut
  | blockedBackgroundOut _ inBout isIns =>
    blockedBackgroundOut _ inBout isIns

def IsCauseInapplicable.toSuper
  (isInapp: IsCauseInapplicable dl cycleA causeA)
  (isSuper: cycleA ⊆ cycleB)
  (isSuperCause: causeA ⊆ causeB)
:
  IsCauseInapplicable dl cycleB causeB
:=
  let isInapp := isInapp.toSuperCause isSuperCause
  isInapp.toSuperCycle isSuper
