import Mathlib.Logic.Basic

import Etst.WFC.Ch5_S0_AProofSystem
import Etst.WFC.Utils.Cause

namespace Etst


def ValVar.eq: d0 = d1 → x0 = x1 → ValVar.mk d0 x0 = ⟨d1, x1⟩
| rfl, rfl => rfl

def ValVar.eqX: @Eq (ValVar D) ⟨d0, x0⟩ ⟨d1, x1⟩ → x0 = x1
| rfl => rfl


def every_cause_inapplicable_preserves_definitive_nonmember
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (d: salg.D)
  (expr: Expr sig)
  (outSet: Set (ValVar salg.D))
  (isEveryCauseInapplicable:
    {cause: Cause salg.D} →
    IsWeakCause salg cause d expr →
    cause.IsInapplicable outSet b)
  (outSetIsEmpty:
    ∀ {d x}, ⟨d, x⟩ ∈ outSet → ¬ (c x).posMem d)
:
  ¬(expr.interpretation salg [] b c).posMem d
:=
  let isSat := Cause.IsWeaklySatisfiedBy.ofValPos b c
  let isApp := isSat.toIsApplicable outSet outSetIsEmpty
  
  isApp ∘ isEveryCauseInapplicable ∘ IsWeakCause.ofValPos

def empty_cycle_is_out
  (salg: Salgebra sig)
  (dl: DefList sig)
  (cycle: Set (ValVar salg.D))
  (isEmptyCycle:
    ∀ {d x},
    ⟨d, x⟩ ∈ cycle →
    (cause: Cause salg.D) →
    IsWeakCause salg cause d (dl.getDef x) →  
    cause.IsInapplicable cycle (dl.wfm salg))
  {d x}
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  ¬(dl.wfm salg x).posMem d
:=
  let _ := Valuation.ordStdLattice
  let wfm := dl.wfm salg
  let ⟨isFp, _⟩ := DefList.wfm_isLfpB salg dl
  
  isFp ▸
  OrderHom.lfpStage_induction
    (operatorC salg dl wfm)
    (fun v => ∀ vv ∈ cycle, ¬(v vv.x).posMem vv.d)
    (fun _n _isLim ih ⟨d, x⟩ inCycle =>
      (Valuation.ordStd.in_set_in_sup_posMem isLUB_iSup).nmp
        fun ⟨prev, ⟨⟨i, eqAtI⟩, dInPrev⟩⟩ =>
          let eq: (operatorC salg dl wfm).lfpStage i = prev := eqAtI
          ih i ⟨d, x⟩ inCycle (eq ▸ dInPrev))
    (fun n _notLim predLt ih ⟨d, x⟩ inCycle =>
      every_cause_inapplicable_preserves_definitive_nonmember
        salg wfm _ d
        (dl.getDef x)
        cycle
        (isEmptyCycle inCycle _)
        (ih ⟨n.pred, predLt⟩ _))
    ⟨d, x⟩
    inCycle


structure InsOutComplete
  (salg: Salgebra sig)
  (dl: DefList sig)
  (v: Valuation salg.D)
:
  Prop
where
  insIsComplete:
    ∀ {d x}, (v x).defMem d → Ins salg dl d x
  outIsComplete:
    ∀ {d x}, ¬(v x).posMem d → Out salg dl d x

def completenessProofC
  (isComplete: InsOutComplete salg dl b)
:
  InsOutComplete salg dl (operatorC.lfp salg dl b)
:=
  let _ := Valuation.ordStdLattice
  -- TODO do I need this variable?
  let opC := operatorC salg dl b
  -- let isMono {v0 v1: Valuation salg.D} (isLe: v0 ≤ v1) :=
  --   operatorC.mono_std salg dl b isLe
  
  {
    insIsComplete :=
      opC.lfpStage_induction
        (fun v => ∀ {d x}, (v x).defMem d → Ins salg dl d x)
        (fun _n _isLim ih _d _x isDefN =>
          let ⟨_v, ⟨m, (vEq: opC.lfpStage _ = _)⟩, inDefV⟩ :=
            (Valuation.ordStd.in_set_in_sup_defMem isLUB_iSup).mpr isDefN
          ih m (vEq ▸ inDefV))
        (fun n _notLim predLt ih d x isDefN =>
          let c := opC.lfpStage n.pred
          
          let cause: Cause salg.D := {
            contextIns := fun ⟨d, x⟩ => (c x).defMem d
            backgroundIns := fun ⟨d, x⟩ => (b x).defMem d
            backgroundOut := fun ⟨d, x⟩ => ¬(b x).posMem d
          }
          
          let isCause: IsStrongCause salg cause d (dl.getDef x) :=
            fun {b1 _c1} isSat =>
              let isLe: b ⊑ b1 := fun _ => {
                defLe := fun _ => isSat.backgroundInsHold
                posLe := fun _ isPos =>
                  byContradiction (isSat.backgroundOutHold · isPos)
              }
              
              Expr.interpretation_mono_apx_defMem
                isLe
                (fun _ _ => isSat.contextInsHold)
                isDefN
          
          Ins.intro d x cause isCause
            (ih ⟨n.pred, predLt⟩)
            isComplete.insIsComplete
            isComplete.outIsComplete)
    outIsComplete :=
      Out.intro
        (fun ⟨d, x⟩ => ¬(operatorC.lfp salg dl b x).posMem d)
        (fun {dd xx} notPos _cause isCause =>
          let opC := operatorC salg dl b
          let lfp := operatorC.lfp salg dl b
          let isFp: _ = _ := (operatorC salg dl b).isFixedPt_lfp
          
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
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  InsOutComplete salg dl (dl.wfm salg)
:=
  let _ := Valuation.ordApx
  let opB := operatorB salg dl
  
  opB.lfpStageCc_induction
    isCcApx
    (InsOutComplete salg dl)
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
  (isInapp: IsCauseInapplicable salg dl cycle causeA)
  (isSuper: causeA ⊆ causeB)
:
  IsCauseInapplicable salg dl cycle causeB
:=
  match isInapp with
  | blockedContextIns _ inCins inCycle =>
    blockedContextIns _ (isSuper.cinsLe inCins) inCycle
  | blockedBackgroundIns _ inBins isOut =>
    blockedBackgroundIns _ (isSuper.binsLe inBins) isOut
  | blockedBackgroundOut _ inBout isIns =>
    blockedBackgroundOut _ (isSuper.boutLe inBout) isIns

def IsCauseInapplicable.toSuperCycle
  (isInapp: IsCauseInapplicable salg dl cycleA cause)
  (isSuper: cycleA ⊆ cycleB)
:
  IsCauseInapplicable salg dl cycleB cause
:=
  match isInapp with
  | blockedContextIns _ inCins inCycle =>
    blockedContextIns _ inCins (isSuper inCycle)
  | blockedBackgroundIns _ inBins isOut =>
    blockedBackgroundIns _ inBins isOut
  | blockedBackgroundOut _ inBout isIns =>
    blockedBackgroundOut _ inBout isIns

def IsCauseInapplicable.toSuper
  (isInapp: IsCauseInapplicable salg dl cycleA causeA)
  (isSuper: cycleA ⊆ cycleB)
  (isSuperCause: causeA ⊆ causeB)
:
  IsCauseInapplicable salg dl cycleB causeB
:=
  let isInapp := isInapp.toSuperCause isSuperCause
  isInapp.toSuperCycle isSuper
