import Mathlib.Logic.Basic

import Etst.WFC.Ch4_S0_MembershipPS

namespace Etst

variable {D: Type*}


def Cause.ofValPos
  (b c: Valuation D)
:
  Cause D
:= {
  contextIns := c.posMembers
  backgroundIns := b.posMembers
  backgroundOut := b.posNonmembers
}

def Cause.empty: Cause D := {
  contextIns := ∅
  backgroundIns := ∅
  backgroundOut := ∅
}

def Cause.eq:
  {a b: Cause D} →
  a.contextIns = b.contextIns →
  a.backgroundIns = b.backgroundIns →
  a.backgroundOut = b.backgroundOut →
  a = b

| ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl, rfl, rfl => rfl

structure Cause.IsSubset
  (a b: Cause D)
:
  Prop
where
  cinsLe: a.contextIns ⊆ b.contextIns
  binsLe: a.backgroundIns ⊆ b.backgroundIns
  boutLe: a.backgroundOut ⊆ b.backgroundOut

instance (D: Type*): HasSubset (Cause D) := ⟨Cause.IsSubset⟩

/-
  This definition differs from `IsCauseInapplicable` in that it
  is semantic instead of proof-theoretic.
-/
inductive Cause.IsInapplicable
  (cause: Cause D)
  (outSet: Set (ValConst D))
  (b: Valuation D)
:
  Prop

| blockedContextIns {d x}
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ outSet)
:
  IsInapplicable cause outSet b

| blockedBackgroundIns {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: ¬(b x).posMem d)
:
  IsInapplicable cause outSet b

| blockedBackgroundOut {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: (b x).defMem d)
:
  IsInapplicable cause outSet b

def Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy
  {cause: Cause D}
  {b c: Valuation D}
  (isApplicable: ¬ Cause.IsInapplicable cause c.nonmembers b)
:
  Cause.IsWeaklySatisfiedBy cause b c
:=
  open Cause.IsWeaklySatisfiedBy in
  {
    contextInsHold :=
      fun inCins =>
        byContradiction fun notPos =>
          isApplicable (blockedContextIns inCins notPos)
    backgroundInsHold :=
      fun inBins =>
        byContradiction fun notPos =>
          isApplicable (blockedBackgroundIns inBins notPos)
    backgroundOutHold :=
      fun inBout =>
        byContradiction fun isDef =>
          isApplicable (blockedBackgroundOut inBout isDef.dne)
  }

def Cause.IsWeaklySatisfiedBy.Not.toIsInapplicable
  {cause: Cause D}
  {b c: Valuation D}
  (notSat: ¬ Cause.IsWeaklySatisfiedBy cause b c)
:
  Cause.IsInapplicable cause c.nonmembers b
:=
  not_imp_comm.mp
    Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy
    notSat

def Cause.IsWeaklySatisfiedBy.toIsApplicable
  {cause b c}
  (isSat: Cause.IsWeaklySatisfiedBy cause b c)
  (outSet: Set (ValConst D))
  (outSetIsEmpty: ∀ {d x}, ⟨d, x⟩ ∈ outSet → ¬ (c x).posMem d)
:
  ¬ Cause.IsInapplicable cause outSet b

| IsInapplicable.blockedContextIns inCins inOutSet =>
  outSetIsEmpty inOutSet (isSat.contextInsHold inCins)

| IsInapplicable.blockedBackgroundIns inBins notPos =>
  notPos (isSat.backgroundInsHold inBins)

| IsInapplicable.blockedBackgroundOut inBout isDef =>
  isSat.backgroundOutHold inBout isDef

def Cause.IsWeaklySatisfiedBy.ofValPos
  (b c: Valuation D)
:
  (Cause.ofValPos b c).IsWeaklySatisfiedBy b c
:= {
  contextInsHold := id
  backgroundInsHold := id
  backgroundOutHold := id
}


noncomputable def IsWeakCause.ofValPos {expr b c d}
  (isPos: (expr.triIntp2 [] b c).posMem d)
:
  IsWeakCause (Cause.ofValPos b c) d expr
:=
  fun isSat =>
    BasicExpr.triIntp2_mono_apx_posMem
      (fun _ => {
        defLe :=
          fun _ isDef =>
            byContradiction (isSat.backgroundOutHold · isDef)
        posLe := fun _ => isSat.backgroundInsHold
      })
      (fun _ _ => isSat.contextInsHold)
      isPos

def IsWeakCause.isPosOfIsApplicable
  {cause d expr}
  (isCause: IsWeakCause cause d expr)
  {b c: Valuation Pair}
  (isApp: ¬ cause.IsInapplicable c.nonmembers b)
:
  (expr.triIntp2 [] b c).posMem d
:=
  isCause (Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy isApp)

def IsWeakCause.isInapplicableOfIsNonmember
  {cause d expr}
  (isCause: IsWeakCause cause d expr)
  {b c: Valuation Pair}
  (notPos: ¬(expr.triIntp2 [] b c).posMem d)
:
  cause.IsInapplicable c.nonmembers b
:=
  (not_imp_not.mpr (isPosOfIsApplicable isCause) notPos).dne
