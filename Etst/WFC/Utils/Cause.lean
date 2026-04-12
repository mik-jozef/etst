import Mathlib.Logic.Basic

import Etst.WFC.Ch4_S0_MembershipPs

namespace Etst

variable {D: Type*}


def Cause.eq:
  {a b: Cause D} →
  a.cins = b.cins →
  a.bout = b.bout →
  a = b

| ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

def Cause.empty: Cause D := {
  cins _ := ∅
  bout _ := ∅
}

def Cause.const
  (x: Nat)
  (d: D)
:
  Cause D
:= {
  cins xx dd := xx = x ∧ dd = d
  bout _ := ∅
}

def Cause.ofValDef
  (b c: Valuation D)
:
  Cause D
:= {
  cins := c.defMembers
  bout := b.defNonMembers
}

def Cause.ofValPos
  (b c: Valuation D)
:
  Cause D
:= {
  cins := c.posMembers
  bout := b.posNonMembers
}

structure Cause.IsSubset
  (a b: Cause D)
:
  Prop
where
  cinsLe: a.cins ≤ b.cins
  boutLe: a.bout ≤ b.bout

instance (D: Type*): HasSubset (Cause D) := ⟨Cause.IsSubset⟩

/-
  This definition differs from `IsCauseInapplicable` in that it
  is semantic instead of proof-theoretic.
-/
inductive Cause.IsInapplicable
  (cause: Cause D)
  (outSet inSet: Nat → Set D)
:
  Prop
|
  blockedCins {x d}
  (inCins: cause.cins x d)
  (inCycle: outSet x d)
:
  IsInapplicable cause outSet inSet
|
  blockedBout {x d}
  (inBout: cause.bout x d)
  (isIns: inSet x d)
:
  IsInapplicable cause outSet inSet

def Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy
  {cause: Cause D}
  {b c: Valuation D}
  (isApplicable:
    ¬ Cause.IsInapplicable cause c.defNonMembers b.defMembers)
:
  Cause.IsWeaklySatisfiedBy cause b c
:=
  open Cause.IsWeaklySatisfiedBy in
  {
    cinsSat :=
      fun inCins =>
        byContradiction fun notPos =>
          isApplicable (blockedCins inCins notPos)
    boutSat :=
      fun inBout =>
        byContradiction fun isDef =>
          isApplicable (blockedBout inBout isDef.dne)
  }

def Cause.IsWeaklySatisfiedBy.toIsApplicable
  {cause b c}
  (isSat: Cause.IsWeaklySatisfiedBy cause b c)
  (outSet: Nat → Set D)
  (outSetIsEmpty: ∀ {x d}, outSet x d → ¬ (c x).posMem d)
:
  ¬ Cause.IsInapplicable cause outSet b.defMembers
|
  .blockedCins inCins inOutSet =>
    outSetIsEmpty inOutSet (isSat.cinsSat inCins)
|
  .blockedBout inBout isDef =>
    isSat.boutSat inBout isDef

def Cause.IsWeaklySatisfiedBy.ofValPos
  (b c: Valuation D)
:
  (Cause.ofValPos b c).IsWeaklySatisfiedBy b c
:= {
  cinsSat := id
  boutSat := id
}


def Cause.IsWeakCauseFv.ofValPos {expr fv b c d}
  (isPos: (expr.triIntp2 fv b c).posMem d)
:
  (Cause.ofValPos b c).IsWeakCauseFv fv expr d
:=
  fun _ _ isSat =>
    BasicExpr.triIntp2_mono_std_posMem
      (fun _ _ isDef => byContradiction (isSat.boutSat · isDef))
      (fun _ _ => isSat.cinsSat)
      isPos

def Cause.IsStrongCauseFv.ofValDef {expr fv b c d}
  (isDef: (expr.triIntp2 fv b c).defMem d)
:
  (Cause.ofValDef b c).IsStrongCauseFv fv expr d
:=
  fun _ _ isSat =>
    BasicExpr.triIntp2_mono_std_defMem
      (fun _ _ isDef => byContradiction (isSat.boutSat · isDef))
      (fun _ _ => isSat.cinsSat)
      isDef


def Cause.IsWeakCauseFv.isPosOfIsApplicable {fv d expr}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv expr d)
  {b c}
  (isApp: ¬ cause.IsInapplicable c.defNonMembers b.defMembers)
:
  (expr.triIntp2 fv b c).posMem d
:=
  isCause (Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy isApp)

def Cause.IsWeakCauseFv.isInapplicableOfIsNonmember {fv d expr}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv expr d)
  {b c: Valuation Pair}
  (notPos: ¬(expr.triIntp2 fv b c).posMem d)
:
  cause.IsInapplicable c.defNonMembers b.defMembers
:=
  (not_imp_not.mpr (isPosOfIsApplicable isCause) notPos).dne


/-
  The least valuation in the approximation order that strongly
  satisfies the background part of a cause.
-/
def Cause.leastBackgroundApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := ∅
    posMem := compl ∘ cause.bout x
    defLePos := nofun
  }

/-
  The least valuation in the approximation order that strongly
  satisfies the context part of a cause.
-/
def Cause.leastContextApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := cause.cins x
    posMem := Set.univ
    defLePos _ _ := trivial
  }

def Cause.leastValsApxAreSat
  (cause: Cause D)
:
  cause.IsStronglySatisfiedBy
    (cause.leastBackgroundApx)
    (cause.leastContextApx)
:= {
  cinsSat := id
  boutSat := Function.eval
}


/-
  A maximal valuation in the approximation order that weakly
  satisfies the background part of a cause.
-/
def Cause.maximalBackgroundApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := compl ∘ cause.bout x
    posMem := compl ∘ cause.bout x
    defLePos _ := id
  }

/-
  A maximal valuation in the approximation order that weakly
  satisfies the context part of a cause.
-/
def Cause.maximalContextApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := cause.cins x
    posMem := cause.cins x
    defLePos _ := id
  }

def Cause.maximalValsApxAreSat
  (cause: Cause D)
:
  cause.IsWeaklySatisfiedBy
    (cause.maximalBackgroundApx)
    (cause.maximalContextApx)
:= {
  cinsSat := id
  boutSat := Function.eval
}


def Cause.IsWeakCauseFv.const {fv x d}:
  IsWeakCauseFv (Cause.const x d) fv (.const x) d
:=
  fun _ _ isSat => isSat.cinsSat ⟨rfl, rfl⟩

def Cause.IsWeakCauseFv.constElim {fv x d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.const x) d)
:
  cause.cins x d
:=
  byContradiction fun notInCins =>
    let isSat := cause.maximalValsApxAreSat
    notInCins (isCause isSat)

def Cause.IsStrongCauseFv.const {fv x d}:
  IsStrongCauseFv (Cause.const x d) fv (.const x) d
:=
  fun _ _ isSat => isSat.cinsSat ⟨rfl, rfl⟩

def Cause.IsStrongCauseFv.constElim {fv x d}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv (.const x) d)
:
  cause.cins x d
:=
  byContradiction fun notInCins =>
    let isSat := cause.leastValsApxAreSat
    notInCins (isCause isSat)


def Cause.IsWeakCauseFv.noneElim {fv d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.none) d)
  {P: Prop}
:
  P
:=
  SingleLaneExpr.inNoneElim
    (isCause cause.maximalValsApxAreSat)

def Cause.IsStrongCauseFv.noneElim {fv d}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv (.none) d)
  {P: Prop}
:
  P
:=
  SingleLaneExpr.inNoneElim
    (isCause cause.leastValsApxAreSat)
