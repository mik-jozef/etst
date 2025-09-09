import Mathlib.Logic.Basic

import Etst.WFC.Ch5_S0_AProofSystem

namespace Etst


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

def Cause.var (x: Nat) (d: D): Cause D := {
  contextIns := fun ⟨dd, xx⟩ => dd = d ∧ xx = x
  backgroundIns := ∅
  backgroundOut := ∅
}

def Cause.union (c1 c2: Cause D): Cause D := {
  contextIns := c1.contextIns ∪ c2.contextIns,
  backgroundIns := c1.backgroundIns ∪ c2.backgroundIns,
  backgroundOut := c1.backgroundOut ∪ c2.backgroundOut,
}

instance (D: Type*): Union (Cause D) := ⟨Cause.union⟩
instance (D: Type*): HasSubset (Cause D) := ⟨Cause.IsSubset⟩

def Cause.arbUn (f: I → Cause D): Cause D := {
  -- Originally defining these as follows was a mistake!
  -- 
  -- ```
  --   contextIns := ⋃ i, (f i).contextIns,
  --   backgroundIns := ⋃ i, (f i).backgroundIns,
  --   backgroundOut := ⋃ i, (f i).backgroundOut,
  -- ```
  -- 
  -- Instead of
  -- 
  --     { d: D | ∃ i: I, d ∈ f i } \,,
  -- 
  -- the arbitrary set union is defined in Mathlib as
  -- 
  --     { d: D | ∃ s: Set D, (∃ i: I, s = f i) ∧ d ∈ s } \,.
  -- 
  -- This is silly.
  
  contextIns := fun vv => ∃ i, vv ∈ (f i).contextIns,
  backgroundIns := fun vv => ∃ i, vv ∈ (f i).backgroundIns,
  backgroundOut := fun vv => ∃ i, vv ∈ (f i).backgroundOut,
}

def Cause.union_symm (c0 c1: Cause D): c0 ∪ c1 = c1 ∪ c0 :=
  Cause.eq
    (Set.union_comm c0.contextIns c1.contextIns)
    (Set.union_comm c0.backgroundIns c1.backgroundIns)
    (Set.union_comm c0.backgroundOut c1.backgroundOut)

def Cause.union_eq_right_sub
  {c0 c1: Cause D}
  (isSub: c1 ⊆ c0)
:
  c0 ∪ c1 = c0
:=
  Cause.eq
    (Set.union_eq_self_of_subset_right isSub.cinsLe)
    (Set.union_eq_self_of_subset_right isSub.binsLe)
    (Set.union_eq_self_of_subset_right isSub.boutLe)

def Cause.except
  (a b: Cause D)
:
  Cause D
:= {
  contextIns := a.contextIns \ b.contextIns
  backgroundIns := a.backgroundIns \ b.backgroundIns
  backgroundOut := a.backgroundOut \ b.backgroundOut
}

def Cause.exceptVar
  (cause: Cause D)
  (x: Nat)
:
  Cause D
:=
  cause.except {
    contextIns := fun vv => vv.x = x
    backgroundIns := fun vv => vv.x = x
    backgroundOut := fun vv => vv.x = x
  }

def Cause.exceptVar_is_sub
  (cause: Cause D)
  (x: Nat)
:
  cause.exceptVar x ⊆ cause
:= {
  cinsLe := fun _ => And.left
  binsLe := fun _ => And.left
  boutLe := fun _ => And.left
}

def Cause.exceptBound
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  Cause D
:=
  cause.except {
    contextIns := {⟨d, x⟩}
    backgroundIns := {⟨d, x⟩}
    backgroundOut := fun ⟨dd, xx⟩ => dd ≠ d ∧ xx = x
  }

def Cause.withBound
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  Cause D
:= {
  contextIns :=
    fun ⟨dd, xx⟩ =>
      Or
        (cause.contextIns ⟨dd, xx⟩ ∧ xx ≠ x)
        (dd = d ∧ xx = x)
  backgroundIns :=
    fun ⟨dd, xx⟩ =>
      Or
        (cause.backgroundIns ⟨dd, xx⟩ ∧ xx ≠ x)
        (dd = d ∧ xx = x)
  backgroundOut :=
    fun ⟨dd, xx⟩ =>
      Or
        (cause.backgroundOut ⟨dd, xx⟩ ∧ xx ≠ x)
        (dd ≠ d ∧ xx = x)
}

def Cause.withBound_cancels_previous
  (cause: Cause D)
  (x: Nat)
  (dA dB: D)
:
  (cause.withBound x dA).withBound x dB = cause.withBound x dB
:=
  Cause.eq
    (funext fun ⟨_dd, _xx⟩ =>
      propext
        (Iff.intro
          (fun inCinsAB =>
            inCinsAB.elim
              (fun ⟨inCinsA, xNeq⟩ =>
                inCinsA.elim
                  Or.inl
                  (False.elim ∘ xNeq ∘ And.right))
              Or.inr)
          (fun inCinsB =>
            inCinsB.elim
              (fun ⟨inCins, xNeq⟩ =>
                Or.inl ⟨(Or.inl ⟨inCins, xNeq⟩), xNeq⟩)
              Or.inr)))
    (funext fun ⟨_dd, _xx⟩ =>
      propext
        (Iff.intro
          (fun inBinsAB =>
            inBinsAB.elim
              (fun ⟨inBinsA, xNeq⟩ =>
                inBinsA.elim
                  Or.inl
                  (False.elim ∘ xNeq ∘ And.right))
              Or.inr)
          (fun inBinsB =>
            inBinsB.elim
              (fun ⟨inBins, xNeq⟩ =>
                Or.inl ⟨(Or.inl ⟨inBins, xNeq⟩), xNeq⟩)
              Or.inr)))
    (funext fun ⟨_dd, _xx⟩ =>
      propext
        (Iff.intro
          (fun inBoutAB =>
            inBoutAB.elim
              (fun ⟨inBoutA, xNeq⟩ =>
                inBoutA.elim
                  Or.inl
                  (False.elim ∘ xNeq ∘ And.right))
              Or.inr)
          (fun inBoutB =>
            inBoutB.elim
              (fun ⟨inBout, xNeq⟩ =>
                Or.inl ⟨(Or.inl ⟨inBout, xNeq⟩), xNeq⟩)
              Or.inr)))

def Cause.inCinsOfInWithAndNotBound
  {cause: Cause D}
  (inCinsWith: ⟨d, x⟩ ∈ (cause.withBound xB dB).contextIns)
  (xNeq: x ≠ xB)
:
  ⟨d, x⟩ ∈ cause.contextIns
:=
  inCinsWith.elim
    (fun ⟨inCins, _⟩ => inCins)
    (fun ⟨_, xEq⟩ => absurd xEq xNeq)

def Cause.inBinsOfInWithAndNotBound
  {cause: Cause D}
  (inBinsWith: ⟨d, x⟩ ∈ (cause.withBound xB dB).backgroundIns)
  (xNeq: x ≠ xB)
:
  ⟨d, x⟩ ∈ cause.backgroundIns
:=
  inBinsWith.elim
    (fun ⟨inBins, _⟩ => inBins)
    (fun ⟨_, xEq⟩ => absurd xEq xNeq)

def Cause.inBoutOfInWithAndNotBound
  {cause: Cause D}
  (inBoutWith: ⟨d, x⟩ ∈ (cause.withBound xB dB).backgroundOut)
  (xNeq: x ≠ xB)
:
  ⟨d, x⟩ ∈ cause.backgroundOut
:=
  inBoutWith.elim
    (fun ⟨inBout, _⟩ => inBout)
    (fun ⟨_, xEq⟩ => absurd xEq xNeq)

def Cause.background
  (cause: Cause D)
:
  Cause D
:= {
  contextIns := {}
  backgroundIns := cause.backgroundIns
  backgroundOut := cause.backgroundOut
}


structure Cause.SatisfiesBoundVar
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  Prop
where
  cinsSat:
    ∀ vv ∈ cause.contextIns, vv.x = x → vv.d = d
  binsSat:
    ∀ vv ∈ cause.backgroundIns, vv.x = x → vv.d = d
  boutSat:
    ∀ vv ∈ cause.backgroundOut, vv.x = x → vv.d ≠ d

def Cause.SatisfiesBoundVar.ninBinsBout
  {cause: Cause D}
  (sat: cause.SatisfiesBoundVar x dBound)
  (d: D)
:
  ⟨d, x⟩ ∉ cause.backgroundIns ∨ ⟨d, x⟩ ∉ cause.backgroundOut
:=
  if h: ⟨d, x⟩ ∈ cause.backgroundIns then
    let dEq := sat.binsSat ⟨d, x⟩ h rfl
    Or.inr (sat.boutSat _ · rfl dEq)
  else
    Or.inl h

def Cause.SatisfiesBoundVar.union
  {causeL causeR: Cause D}
  (satL: causeL.SatisfiesBoundVar x dBound)
  (satR: causeR.SatisfiesBoundVar x dBound)
:
  (causeL ∪ causeR).SatisfiesBoundVar x dBound
:= {
  cinsSat := fun
    | _, Or.inl inCins => satL.cinsSat _ inCins
    | _, Or.inr inCins => satR.cinsSat _ inCins
  binsSat := fun
    | _, Or.inl inBins => satL.binsSat _ inBins
    | _, Or.inr inBins => satR.binsSat _ inBins
  boutSat := fun
    | _, Or.inl inBout => satL.boutSat _ inBout
    | _, Or.inr inBout => satR.boutSat _ inBout
}

def Cause.SatisfiesBoundVar.leWithBound
  {cause: Cause D}
  (sat: cause.SatisfiesBoundVar x d)
:
  cause ⊆ cause.withBound x d
:= {
  cinsLe :=
    fun vv inCins =>
      if h: vv.x = x then
        Or.inr ⟨sat.cinsSat vv inCins h, h⟩
      else
        Or.inl ⟨inCins, h⟩
  binsLe :=
    fun vv inBins =>
      if h: vv.x = x then
        Or.inr ⟨sat.binsSat vv inBins h, h⟩
      else
        Or.inl ⟨inBins, h⟩
  boutLe :=
    fun vv inBout =>
      if h: vv.x = x then
        Or.inr ⟨sat.boutSat vv inBout h, h⟩
      else
        Or.inl ⟨inBout, h⟩
}

def Cause.SatisfiesBoundVar.toSubCause
  {cause: Cause D}
  (sat: cause.SatisfiesBoundVar x d)
  (isLe: subcause ⊆ cause)
:
  subcause.SatisfiesBoundVar x d
:= {
  cinsSat :=
    fun vv inCins xEq =>
      sat.cinsSat vv (isLe.cinsLe inCins) xEq
  binsSat :=
    fun vv inBins xEq =>
      sat.binsSat vv (isLe.binsLe inBins) xEq
  boutSat :=
    fun vv inBout xEq =>
      sat.boutSat vv (isLe.boutLe inBout) xEq
}


/-
  This definition differs from `IsCauseInapplicable` in that it
  is semantic instead of proof-theoretic.
-/
inductive Cause.IsInapplicable
  (cause: Cause D)
  (outSet: Set (ValVar D))
  (b: Valuation D)
:
  Prop

| blockedContextIns
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ outSet)
:
  IsInapplicable cause outSet b

| blockedBackgroundIns
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: ¬(b x).posMem d)
:
  IsInapplicable cause outSet b

| blockedBackgroundOut
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
  {b c: Valuation D}
  (isSat: Cause.IsWeaklySatisfiedBy cause b c)
  (outSet: Set (ValVar D))
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

def Cause.IsWeaklySatisfiedBy.union
  (isSatLeft: Cause.IsWeaklySatisfiedBy causeLeft b c)
  (isSatRite: Cause.IsWeaklySatisfiedBy causeRite b c)
:
  (causeLeft ∪ causeRite).IsWeaklySatisfiedBy b c
:= {
  contextInsHold :=
    fun inCins =>
      inCins.elim
        isSatLeft.contextInsHold
        isSatRite.contextInsHold,
  backgroundInsHold :=
    fun inBins =>
      inBins.elim
        isSatLeft.backgroundInsHold
        isSatRite.backgroundInsHold,
  backgroundOutHold :=
    fun inBout =>
      inBout.elim
        isSatLeft.backgroundOutHold
        isSatRite.backgroundOutHold,
}

def Cause.IsWeaklySatisfiedBy.ofSuper
  (isSat: Cause.IsWeaklySatisfiedBy causeSuper b c)
  (le: cause ⊆ causeSuper)
:
  Cause.IsWeaklySatisfiedBy cause b c
:= {
  contextInsHold :=
    fun inCins => isSat.contextInsHold (le.cinsLe inCins)
  backgroundInsHold :=
    fun inBins => isSat.backgroundInsHold (le.binsLe inBins)
  backgroundOutHold :=
    fun inBout => isSat.backgroundOutHold (le.boutLe inBout)
}

def Cause.IsWeaklySatisfiedBy.elimUnL
  (isSat: Cause.IsWeaklySatisfiedBy (causeL ∪ causeR) b c)
:
  Cause.IsWeaklySatisfiedBy causeL b c
:= {
  contextInsHold := isSat.contextInsHold ∘ Or.inl
  backgroundInsHold := isSat.backgroundInsHold ∘ Or.inl
  backgroundOutHold := isSat.backgroundOutHold ∘ Or.inl
}

def Cause.IsWeaklySatisfiedBy.elimUnR
  (isSat: Cause.IsWeaklySatisfiedBy (causeL ∪ causeR) b c)
:
  Cause.IsWeaklySatisfiedBy causeR b c
:= {
  contextInsHold := isSat.contextInsHold ∘ Or.inr
  backgroundInsHold := isSat.backgroundInsHold ∘ Or.inr
  backgroundOutHold := isSat.backgroundOutHold ∘ Or.inr
}

def Cause.IsWeaklySatisfiedBy.elimArbUn
  {f: I → Cause D}
  (isSat: Cause.IsWeaklySatisfiedBy (Cause.arbUn f) b c)
  (i: I)
:
  Cause.IsWeaklySatisfiedBy (f i) b c
:= {
  contextInsHold := isSat.contextInsHold ∘ fun vv => ⟨_, vv⟩
  backgroundInsHold := isSat.backgroundInsHold ∘ fun vv => ⟨_, vv⟩
  backgroundOutHold := isSat.backgroundOutHold ∘ fun vv => ⟨_, vv⟩
}


noncomputable def IsWeakCause.ofValPos
  (isPos: (expr.interpretation salg [] b c).posMem d)
:
  IsWeakCause salg (Cause.ofValPos b c) d expr
:=
  fun isSat =>
    Expr.interpretation_mono_apx_posMem
      (fun _ => {
        defLe :=
          fun _ isDef =>
            byContradiction (isSat.backgroundOutHold · isDef)
        posLe := fun _ => isSat.backgroundInsHold
      })
      (fun _ _ => isSat.contextInsHold)
      isPos

def IsWeakCause.isPosOfIsApplicable
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  (isCause: IsWeakCause salg cause d expr)
  {b c: Valuation salg.D}
  (isApp: ¬ cause.IsInapplicable c.nonmembers b)
:
  (expr.interpretation salg [] b c).posMem d
:=
  isCause (Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy isApp)

def IsWeakCause.isInapplicableOfIsNonmember
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  (isCause: IsWeakCause salg cause d expr)
  {b c: Valuation salg.D}
  (notPos: ¬(expr.interpretation salg [] b c).posMem d)
:
  cause.IsInapplicable c.nonmembers b
:=
  (not_imp_not.mpr (isPosOfIsApplicable isCause) notPos).dne
