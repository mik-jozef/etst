/-
  # Chapter 4: A Proof System for Membership in Well-Founded Collections
  
  In this chapter, we define a proof system for showing membership
  of individual elements in particular well-founded collections,
  and prove its soundness and completeness.
  
  To hide the tedious details of the proofs, we split the chapter
  into two sections/files, with the latter importing additional
  utility files that hold most of the proofs and helper definitions.
  The interested reader is free to explore the details there, however
  they are not necessary for understanding the proof system itself.
-/

import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.RulesOfInference

namespace Etst

variable {D: Type*}


-- See `Cause` below.
structure BackgroundCause (D: Type*) where
  backgroundIns: Set (ValConst D)
  backgroundOut: Set (ValConst D)

/-
  If (under some valuation) expressions `a` and `c` contain an
  element `d`, then the expression `a ∩ (b ∪ c)` also contains
  that element. For this reason, we may call `d ∈ a ∧ d ∈ c`
  a cause of `d ∈ a ∪ (b ∪ c)`.
  
  We encode the causes as sets of `ValConst` instances. A cause
  consists of three such sets:
  - those that need to be present in the context,
  - those that need to be present in the background, and
  - those that need to be *absent* from the background.
  
  Note that it never happens that a value would need to be absent
  from context in order to cause something.
-/
structure Cause (D: Type*) extends BackgroundCause D where
  contextIns: Set (ValConst D)

def BackgroundCause.toCause
  (cause: BackgroundCause D)
:
  Cause D
:= {
  contextIns := {}
  backgroundIns := cause.backgroundIns
  backgroundOut := cause.backgroundOut
}

instance: Coe (BackgroundCause D) (Cause D) := ⟨BackgroundCause.toCause⟩


structure Cause.IsStronglySatisfiedByBackground
  (cause: Cause D)
  (b: Valuation D)
:
  Prop
where
  backgroundInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → (b x).defMem d
  backgroundOutHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → ¬(b x).posMem d

/-
  Defines when a cause is strongly satisfied by a context-background
  pair of valuations.
-/
structure Cause.IsStronglySatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
extends
  Cause.IsStronglySatisfiedByBackground cause b
where
  contextInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → (c x).defMem d


structure Cause.IsWeaklySatisfiedByBackground
  (cause: Cause D)
  (b: Valuation D)
:
  Prop
where
  backgroundInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → (b x).posMem d
  backgroundOutHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → ¬(b x).defMem d

/-
  Defines when a cause is weakly satisfied by a context-background
  pair of valuations. The properties are all inherited from the
  above two structures.
-/
structure Cause.IsWeaklySatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
extends
  Cause.IsWeaklySatisfiedByBackground cause b
where
  contextInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → (c x).posMem d

/-
  `Is[X]Cause cause d expr` means that for every pair of
  valuations `(b, c)` that satisfies `cause`, `d ∈ expr` holds
  (with `b` and `c` serving as background and context valuations,
  respectively).
-/
def IsStrongCause
  (cause: Cause Pair)
  (d: Pair)
  (expr: BasicExpr)
:
  Prop
:=
  {b c: Valuation Pair} →
  cause.IsStronglySatisfiedBy b c →
  expr.triIntp2Def [] b c d

def IsWeakCause
  (cause: Cause Pair)
  (d: Pair)
  (expr: BasicExpr)
:
  Prop
:=
  {b c: Valuation Pair} →
  cause.IsWeaklySatisfiedBy b c →
  expr.triIntp2Pos [] b c d


mutual
/-
  `Ins dl d x` means that `d` is (provably) a member of `x`
  (in the well-founded model of `dl`).
  
  If there exists a strong cause of `d ∈ dl.getDef x` such that
  for every value–variable pair `(d, x)`:
  
  0. `(d, x) ∈ cause.contextIns` implies `d` is provably a member
     of `x`,
  1. `(d, x) ∈ cause.backgroundIns` also implies `d` is provably
     a member of `x`, and
  2. `(d, x) ∈ cause.backgroundOut` implies `d` is provably a
     non-member of `x`,
  
  then `d` is provably a member of `x`.
-/
inductive Ins
  (dl: DefList)
:
  Pair → Nat → Prop

| intro:
  (d: Pair) →
  (x: Nat) →
  (cause: Cause Pair) →
  IsStrongCause cause d (dl.getDef x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → Ins dl d x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → Ins dl d x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → Out dl d x) →
  Ins dl d x


/-
  A cause is *provably* inapplicable for a given set S of value–
  constant pairs if for some element (d, x) of S, either:
  
  0. (d, x) is in the contextIns of the cause,
  1. (d, x) is in backgroundIns, and provably `d ∉ x`, or
  2. (d, x) is in backgroundOut, and provably `d ∈ x`.
  
  A set of value–constant pairs is called an empty cycle if all
  its elements have only inapplicable causes. Empty cycles formalize
  cyclic definitions like
  
      let A = B
      let B = A
  
  that do not contain any elements in the well-founded model.
-/
inductive IsCauseInapplicable
  (dl: DefList)
:
  Set (ValConst Pair) →
  Cause Pair →
  Prop

| blockedContextIns
  (cause: Cause Pair)
  {d x}
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  {cycle} (inCycle: ⟨d, x⟩ ∈ cycle)
:
  IsCauseInapplicable dl cycle cause

| blockedBackgroundIns {cycle}
  (cause: Cause Pair)
  {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: Out dl d x)
:
  IsCauseInapplicable dl cycle cause

| blockedBackgroundOut {cycle}
  (cause: Cause Pair)
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: Ins dl d x)
:
  IsCauseInapplicable dl cycle cause

/-
  `Out dl d x` means that `d` is a definitive non-member of
  `x` in the well-founded model of `dl`.
  
  A `d` is provably a non-member of `x` if there exists an empty
  cycle containing the pair `(d, x)`.
-/
inductive Out
  (dl: DefList)
:
  Pair → Nat → Prop

| intro {d x}:
  (cycle: Set (ValConst Pair)) →
  (isEmptyCycle:
    ∀ {d x},
    ⟨d, x⟩ ∈ cycle →
    (cause: Cause Pair) →
    IsWeakCause cause d (dl.getDef x) →
    IsCauseInapplicable dl cycle cause) →
  ⟨d, x⟩ ∈ cycle →
  Out dl d x
end

/-
  The chapter continues in the file `Ch4_S1_MembershipPS.lean`.
-/
