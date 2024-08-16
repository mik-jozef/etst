/-
  In this chapter, we define a proof system for well-founded
  collections, and prove its soundness and completeness.
  
  To hide the tedious details of the proofs, we split the chapter
  into two sections/files, plus an additional file
  
  `/Utils/AProofSystem.lean`
  
  that holds most of the proofs and helper definitions. The
  interested reader is free to explore the details there, however
  they are not necessary for understanding the proof system itself.
-/

import WFC.Ch5_PairSalgebra
import WFC.Appx0_ExprRulesOfInference


/-
  `ValVar` encodes some (usage-specific) relation between a variable
  and an element. For example, it may be used to represent the
  assertion that a certain variable contains a certain element in
  some valuation.
  
  That the variable `x` contains the element `d` may be denoted
  as `d ∈ x`.
-/
structure ValVar (D: Type*) where
  d: D
  x: Nat

/-
  If expressions `a` and `c` contain an element `d`, then the
  expression `a ∩ (b ∪ c)` also contains that element. For this
  reason, we may call `d ∈ a ∧ d ∈ c` a cause of `d ∈ a ∪ (b ∪ c)`.
  
  We encode the causes as sets of `ValVar` instances. A cause
  consists of three such sets:
  - those that need to be present in the context,
  - those that need to be present in the background, and
  - those that need to be *absent* from the background.
-/
structure Cause (D: Type*) where
  contextIns: Set (ValVar D)
  backgroundIns: Set (ValVar D)
  backgroundOut: Set (ValVar D)


-- Defines when a cause is strongly satisfied by a pair of valuations.
structure Cause.IsStronglySatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
where
  contextInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → (c x).defMem d
  backgroundInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → (b x).defMem d
  backgroundOutHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → ¬(b x).posMem d

-- Defines when a cause is weakly satisfied by a pair of valuations.
structure Cause.IsWeaklySatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
where
  contextInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → (c x).posMem d
  backgroundInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → (b x).posMem d
  backgroundOutHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → ¬(b x).defMem d

/-
  `Is[X]Cause salg cause d expr` means that for every pair of
  valuations `(b, c)` that satisfies `cause`, `d ∈ expr` holds
  (with `b` and `c` serving as background and context valuations,
  respectively).
-/
def IsStrongCause
  (salg: Salgebra sig)
  (cause: Cause salg.D)
  (d: salg.D)
  (expr: Expr sig)
:
  Prop
:=
  {b c: Valuation salg.D} →
  cause.IsStronglySatisfiedBy b c →
  (expr.interpretation salg b c).defMem d

def IsWeakCause
  (salg: Salgebra sig)
  (cause: Cause salg.D)
  (d: salg.D)
  (expr: Expr sig)
:
  Prop
:=
  {b c: Valuation salg.D} →
  cause.IsWeaklySatisfiedBy b c →
  (expr.interpretation salg b c).posMem d


mutual
-- A workaround for this bug, can be deleted when fixed:
-- https://github.com/leanprover/lean4/issues/3242
variable {sig: Signature}

/-
  `Ins salg dl d x` means that `d` is (provably) a member of `x`
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
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  salg.D → Nat → Prop

| intro:
  (d: salg.D) →
  (x: Nat) →
  IsStrongCause salg cause d (dl.getDef x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → Ins salg dl d x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → Ins salg dl d x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → Out salg dl d x) →
  Ins salg dl d x


/-
  A cause is *provably* inapplicable for a given set S of value–
  variable pairs if for some element (d, x) of S, either:
  
  0. (d, x) is in the contextIns of the cause,
  1. (d, x) is in backgroundIns, and provably `d ∉ x`, or
  2. (d, x) is in backgroundOut, and provably `d ∈ x`.
  
  A set of value–variable pairs is called an empty cycle if all
  its elements have only inapplicable causes. Empty cycles formalize
  cyclic definitions like
  
      let A = B
      let B = A
  
  that do not contain any elements in the well-founded model.
-/
inductive IsCauseInapplicable
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Set (ValVar salg.D) →
  Cause salg.D →
  Prop

| blockedContextIns
  (cause: Cause salg.D)
  {d x}
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  IsCauseInapplicable salg dl cycle cause

| blockedBackgroundIns
  (cause: Cause salg.D)
  {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: Out salg dl d x)
:
  IsCauseInapplicable salg dl cycle cause

| blockedBackgroundOut
  (cause: Cause salg.D)
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: Ins salg dl d x)
:
  IsCauseInapplicable salg dl cycle cause

/-
  `Out salg dl d x` means that `d` is a definitive non-member of
  `x` in the well-founded model of `dl`.
  
  A `d` is provably a non-member of `x` if there exists an empty
  cycle containing the pair `(d, x)`.
-/
inductive Out
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  salg.D → Nat → Prop

| intro:
  (cycle: Set (ValVar salg.D)) →
  (isEmptyCycle:
    ∀ {d x cause},
    ⟨d, x⟩ ∈ cycle →
    IsWeakCause salg cause d (dl.getDef x) →
    IsCauseInapplicable salg dl cycle cause) →
  ⟨d, x⟩ ∈ cycle →
  Out salg dl d x
end

/-
  The chapter continues in the file `Ch6_S1_AProofSystem.lean`.
-/
