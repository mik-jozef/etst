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


/-
  If (under some valuation) the constants `a` and `c` contain an
  element `d`, then the expression `a & (b | c)` also contains
  that element. For this reason, we may call `d ∈ a ∧ d ∈ c`
  a cause of `d ∈ a & (b | c)`.
  
  We encode the causes as sets of elements that need to exist in
  the respective constants. There are two kinds of such sets:
  - those that need to be present in the context, and
  - those that need to be absent in the background.
-/
structure Cause (D: Type*) where
  cins: Nat → Set D
  bout: Nat → Set D

structure Cause.IsStronglySatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
where
  cinsSat:
    ∀ {x d}, cause.cins x d → (c x).defMem d
  boutSat:
    ∀ {x d}, cause.bout x d → ¬(b x).posMem d

structure Cause.IsWeaklySatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
where
  cinsSat:
    ∀ {x d}, cause.cins x d → (c x).posMem d
  boutSat:
    ∀ {x d}, cause.bout x d → ¬(b x).defMem d

/-
  `Is[X]Cause cause d expr` means that for every pair of
  valuations `(b, c)` that satisfies `cause`, `d ∈ expr` holds
  (with `b` and `c` serving as background and context valuations,
  respectively).
-/
def Cause.IsStrongCauseFv
  (cause: Cause Pair)
  (fv: List Pair)
  (expr: BasicExpr)
  (d: Pair)
:
  Prop
:=
  ⦃b c: Valuation Pair⦄ →
  cause.IsStronglySatisfiedBy b c →
  expr.triIntp2Def fv b c d

def Cause.IsWeakCauseFv
  (cause: Cause Pair)
  (fv: List Pair)
  (expr: BasicExpr)
  (d: Pair)
:
  Prop
:=
  ⦃b c: Valuation Pair⦄ →
  cause.IsWeaklySatisfiedBy b c →
  expr.triIntp2Pos fv b c d

abbrev Cause.IsStrongCause
  (cause: Cause Pair)
  (expr: BasicExpr)
  (d: Pair)
:
  Prop
:=
  IsStrongCauseFv cause [] expr d

abbrev Cause.IsWeakCause
  (cause: Cause Pair)
  (expr: BasicExpr)
  (d: Pair)
:
  Prop
:=
  IsWeakCauseFv cause [] expr d


mutual
/-
  `Ins dl x d` means that `d` is (provably) a member of `x`
  (in the well-founded model of `dl`).
  
  If there exists a strong cause of `d ∈ dl.getDef x` such that
  for every value–variable pair `(d, x)`:
  
  0. `cause.cins x d` implies `d` is provably a member of `x`, and
  1. `cause.bout x d` implies `d` is provably a non-member
    of `x`,
  
  then `d` is provably a member of `x`.
-/
inductive DefList.Ins
  (dl: DefList)
:
  Nat → Pair → Prop

| intro:
  (x: Nat) →
  (d: Pair) →
  (cause: Cause Pair) →
  cause.IsStrongCause (dl.getDef x) d →
  (∀ {x d}, cause.cins x d → Ins dl x d) →
  (∀ {x d}, cause.bout x d → Out dl x d) →
  Ins dl x d


/-
  A cause is *provably* inapplicable for a given set S of constant-
  value pairs if for some `x` and `d`, either
  
  0. `cause.cins x d` and `d` is in S, or
  1. `cause.bout x d` and `d` is provably a member of `x`.
  
  A set of constant-value pairs is called an empty cycle if all
  its elements have only inapplicable causes. Empty cycles formalize
  cyclic definitions like
  
      let A = B
      let B = A
  
  that do not contain any elements in the well-founded model.
-/
inductive DefList.IsCauseInapplicable
  (dl: DefList)
:
  (Nat → Set Pair) →
  Cause Pair →
  Prop
|
  blockedCins
  (cause: Cause Pair)
  {x d} (inContext: cause.cins x d)
  {cycle} (inCycle: cycle x d)
:
  IsCauseInapplicable dl cycle cause
|
  blockedBout {cycle}
  (cause: Cause Pair)
  {x d} (inBackground: cause.bout x d)
  (isIns: Ins dl x d)
:
  IsCauseInapplicable dl cycle cause

/-
  `Out dl x d` means that `d` is a definitive non-member of
  `x` in the well-founded model of `dl`.
  
  A `d` is provably a non-member of `x` if there exists an empty
  cycle containing the pair `(d, x)`.
  
  TODO: Could `Out` be defined coinductively?
    Also see the commit that added this todo for more info.
-/
inductive DefList.Out
  (dl: DefList)
:
  Nat → Pair → Prop
|
  intro {x d}
  (cycle: Nat → Set Pair)
  (isEmptyCycle:
    ∀ {x d},
    cycle x d →
    (cause: Cause Pair) →
    cause.IsWeakCause (dl.getDef x) d →
    dl.IsCauseInapplicable cycle cause)
  (incycle: cycle x d)
:
  Out dl x d
end

/-
  The chapter continues in the file `Ch4_S1_MembershipPs.lean`.
-/
