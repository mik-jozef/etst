-- TODO make this a chapter and add description
-- TODO document everything well. Don't be lazy.
-- Explain the important we have done in the previous
-- chapters, even to those who haven't read them.
-- Explain how and why we do the quotient construction,
-- and why set membership is respected by it.

import old.UniSet3.Ch9_S2_InternalExternalEquivalence

import old.Utils.BasicUtils
import old.Utils.Bisimilarity


inductive Truth3 where
| f3 -- false
| t3 -- true
| u3 -- undetermined

def Truth3.or: Truth3 → Truth3 → Truth3
| f3, b => b
| a, f3 => a
| u3, u3 => u3
| t3, _ => t3
| _, t3 => t3

def Truth3.and: Truth3 → Truth3 → Truth3
| f3, _ => f3
| _, f3 => f3
| u3, u3 => u3
| t3, b => b
| a, t3 => a

def Truth3.not: Truth3 → Truth3
| f3 => t3
| u3 => u3
| t3 => f3


def Truth3.and_eq_t3
  (eq: Truth3.and a b = t3)
:
  a = t3 ∧ b = t3
:=
  match a, b with
  | t3, t3 => ⟨rfl, rfl⟩

def Truth3.and_eq_f3
  (eq: Truth3.and a b = f3)
:
  a = f3 ∨ b = f3
:=
  match a, b with
  | _, f3 => Or.inr rfl
  | f3, _ => Or.inl rfl

def Truth3.or_eq_t3
  (eq: Truth3.or a b = t3)
:
  a = t3 ∨ b = t3
:=
  match a, b with
  | _, t3 => Or.inr rfl
  | t3, _ => Or.inl rfl

def Truth3.or_eq_f3
  (eq: Truth3.or a b = f3)
:
  a = f3 ∧ b = f3
:=
  match a, b with
  | f3, f3 => ⟨rfl, rfl⟩


structure TriRelation (T: Type*) where
  Rel: T → T → Truth3

inductive TriRelation.Expr (T: Type*) where



/-
  A system of trisets (or a universe) is a collection of elements,
  called trisets, together with a three-valued membership relation,
  that satisfies the following properties:

  TODO

  TODO sth like: In this volume, our goal is to construct an instance
  of `Trisets`.
-/
structure Trisets where
  Triset: Type*

  Mem: Triset → Triset → Truth3

  isExtensional:
    (∀ a b e: Triset, Mem e a = Mem e b) →
    a = b

  exEmpty: ∃ empty, ∀ s, Mem s empty = f3
  exUnion:
    ∀ s0 s1 elem, ∃ s,
      Mem elem s = (Mem elem s0).or (Mem elem s1)

  /-
    TODO should be redundant if we have comprehension. Also:
    restricted comprehension? should follow from replacement, right?
    full comprehension?
    replacement?
    infinity?
    power set?
  -/
  exIntersection:
    ∀ s0 s1 elem, ∃ s,
      Mem elem s = (Mem elem s0).and (Mem elem s1)


-- Is the intersection of two Triset models a triset model?
-- What about arbitrary intersection?
-- Is there a "least" model of trisets?


namespace Set3Pair
  def PreTriset := Nat

  -- Strong (a la "definite") membership, `a ∈ b`.
  def PreTriset.Ins (preElem preTs: PreTriset): Prop :=
    Set3.defMem (Pair.nthSet3 preElem) (Pair.fromNat preTs)

  -- Weak (a la "possible") membership, `a ∈? b`.
  def PreTriset.Inw (preElem preTs: PreTriset): Prop :=
    Set3.posMem (Pair.nthSet3 preElem) (Pair.fromNat preTs)

  open PreTriset

  inductive TransitionLabels where
  | ins
  | inw

  def transitionSystem:
    LabeledTransitionSystem PreTriset
  := {
    Labels := TransitionLabels
    isTransition := fun
      | a, .ins, b => a.Ins b
      | a, .inw, b => a.Inw b
  }

  def trisetSetoid: Setoid PreTriset where
    iseqv := isEquivalence transitionSystem

  def Triset := Quotient trisetSetoid

  structure TrisetIns
    (elem ts: Triset)
    (preElem preTs: PreTriset)
  :
    Prop
  where
    elemEq: elem = ⟦preElem⟧
    tsEq: ts = ⟦preTs⟧
    ins: preElem.Ins preTs

  structure TrisetInw
    (elem ts: Triset)
    (preElem preTs: PreTriset)
  :
    Prop
  where
    elemEq: elem = ⟦preElem⟧
    tsEq: ts = ⟦preTs⟧
    inw: preElem.Inw preTs

  def Triset.Ins (elem ts: Triset): Prop :=
    ∃ preElem preTs, TrisetIns elem ts preElem preTs

  def Triset.Inw (elem ts: Triset): Prop :=
    ∃ preElem preTs, TrisetInw elem ts preElem preTs

  noncomputable def Triset.Mem3 (elem ts: Triset): Truth3 :=
    if Triset.Ins elem ts
    then .t3
    else if Triset.Inw elem ts
    then .u3
    else .f3

end Set3Pair
