-- TODO make this a chapter and add description
-- TODO document everything well. Don't be lazy.
-- Explain the important we have done in the previous
-- chapters, even to those who haven't read them.
-- Explain how and why we do the quotient construction,
-- and why set membership is respected by it.

import UniSet3.Ch9_S2_InternalExternalEquivalence

import Utils.BasicUtils
import Utils.Bisimilarity


inductive Truth3 where
| false
| true
| undetermined

def f3 := Truth3.false
def t3 := Truth3.true
def u3 := Truth3.undetermined

def Truth3.or: Truth3 → Truth3 → Truth3
| false, b => b
| a, false => a
| undetermined, undetermined => undetermined
| true, _ => true
| _, true => true

def Truth3.and: Truth3 → Truth3 → Truth3
| false, _ => false
| _, false => false
| undetermined, undetermined => undetermined
| true, b => b
| a, true => a


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
    then t3
    else if Triset.Inw elem ts
    then u3
    else f3
  
end Set3Pair
