-- TODO make this a chapter and add description
-- TODO document everything well. Don't be lazy.
-- Explain the important we have done in the previous
-- chapters, even to those who haven't read them.
-- Explain how and why we do the quotient construction,
-- and why set membership is respected by it.

import UniSet3.Ch9_S2_InternalExternalEquivalence

import Utils.BasicUtils
import Utils.Bisimilarity


structure PairOf (A: Type u) where
  zth: A
  fst: A


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


namespace Set3Pair
  def PreTriset := Nat
  
  -- Strong (a la "definite") membership, `a ∈ b`.
  def PreTriset.Ins (elem pts: PreTriset): Prop :=
    Set3.defMem (Pair.nthSet3 elem) (Pair.fromNat pts)
  
  -- Weak (a la "possible") membership, `a ∈? b`.
  def PreTriset.Inw (elem pts: PreTriset): Prop :=
    Set3.posMem (Pair.nthSet3 elem) (Pair.fromNat pts)
  
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
  
  
  def PreTriset.insOfInsRel
    (bisim: Bisimulation transitionSystem)
    (relA: bisim.Rel a0 a1)
    (relB: bisim.Rel b0 b1)
    (ins0: Ins a0 b0)
  :
    Ins a1 b1
  :=
    let ⟨bM, relBM, insBM⟩ :=
      bisim.isSimulation relA (label := .ins) ins0
    
    sorry
  
  def Triset.insRespects
    (a0 b0 a1 b1: PreTriset)
    (relA: IsBisimilar transitionSystem a0 a1)
    (relB: IsBisimilar transitionSystem b0 b1)
  :
    Ins a0 b0 = Ins a1 b1
  :=
    let ⟨bisimA, relA⟩ := relA
    let ⟨bisimB, relB⟩ := relB
    
    let bisim := bisimA.union bisimB
    
    Eq.propIntro
      (insOfInsRel bisim (Or.inl relA) (Or.inr relB))
      (insOfInsRel bisim.converse (Or.inl relA) (Or.inr relB))
  
  def Triset.ins:
    Triset → Triset → Prop
  :=
    Quotient.lift₂ Ins insRespects
end Set3Pair


/-
  A system of trisets (or a universe) is a collection of elements,
  called trisets, together with a three-valued membership relation,
  that satisfies the following properties:
  
  TODO
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
