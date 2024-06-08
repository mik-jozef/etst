import Utils.BasicUtils


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


@[reducible] def Trisets.IsMem (Triset: Type u) :=
  Triset → Triset → Truth3

structure IsTrisetBisimulation.Related
  (isMem: Trisets.IsMem Triset)
  (Rel: Set (PairOf Triset))
  (r0: Rel)
  (t0 t1: Triset)
:
  Prop
:=
  isMemEq: isMem r0.val.fst t1 = tv
  tRelated: ⟨t0, t1⟩ ∈ Rel

def IsTrisetBisimulation
  (isMem: Trisets.IsMem Triset)
  (Rel: Set (PairOf Triset))
:
  Prop
:=
  ∀ (tv: Truth3)
    (r0: Rel)
    (t0: Triset),
  isMem r0.val.zth t0 = tv →
    ∃ t1: Triset,
      IsTrisetBisimulation.Related isMem Rel r0 t0 t1

def TrisetBisimilation
  (isMem: Trisets.IsMem Triset)
:=
  { Rel: Set (PairOf Triset) // IsTrisetBisimulation isMem Rel }

def IsBisimilar
  (isMem: Trisets.IsMem Triset)
  (a b: Triset)
:=
  ∃ tb: TrisetBisimilation isMem, ⟨a, b⟩ ∈ tb.val


/-
  A system of trisets (or a universe) is a collection of elements,
  called trisets, together with a three-valued membership relation,
  that satisfies the following properties:
  
  TODO
-/
structure Trisets where
  Triset: Type u
  isMem: Trisets.IsMem Triset
  
  isExtensional: ∀ a b: Triset, IsBisimilar isMem a b → a = b

  exEmpty: ∃ empty, ∀ s, isMem s empty = f3
  exUnion:
    ∀ s0 s1 elem, ∃ s,
      isMem elem s = (isMem elem s0).or (isMem elem s1)
  
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
      isMem elem s = (isMem elem s0).and (isMem elem s1)


def Trisets.fromPairs: Trisets := {
  Triset := sorry
  isMem := sorry
  
  isExtensional := sorry
  
  exEmpty := sorry
  exUnion := sorry
  exIntersection := sorry
}
