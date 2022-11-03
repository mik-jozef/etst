/-
  Defines sets and related definiitons.
-/

import PartialOrder

open Classical


noncomputable def choiceEx {P: T → Prop} (ex: ∃ t: T, P t): { t: T // P t } :=
  let nonempty: Nonempty { t: T // P t } :=
    match ex with
    | ⟨t, prop⟩ => ⟨t, prop⟩
  choice nonempty


def Set.{u} (T : Type u) := T → Prop

instance: Membership T (Set T) where
  mem := fun (t: T) (s: Set T) => s t

instance: Coe (Set T) Type where
  coe s := { t: T // t ∈ s }

instance: LE (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b

infix:50 " ⊆ " => LE.le


theorem Set.ext {a b : Set D} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))


instance: PartialOrder (Set D) where
  le (a: Set D) (b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  refl (_: Set D) := fun _: D => id
  
  antisymm (a b: Set D) :=
    fun (ab: a ≤ b) (ba: ∀ d: D, d ∈ b → d ∈ a) =>
      let abElem: ∀ d: D, d ∈ a ↔ d ∈ b := fun (s: D) => Iff.intro (ab s) (ba s);
      Set.ext abElem
  
  trans (a b c: Set D) := fun (ab: a ≤ b) (bc: b ≤ c) =>
    -- In general, do I prefer long and incremental and explicit proofs,
    -- or terse and unreadable monsters? I think I prefer the former.
    --
    -- fun (d: D) =>
    --   let abi: d ∈ a → d ∈ b := ab s
    --   let bci: d ∈ b → d ∈ c := bc s
    --   fun (sa: d ∈ a) => bci (abi sa)
    fun (d: D) (sa: d ∈ a) => (bc d) ((ab d) sa)
  
  ltIffLeNotEq _ _ := Iff.intro id id

namespace Set
  def empty {D: Type}: Set D := fun _ => False  
  def full  {D: Type}: Set D := fun _ => True
  def just  {D: Type} (d: D): Set D := fun x => x = d
  
  def isFinite (s: Set D): Prop := ∃ l: List D, ∀ t: D, t ∈ s → t ∈ l
  
  def isSubset (a b: Set D): Prop := ∀ d: D, d ∈ a → d ∈ b
  
  def union {Index: Type} {D: Type} (family: Index → Set D): Set D :=
    fun (d: D) => ∃ i: Index, family i d
  
  theorem union.isWider
    (family: Index → Set D)
    (i: Index)
  :
    (family i) ⊆ (union family)
  :=
    fun (d: D) (dfi: d ∈ family i) => ⟨i, dfi⟩
  
  def binaryUnion (a b: Set D): Set D := fun d: D => a d ∨ b d
  def binaryIntersection (a b: Set D): Set D := fun d: D => a d ∧ b d
  def complement (a: Set D): Set D := fun d: D => ¬ a d
end Set

infix:60 " ∪ " => Set.binaryUnion
infix:60 " ∩ " => Set.binaryIntersection
prefix:100 "~ " => Set.complement
