/-
  Defines ordinals. Takes heavy inspiration from mathlib
  (I guess -- I wrote this comment before defining them).
-/

import Set


/-def isLeast
  (le: T → T → Prop)
  (tL: T)
  (s: Set T)
:=
  ∀ t: ↑s, le tL t

def hasLeast (le: T → T → Prop) (s: Set T) := ∃ tL: ↑s, isLeast le tL s-/

structure WellOrder where
  T: Type -- How can I make you an instance of LE?
  le: T → T → Prop
  
  total: ∀ a b: T, le a b ∨ le b a
  wf: ∀ s: Set T, s = Set.empty ∨ ∃ tL: ↑s, ∀ t: ↑s, le tL t

namespace WellOrder
  structure Isomorphism (wa wb: WellOrder) where
    f: wa.T → wb.T
    g: wb.T → wa.T
    
    bijA: ∀ a: wa.T, g (f a) = a
    bijB: ∀ b: wb.T, f (g b) = b
    
    ordPres: ∀ a b: wa.T, wa.le a b ↔ wb.le (f a) (f b)
  
  def isIsomorphic (wa wb: WellOrder) := ∃ _: Isomorphism wa wb, True
  
  def selfIsomorphism (x: WellOrder): Isomorphism x x := {
    f := id
    g := id
    
    bijA := by simp
    bijB := by simp
    ordPres := by simp
  }
  
  def Isomorphism.symm (iab: Isomorphism wa wb): Isomorphism wb wa := {
    f := iab.g
    g := iab.f
    
    bijA := iab.bijB
    bijB := iab.bijA
    
    ordPres := fun (a b: wb.T) => Iff.intro
      (fun wbLeAB =>
        ((iab.bijB a) ▸ (iab.bijB b) ▸
          (iab.ordPres (iab.g a) (iab.g b)).mpr) wbLeAB)
      (fun leWaGaGb =>
        ((iab.bijB a) ▸ (iab.bijB b) ▸
          (iab.ordPres (iab.g a) (iab.g b)).mp) leWaGaGb)
  }
  
  def Isomorphism.trans
    (iab: Isomorphism wa wb)
    (ibc: Isomorphism wb wc)
  :
    Isomorphism wa wc
  := {
    f := ibc.f ∘ iab.f
    g := iab.g ∘ ibc.g
    
    bijA := fun a: wa.T =>
      let ibcGF: ibc.g ∘ ibc.f = id := funext ibc.bijA
      let iabGF: iab.g ∘ iab.f = id := funext iab.bijA
      
      show (iab.g ∘ (ibc.g ∘ ibc.f) ∘ iab.f) a = a from ibcGF ▸ iabGF ▸ rfl
    
    bijB := fun a: wc.T =>
      let ibcFG: ibc.f ∘ ibc.g = id := funext ibc.bijB
      let iabFG: iab.f ∘ iab.g = id := funext iab.bijB
      
      show (ibc.f ∘ (iab.f ∘ iab.g) ∘ ibc.g) a = a from iabFG ▸ ibcFG ▸ rfl
    
    ordPres := fun a b: wa.T =>
      Iff.intro
        (fun waLeAB =>
          let wbLeAB := (iab.ordPres a b).mp waLeAB
          (ibc.ordPres (iab.f a) (iab.f b)).mp wbLeAB)
        (fun wcLeAB =>
          let wbLeAB := (ibc.ordPres (iab.f a) (iab.f b)).mpr wcLeAB
          (iab.ordPres a b).mpr wbLeAB)
  }
end WellOrder


instance wellOrderSetoid: Setoid WellOrder where
  r (a b: WellOrder) := WellOrder.isIsomorphic a b
  iseqv := {
    refl := fun x => ⟨x.selfIsomorphism, trivial⟩
    symm := fun isIsm => isIsm.elim fun i _ => ⟨i.symm, trivial⟩
    trans := fun ab bc =>
      ab.elim fun iab _ =>
        bc.elim fun ibc _ =>
          ⟨WellOrder.Isomorphism.trans iab ibc, trivial⟩
  }

def Ordinal := Quotient wellOrderSetoid