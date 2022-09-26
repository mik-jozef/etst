/-
  Defines ordinals. Takes heavy inspiration from mathlib
  (I guess -- I wrote this comment before defining them).
  Update: so I guess I freestyle a lot.
-/

import Set


structure WellOrder where
  T: Type -- How can I make you an instance of LE?
  lt: T → T → Prop
  
  total: ∀ a b: T, lt a b ∨ lt b a ∨ a = b
  wf: WellFounded lt
  
  -- This is the definition that I know, but it surely is equivalent. (Right?)
  -- wf: ∀ s: Set T, s = Set.empty ∨ ∃ tL: ↑s, ∀ t: ↑s, le tL t

instance (w: WellOrder): WellFoundedRelation w.T where
  rel := w.lt
  wf := w.wf

namespace WellOrder
  structure Isomorphism (wa wb: WellOrder) where
    f: wa.T → wb.T
    g: wb.T → wa.T
    
    bijA: ∀ a: wa.T, g (f a) = a
    bijB: ∀ b: wb.T, f (g b) = b
    
    ordPres: ∀ a b: wa.T, wa.lt a b ↔ wb.lt (f a) (f b)
  
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
      (fun wbltAB =>
        ((iab.bijB a) ▸ (iab.bijB b) ▸
          (iab.ordPres (iab.g a) (iab.g b)).mpr) wbltAB)
      (fun ltWaGaGb =>
        ((iab.bijB a) ▸ (iab.bijB b) ▸
          (iab.ordPres (iab.g a) (iab.g b)).mp) ltWaGaGb)
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
        (fun waltAB =>
          let wbltAB := (iab.ordPres a b).mp waltAB
          (ibc.ordPres (iab.f a) (iab.f b)).mp wbltAB)
        (fun wcltAB =>
          let wbltAB := (ibc.ordPres (iab.f a) (iab.f b)).mpr wcltAB
          (iab.ordPres a b).mpr wbltAB)
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

namespace Ordinal
  def mk (w: WellOrder) := Quotient.mk' w
  
  inductive ZeroT
  
  def zero: Ordinal := mk {
    T := ZeroT,
    lt := fun _ _ => False,
    total := fun nope _ => ZeroT.rec nope,
    wf := ⟨fun nope => ZeroT.rec nope⟩
  }
  
  
  @[reducible] def succW.lt (w: WellOrder): (a b: Option w.T) → Prop
    | none, _ => False
    | some _, none => True
    | some a, some b => w.lt a b
  
  def succW.wf (w: WellOrder) (a: w.T): Acc (succW.lt w) (some a) :=
      Acc.intro (some a) fun (b: Option w.T) ltB =>
        match b with
        | none => False.elim ltB
        | some c =>
            let wLtAC: w.lt c a = lt w (some c) (some a) := rfl
            have: w.lt c a := wLtAC ▸ ltB
            have: WellFounded w.lt := w.wf
            succW.wf w c
  termination_by succW.wf w a => a
  
  def succW (w: WellOrder): Ordinal :=
    /-
    -- Lean, it's a shame that:
    -- 0. I have to repeat `let (rec)? wf (a: w.T)`,
    -- 1. termination_by seemingly cannot be put in anywhere.
    -- 2. While we are bashing Lean, I would expect local namespaces
    --    to work as well :D
    let wf (a: w.T) := let rec wf (a: w.T): Acc (succ.lt w) (some a) := (
      Acc.intro (some a) fun (b: Option w.T) ltB =>
        match b with
        | none => False.elim ltB
        | some c =>
            let wLtAC: w.lt c a = lt (some c) (some a) := rfl
            have: w.lt c a := wLtAC ▸ ltB
            wf c
    ) -- It's also a shame that you have significant whitespace.
     wf a
    termination_by succ.wf w a => a
    -/
    
    /-| some a => -- TODO delete?
        -- Why is WellFounded defined in such a stupid way?
        -- (Why wrap the prop in an inductive type?)
        match w.wf with
        | ⟨f⟩ => f a-/
    
    mk {
      T := Option w.T,
      lt := succW.lt w,
      total := fun (a b: Option w.T) =>
        match a, b with
        | none, none => by simp
        | none, some x => by simp [rfl ▸ trivial]
        | some x, none =>
            let whyUNoDoItUrself: succW.lt w (some x) none = True := rfl
            by simp [whyUNoDoItUrself, rfl ▸ trivial]
        | some x, some y =>
            let a: w.lt x y = succW.lt w (some x) (some y) := rfl
            let b: w.lt y x = succW.lt w (some y) (some x) := rfl
            let c := a ▸ b ▸ w.total x y
            c.elim
              (fun a => Or.inl a)
              (fun bc => bc.elim
                (fun b => Or.inr (Or.inl b))
                fun c => Or.inr (Or.inr (congr rfl c)))
      wf := ⟨
        fun a: Option w.T =>
          match a with
            | none =>
                Acc.intro none fun (b: Option w.T) ltB =>
                  match b with
                    | none => False.elim ltB
                    | some a => succW.wf w a
            | some a => succW.wf w a
      ⟩
    }
  
  def succ := Quotient.lift succW fun wa wb: WellOrder =>
    fun asimb: wa ≈ wb => sorry
end Ordinal
