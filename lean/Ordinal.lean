/-
  Defines ordinals. Takes heavy inspiration from mathlib
  (I guess -- I wrote this comment before defining them).
  Update: so I guess I freestyle a lot.
  
  Don't look inside. It's embarrassing. (And also supposed
  to be write-once, forget and don't ever read again.)
-/

import Set

open Classical


theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- When I try to inline this, I get errors ¯\_(ツ)_/¯
def Quotient.lift.eq {s: Setoid T}
  (f: T → R)
  (respects: ∀ a b, a ≈ b → f a = f b)
  (t: T)
  (q: Quotient s)
  (tq: q = Quotient.mk s t)
:
  Quotient.lift f respects q = f t
:=
  tq ▸ rfl

def Quotient.delift {s: Setoid T}
  (f: T → R)
  (respects: ∀ a b, a ≈ b → f a = f b)
  (t: T)
  (q: Quotient s)
  (tq: q = Quotient.mk s t)
:
  Quotient.lift f respects q = f t
:=
  let ind (tt: T):
    Quotient.mk' tt = q →
    Quotient.lift f respects (Quotient.mk' tt) = f t
  :=
    fun eqIn =>
      let eq: Quotient.mk' tt = Quotient.mk' t := eqIn.trans tq
      eq ▸ rfl
  
  let motive (qq: Quotient s) := qq = q → Quotient.lift f respects qq = f t
  
  (@Quotient.ind T s motive ind q) rfl


def subtypeWellfounded
  {T: Type}
  (s: Set T)
  [wf : WellFoundedRelation T]
:
  WellFoundedRelation s
:=
  invImage Subtype.val wf


def Minimal (s: Set T) (lt: T → T → Prop): Type :=
  { t: T // t ∈ s ∧ ∀ tt: T, lt tt t → tt ∉ s }

noncomputable def minimal
  {T: Type}
  [wf: WellFoundedRelation T]
  (s: Set T)
  (nonempty: ↑s)
:
  Minimal s wf.rel
:= (
  WellFounded.fix (subtypeWellfounded s).wf fun
    (t: ↑s)
    (rc: (tt: ↑s) → wf.rel tt t → Minimal s wf.rel)
  =>
    if h: ∃ tt: ↑s, wf.rel tt t then
      let tt := choiceEx h
      rc tt tt.property
    else
      let nh: ∀ tt: T, wf.rel tt t → tt ∉ s :=
        fun tt ttLtT ttInS =>
          h ⟨⟨tt, ttInS⟩, ttLtT⟩
      ⟨t, And.intro t.property nh⟩
) nonempty


def wfRel.irefl [wf: WellFoundedRelation T] (a: T):
  ¬ wf.rel a a
:=
  -- The following crashes Lean:
  -- https://github.com/leanprover/lean4/issues/1673
  --
  -- fun aLtA => False.elim ((wfRel.irefl a) aLtA)
  -- termination_by wfRel.irefl a => a
  let A := { t: T // t = a }
  let wfSub := subtypeWellfounded (fun t => t = a)
  
  fun aLtA =>
    let f := WellFounded.fix wfSub.wf fun
      (x: A)
      (rc: (xx: A) → wf.rel xx x → ¬ wf.rel a a)
    =>
      match h: x with
        | ⟨xVal, eqA⟩ =>
            rc ⟨a, rfl⟩ (eqA ▸ aLtA)
    
    f ⟨a, rfl⟩ aLtA

def wfRel.antisymm [wf: WellFoundedRelation T] {a b: T}:
  wf.rel a b → wf.rel b a → a = b
:=
  let AOrB := { t: T // t = a ∨ t = b }
  let wfSub := subtypeWellfounded (fun t => t = a ∨ t = b)
  
  fun aLtB bLtA =>
    let f := WellFounded.fix wfSub.wf fun
      (x: AOrB)
      (rc: (xx: AOrB) → wf.rel xx x → a = b)
    =>
      match h: x with
        | ⟨xVal, Or.inl eqA⟩ =>
            rc ⟨b, Or.inr rfl⟩ (eqA ▸ bLtA)
        | ⟨xVal, Or.inr eqB⟩ =>
            rc ⟨a, Or.inl rfl⟩ (eqB ▸ aLtB)
    
    f ⟨a, Or.inl rfl⟩


def monoInvMono
  (f: A → B)
  (a0 a1: A)
  [aOrd: WellFoundedRelation A]
  [bOrd: WellFoundedRelation B]
  (ltFA: bOrd.rel (f a0) (f a1))
  (total: ∀ a0 a1: A, aOrd.rel a0 a1 ∨ aOrd.rel a1 a0 ∨ a0 = a1)
  (fMono: ∀ a0 a1: A, aOrd.rel a0 a1 → bOrd.rel (f a0) (f a1))
:
  aOrd.rel a0 a1
:=
  (total a0 a1).elim id
    (fun gtOrEq =>
      let eq: f a0 = f a1 := gtOrEq.elim
        (fun gt => wfRel.antisymm ltFA (fMono a1 a0 gt))
        fun eq => congr rfl eq
      let irefl: bOrd.rel (f a0) (f a0) := eq ▸ ltFA
      
      False.elim (wfRel.irefl (f a0) irefl))


structure WellOrder where
  T: Type
  lt: T → T → Prop
  
  total: ∀ a b: T, lt a b ∨ lt b a ∨ a = b
  wf: WellFounded lt

instance wfWT (w: WellOrder): WellFoundedRelation w.T where
  rel := w.lt
  wf := w.wf

instance ltWLt (w: WellOrder): LT w.T where
  lt := w.lt

namespace WellOrder
  def lt.trans {w: WellOrder} {a b c: w.T}:
    a < b → b < c → a < c
  := (
    WellFounded.fix w.wf fun
      (c: w.T)
      (rc:
        (cc: w.T) →
        w.lt cc c →
        ∀ a b: w.T, a < b → b < cc → a < cc
      )
    =>
      fun (a b: w.T) aLtB bLtC =>
        (w.total a c).elim id (
          fun gtOrEq =>
            let cLtB: c < b := gtOrEq.elim
              (fun cLtA => rc b bLtC c a cLtA aLtB)
              (fun aEqC => aEqC ▸ aLtB)
            let bEqC: b = c := wfRel.antisymm bLtC cLtB
            let bLtB: b < b := bEqC ▸ cLtB
            let bNLtB: ¬ b < b := wfRel.irefl b
            False.elim (bNLtB bLtB)
        )
  ) c a b
  
  
  structure Morphism (wa wb: WellOrder) where
    f: wa.T → wb.T
    
    ordPres: ∀ a0 a1: wa.T, a0 < a1 ↔ f a0 < f a1
  
  namespace Morphism
    def ordPresEq (m: Morphism wa wb) {a b: wa.T}:
      m.f a = m.f b → a = b
    :=
      fun eq =>
        let nope {p: Prop} {a b: wa.T} (lt: a < b) (eq: m.f a = m.f b): p :=
          let ltFAB := (m.ordPres a b).mp lt
          False.elim (wfRel.irefl (m.f a) (eq ▸ ltFAB))
        
        (wa.total a b).elim
          (fun lt => nope lt eq)
          (fun gtOrEq => gtOrEq.elim
            (fun gt => nope gt eq.symm)
            id)
    
    def free (m: Morphism wa wb) (b: wb.T): Prop :=
      ∀ aa: wa.T, b ≠ m.f aa
    
    def bound (m: Morphism wa wb) (b: wb.T): Prop :=
      ∃ aa: wa.T, b = m.f aa
    
    def freeBound {p: Prop}
      (f: free m b)
      (b: bound m b)
    :
      p
    :=
      let aa := choiceEx b
      False.elim (f aa aa.property)
    
    def nFreeBound {p: Prop}
      (f: ¬ free m b)
      (b: ¬ bound m b)
    :
      p
    :=
      False.elim (f fun a neq => b ⟨a, neq⟩)
    
    
    -- Not sure if the terminology corresponds to category
    -- theory. An initial morphism picks the least elements
    -- possible. (In other words, it maps onto the initial
    -- segment of the target well-order.)
    def isInitial (m: Morphism wa wb): Prop :=
      ∀ a: wa.T, ∀ b: wb.T, b < m.f a → bound m b
    
    @[reducible] def Initial (wa wb: WellOrder) :=
      { m: Morphism wa wb // isInitial m }
    
    
    def trans
      (mab: Morphism wa wb)
      (mbc: Morphism wb wc)
    :
      Morphism wa wc
    := {
      f := mbc.f ∘ mab.f
      
      ordPres := fun a b => Iff.intro (
        fun waLtAB =>
          (mbc.ordPres (mab.f a) (mab.f b)).mp ((mab.ordPres a b).mp waLtAB)
      ) (
        fun wbLtAB =>
          (mab.ordPres a b).mpr ((mbc.ordPres (mab.f a) (mab.f b)).mpr wbLtAB)
      )
    }
  end Morphism
  
  structure Isomorphism (wa wb: WellOrder) where
    f: wa.T → wb.T
    g: wb.T → wa.T
    
    bijA: ∀ a: wa.T, g (f a) = a
    bijB: ∀ b: wb.T, f (g b) = b
    
    ordPres: ∀ a b: wa.T, a < b ↔ f a < f b
  
  def isIsomorphic (wa wb: WellOrder) := ∃ _: Isomorphism wa wb, True
  
  namespace Isomorphism
    def morphismF (i: Isomorphism wa wb): Morphism wa wb := {
      f := i.f
      ordPres := i.ordPres
    }
    
    def morphismG (i: Isomorphism wa wb): Morphism wb wa := {
      f := i.g
      ordPres := fun (a b: wb.T) => Iff.intro (
        fun ltAb =>
          ((i.bijB a) ▸ (i.bijB b) ▸ (i.ordPres (i.g a) (i.g b)).mpr) ltAb
      ) (
        fun ltAb =>
          ((i.bijB a) ▸ (i.bijB b) ▸ (i.ordPres (i.g a) (i.g b)).mp) ltAb
      )
    }
    
    def morphismF.isInitial
      (i: Isomorphism wa wb)
    :
      Morphism.isInitial (i.morphismF)
    :=
      fun _ b _ => ⟨i.morphismG.f b, (i.bijB b).symm⟩
    
    def notFree
      (i: Isomorphism wa wb)
      (b: wb.T)
    :
      ¬ Morphism.free i.morphismF b --∀ aa: wa.T, b ≠ m.f aa
    :=
      fun allFANeqB =>
        let a := i.morphismG.f b
        let bEqFA: b = i.morphismF.f a := (i.bijB b).symm
        let bNeqFA: b ≠ i.morphismF.f a := allFANeqB a
        bNeqFA bEqFA
    
    
    def refl (x: WellOrder): Isomorphism x x := {
      f := id
      g := id
      
      bijA := by simp
      bijB := by simp
      ordPres := by simp
    }
    
    def symm (iab: Isomorphism wa wb): Isomorphism wb wa := {
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
    
    def trans
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
  end Isomorphism
  
  def isIsomorphic.refl: isIsomorphic wa wa :=
     ⟨WellOrder.Isomorphism.refl wa, trivial⟩
  
  def isIsomorphic.symm (isIso: isIsomorphic wa wb): isIsomorphic wb wa :=
     isIso.elim fun iso _ => ⟨iso.symm, trivial⟩
  
  def isIsomorphic.trans
    (isIsoAB: isIsomorphic wa wb)
    (isIsoBC: isIsomorphic wb wc)
  :
    isIsomorphic wa wc
  :=
     isIsoAB.elim fun ab _ =>
      isIsoBC.elim fun bc _ =>
       ⟨Isomorphism.trans ab bc, trivial⟩
  
  
  def Morphism.refl (w: WellOrder): Morphism.Initial w w := ⟨
    (Isomorphism.refl w).morphismF,
    Isomorphism.morphismF.isInitial (Isomorphism.refl w)
  ⟩
  
  
  @[reducible] def succ.lt (w: WellOrder): (a b: Option w.T) → Prop
    | none, _ => False
    | some _, none => True
    | some a, some b => a < b
  
  def succ.wf (w: WellOrder) (a: w.T): Acc (succ.lt w) (some a) :=
      Acc.intro (some a) fun (b: Option w.T) ltB =>
        match b with
        | none => False.elim ltB
        | some c => succ.wf w c
  termination_by succ.wf w a => a
  
  def succ.ordPress (w: WellOrder) (a b: w.T):
    a < b ↔ succ.lt w (some a) (some b)
  :=
    Iff.intro id id
  
  def succ (w: WellOrder): WellOrder :=
    {
      T := Option w.T,
      lt := succ.lt w,
      total := fun (a b: Option w.T) =>
        match a, b with
        | none, none => by simp
        | none, some x => by simp [rfl ▸ trivial]
        | some x, none =>
            let whyUNoDoItUrself: succ.lt w (some x) none = True := rfl
            by simp [whyUNoDoItUrself, rfl ▸ trivial]
        | some x, some y =>
            let a: (x < y) = succ.lt w (some x) (some y) := rfl
            let b: (y < x) = succ.lt w (some y) (some x) := rfl
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
                    | some a => succ.wf w a
            | some a => succ.wf w a
      ⟩
    }
  
  -- TODO do I need you
  def succ.morphism (w: WellOrder): Morphism w w.succ := {
    f := fun a => some a
    
    -- This is another trivial statement that your theorem
    -- prover should be able to derive on its own.
    ordPres := fun _ _ => Iff.intro id id
  }
  
  def succ.f
   {wa wb: WellOrder}
   (f: wa.T → wb.T)
  :
    wa.succ.T → wb.succ.T
  :=
    fun a: wa.succ.T =>
      match a with
        | none => none
        | some a => some (f a)
  
  def Morphism.succ (mab: Morphism wa wb):
    Morphism wa.succ wb.succ
  := {
    f := succ.f mab.f
    ordPres := fun a0 a1 =>
      match a0, a1 with
        | none, _ => Iff.intro False.elim False.elim
        | some _, none => Iff.intro id id
        | some a0, some a1 => mab.ordPres a0 a1
  }
  
  
  noncomputable def Morphism.initial.f
    (m: Morphism wa wb)
    (a: wa.T)
  :
    { b: wb.T // b < m.f a ∨ b = m.f a }
    --Minimal (fun b: wb.T => ∀ aa: wa.T, aa < a → Morphism.initial.f m aa < b) wb.lt
  :=
    let gtBefore (b: wb.T) := ∀ aa: wa.T, aa < a → Morphism.initial.f m aa < b
    
    let mfaGt: gtBefore (m.f a) :=
      fun aa aaLtA =>
        (Morphism.initial.f m aa).property.elim
         (fun lt => WellOrder.lt.trans lt ((m.ordPres aa a).mp aaLtA))
         (fun eq => eq.symm ▸ ((m.ordPres aa a).mp aaLtA))
    
    let minimalGt := (minimal gtBefore ⟨m.f a, mfaGt⟩)
    
    ⟨minimalGt.val, (wb.total minimalGt.val (m.f a)).elim
      (fun lt => Or.inl lt)
      (fun gtOrEq => gtOrEq.elim
        (fun gt => False.elim (minimalGt.property.right (m.f a) gt mfaGt))
        (fun eq => Or.inr eq))⟩
    termination_by Morphism.initial.f m a => a
  
  -- TODO do I need you? This is probably useless, because
  -- an initial morphism does not have to be a one constructed
  -- using this function.
  noncomputable def Morphism.initial.f.properType
    (m: Morphism wa wb)
    (a: wa.T)
  :
    Minimal (fun b: wb.T => ∀ aa: wa.T, aa < a → Morphism.initial.f m aa < b) wb.lt
  :=
    -- I have to put parts of the implementation of `Morphism.initial.f`
    -- here, because Lean cannot mention the function in its return type.
    -- Or is there a better way?
    let gtBefore (b: wb.T) := ∀ aa: wa.T, aa < a → Morphism.initial.f m aa < b
    let mfaGt: gtBefore (m.f a) :=
      fun aa aaLtA =>
        (Morphism.initial.f m aa).property.elim
         (fun lt => WellOrder.lt.trans lt ((m.ordPres aa a).mp aaLtA))
         (fun eq => eq.symm ▸ ((m.ordPres aa a).mp aaLtA))
    let minimalGt := (minimal gtBefore ⟨m.f a, mfaGt⟩)
    -- I think I need to return this to make use of definitional equality.
    let ret := (Morphism.initial.f m a).val
    let eq: minimalGt.val = ret :=
      -- Definitional equality having a break?
      show minimalGt.val = (Morphism.initial.f m a) from by unfold f; rfl
    
    ⟨ret, eq ▸ minimalGt.property⟩
  
  noncomputable def Morphism.initial.f.monotonic
    (m: Morphism wa wb)
    (a0 a1: wa.T)
    (ltAA: a0 < a1)
  :
    (f m a0).val < (f m a1).val
  :=
    let gtBefore (b: wb.T) := ∀ aa: wa.T, aa < a1 → Morphism.initial.f m aa < b
    let mfaGt: gtBefore (m.f a1) :=
      fun aa aaLtA =>
        (Morphism.initial.f m aa).property.elim
         (fun lt => WellOrder.lt.trans lt ((m.ordPres aa a1).mp aaLtA))
         (fun eq => eq.symm ▸ ((m.ordPres aa a1).mp aaLtA))
    let minimalGt := (minimal gtBefore ⟨m.f a1, mfaGt⟩)
    
    let eq: minimalGt.val = Morphism.initial.f m a1 := by unfold f; rfl
    
    eq ▸ minimalGt.property.left a0 ltAA
  
  noncomputable def Morphism.initial.f.initial
    (m: Morphism wa wb)
    (a: wa.T)
    (b: wb.T)
    (ltBFA: b < f m a)
  :
    ∃ aa: wa.T, b = f m aa
  :=
    if hGt: ∃ aa: wa.T, aa < a ∧ b < f m aa then
      let aa := choiceEx hGt
      have: aa < a := aa.property.left
      initial m aa b aa.property.right
    else
      let gtBefore (b: wb.T) := ∀ aa: wa.T, aa < a → f m aa < b
      let mfaGt: gtBefore (m.f a) :=
        fun aa aaLtA =>
          (f m aa).property.elim
          (fun lt => WellOrder.lt.trans lt ((m.ordPres aa a).mp aaLtA))
          (fun eq => eq.symm ▸ ((m.ordPres aa a).mp aaLtA))
      let minimalGt := (minimal gtBefore ⟨m.f a, mfaGt⟩)
      
      let eq: minimalGt.val = f m a := by unfold f; rfl
      
      if hEq: ∃ aa: wa.T, aa < a ∧ b = f m aa then
        let aa := choiceEx hEq
        ⟨aa, aa.property.right⟩
      else
        let bGt: gtBefore b :=
          fun aa aaLtA =>
            (wb.total (f m aa) b).elim id
              fun geOrEq => geOrEq.elim
                (fun bLtFAa => False.elim (hGt ⟨aa, And.intro aaLtA bLtFAa⟩))
                fun eq => False.elim (hEq ⟨aa, And.intro aaLtA eq.symm⟩)
        
        let bNGt := minimalGt.property.right b (eq ▸ ltBFA)
        
        False.elim (bNGt bGt)
  termination_by Morphism.initial.f.initial m a b ltBFA => a
  
  noncomputable def Morphism.initial (m: Morphism wa wb): Morphism.Initial wa wb :=
    let f := fun a => (Morphism.initial.f m a).val
    let mi := {
      f := f
      
      ordPres :=
        fun a0 a1 => Iff.intro
          (initial.f.monotonic m a0 a1)
          (fun ltFA => @monoInvMono wa.T wb.T f a0 a1
            (wfWT wa) (wfWT wb) ltFA (wa.total) (initial.f.monotonic m))
    }
    ⟨
      mi,
      fun a b (bLtFa: b < mi.f a) =>
        let eqFa: Morphism.initial.f m a = mi.f a := by simp
        Morphism.initial.f.initial m a b (eqFa ▸ bLtFa)
    ⟩
  
  def initial.trans.eq.helper
    (mab: Morphism.Initial wa wb)
    (mbc: Morphism.Initial wb wc)
    (mac: Morphism.Initial wa wc)
    (a: wa.T)
  :
    (mab.val.trans mbc.val).f a = mac.val.f a
  :=
    let rc (aa: wa.T) (_: aa < a) :=
      initial.trans.eq.helper mab mbc mac aa
    
    let mtr := (mab.val.trans mbc.val)
    
    let abc := mtr.f a
    let ac := mac.val.f a
    
    (wc.total abc ac).elim
      (fun lt =>
        let abcBound: mac.val.bound abc := mac.property a abc lt
        let abcNBound: ¬ mac.val.bound abc :=
          fun isBound =>
            let bound := choiceEx isBound
            let boundAC := mac.val.f bound
            let boundABC := mtr.f bound
            (wa.total bound.val a).elim
              (fun ltB =>
                let eqBound: boundABC = boundAC := rc bound ltB
                let eq: boundABC = abc := eqBound.trans bound.property.symm
                let lt: boundABC < abc := (mtr.ordPres bound a).mp ltB
                wfRel.irefl abc (eq ▸ lt))
              (fun gtOrEq => gtOrEq.elim
                (fun gt =>
                  let acLtAbc: ac < abc :=
                    bound.property ▸ (mac.val.ordPres a bound).mp gt
                  let eq: ac = abc := wfRel.antisymm acLtAbc lt
                  wfRel.irefl abc (eq ▸ lt))
                (fun eq =>
                  -- So much for the definitional equality of variables
                  -- with their bodies.
                  let eq1: ac = abc := show mac.val.f a = abc from
                    eq ▸ bound.property ▸ congr rfl rfl
                  wfRel.irefl abc (eq1 ▸ lt)))
        False.elim (abcNBound abcBound))
      (fun gtOrEq => gtOrEq.elim
        (fun gt =>
          let ab := mab.val.f a
          let ltAc (aa: wa.T) (aaLtA: aa < a): mtr.f aa < ac :=
            let eq: mtr.f aa = mac.val.f aa := rc aa aaLtA
            let lt: mac.val.f aa < mac.val.f a :=
              (mac.val.ordPres aa a).mp aaLtA
            eq ▸ lt
          let ltBA (bb: wb.T) (bbLtB: bb < ab):
            mbc.val.f bb < ac
          :=
            let bbBound: mab.val.bound bb := mab.property a bb bbLtB
            let bA := choiceEx bbBound
            let bALtA: bA < a := (mab.val.ordPres bA a).mpr (bA.property ▸ bbLtB)
            let ltMtrBaAc := ltAc bA bALtA
            let mtrEqLeft: mtr.f bA = mbc.val.f (mab.val.f bA.val) := rfl
            let mtrEqRight: mbc.val.f (mab.val.f bA.val) = mbc.val.f bb :=
              congr rfl bA.property.symm
            let mtrEq: mtr.f bA = mbc.val.f bb := mtrEqLeft.trans mtrEqRight
            mtrEq ▸ ltMtrBaAc
          let acBoundEx: mbc.val.bound ac := mbc.property ab ac gt
          let acBound := choiceEx acBoundEx
          let acBoundLtAb: acBound < ab :=
            (mbc.val.ordPres acBound ab).mpr (acBound.property ▸ gt)
          let acBoundLtAc: mbc.val.f acBound < ac := ltBA acBound acBoundLtAb
          let selfLt: mbc.val.f acBound < mbc.val.f acBound :=
            acBound.property ▸ acBoundLtAc
          False.elim (wfRel.irefl (mbc.val.f acBound) selfLt))
        id)
  termination_by initial.trans.eq.helper mab mbc mac a => a
  
  def initial.trans.eq
    (mab: Morphism.Initial wa wb)
    (mbc: Morphism.Initial wb wc)
    (mac: Morphism.Initial wa wc)
  :
    mab.val.trans mbc.val = mac.val
  :=
    let fEq: (mab.val.trans mbc.val).f = mac.val.f :=
      funext fun a: wa.T => eq.helper mab mbc mac a
    match mab.val.trans mbc.val, mac.val, fEq with
      | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
  
  noncomputable def Morphism.self.initial.eqId
    (m: Morphism.Initial w w)
  :
    m.val.f = id
  :=
    let mwId: Morphism.Initial w w := Morphism.refl w
    let eq: mwId.val.trans mwId.val = m := initial.trans.eq mwId mwId m
    let leftId: (mwId.val.trans mwId.val).f = id := rfl
    eq ▸ leftId
  
  
  def isGreatest (w: WellOrder) (gst: w.T) := ∀ t: w.T, t = gst ∨ t < gst
  
  def isGreatest.nLt {w: WellOrder} {a: w.T} {b: w.T}
    (gstA: isGreatest w a)
    (aLtB: a < b)
  :
    a = b
  :=
    (gstA b).elim
      (fun eq => eq.symm)
      (fun bLtA => wfRel.antisymm aLtB bLtA)
  
  def isGreatest.eq {w: WellOrder} {a: w.T} {b: w.T}
    (gstA: isGreatest w a)
    (gstB: isGreatest w b)
  :
    a = b
  :=
    (w.total a b).elim
      (fun aLtB => nLt gstA aLtB)
      (fun gtOrEq => gtOrEq.elim (fun gt => (nLt gstB gt).symm) id)
  
  def greatestIso
    (wa wb: WellOrder)
    (isoAB: Isomorphism wa wb)
    (waGst: { t: wa.T // isGreatest wa t })
  :
    { t: wb.T // isGreatest wb t }
  := ⟨
    isoAB.f waGst,
    fun t: wb.T =>
      if h: t = isoAB.f waGst then
        Or.inl h
      else
        Or.inr ((waGst.property (isoAB.g t)).elim (
          fun eq =>
            let eqF: t = isoAB.f waGst.val :=
              (isoAB.bijB t) ▸ congr (@rfl _ isoAB.f) eq
            False.elim (h eqF)
          ) (
            fun lt =>
              (isoAB.bijB t) ▸ (isoAB.ordPres (isoAB.g t) waGst).mp lt
          ))
  ⟩
  
  def nGreatestIso
    (wa wb: WellOrder)
    (isoAB: Isomorphism wa wb)
    (a: { t: wa.T // ¬ isGreatest wa t })
  :
    { t: wb.T // ¬ isGreatest wb t }
  := ⟨
    isoAB.f a.val,
    fun nope =>
      let aGst := (greatestIso wb wa isoAB.symm ⟨isoAB.f a, nope⟩)
      a.property ((isoAB.bijA a) ▸ aGst.property)
  ⟩
  
  def succ.nIso (w: WellOrder): ¬ ∃ _: Isomorphism w w.succ, True :=
    fun isoEx =>
      let iso: Isomorphism w w.succ := choiceEx isoEx
      
      if h: ∃ t: w.T, iso.f t ≠ some t then
        let lstT: Minimal (fun t => iso.f t ≠ some t) w.lt :=
          minimal (fun t => iso.f t ≠ some t) (choiceEx h)
        
        (w.succ.total (iso.f lstT.val) (some lstT.val)).elim
          (fun lt =>
            let fLstT: { t: w.T // some t = iso.f lstT.val } :=
              match hh: iso.f lstT.val with
                | none =>
                    let ltNone: w.succ.lt none (some lstT.val) := hh ▸ lt
                    False.elim ltNone
                | some a => ⟨a, rfl⟩
            
            let ltWSucc: w.succ.lt (some fLstT) (some lstT.val) :=
              fLstT.property.symm ▸ lt
            let ltW: w.lt fLstT lstT.val := ltWSucc
            
            let notNotId := lstT.property.right fLstT ltW
            
            let ff: iso.f fLstT.val = some fLstT.val :=
              dne notNotId
            
            let lt0: w.succ.lt (iso.f fLstT.val) (iso.f lstT.val) :=
              (iso.ordPres fLstT lstT.val).mp ltW
            
            let lt1: w.succ.lt (some fLstT.val) (iso.f lstT.val) :=
              ff ▸ lt0
            
            let lt2: w.succ.lt (some fLstT.val) (some fLstT.val) :=
              by conv =>
                rhs
                rw [fLstT.property]; exact lt1
            
            @wfRel.irefl w.succ.T (wfWT w.succ) (some fLstT.val) lt2)
          (fun gtOrEq => gtOrEq.elim
            (fun gt =>
              let gLst := iso.g (some lstT.val)
              let fgLst := iso.f gLst
              let fgLstEq: fgLst = some lstT.val :=
                iso.bijB (some lstT.val)
              
              (w.total gLst lstT.val).elim
                (fun lt =>
                  let ltSucc: w.succ.lt (some gLst) (some lstT.val) := lt
                  let gEq0: w.succ.lt (iso.f gLst) (some lstT.val) :=
                    (dne (lstT.property.right gLst lt)) ▸ ltSucc
                  let gEq1: w.succ.lt (iso.f gLst) fgLst :=
                    fgLstEq ▸ gEq0
                  let gEq1: w.succ.lt fgLst fgLst := gEq1
                  
                  wfRel.irefl fgLst gEq1)
                fun gtOrEq => gtOrEq.elim
                  (fun gtInner =>
                    let lt0: iso.f lstT.val < fgLst :=
                      (iso.ordPres lstT.val gLst).mp gtInner
                    let lt1: w.succ.lt (iso.f lstT.val) (some lstT.val) :=
                      fgLstEq ▸ lt0
                    let eq0: iso.f lstT.val = some lstT.val :=
                      wfRel.antisymm lt1 gt
                    let lt2: w.succ.lt (iso.f lstT.val) (iso.f lstT.val) :=
                      by conv =>
                        rhs
                        rw [eq0]; exact lt1
                    wfRel.irefl (iso.f lstT.val) lt2)
                  fun eq =>
                    let eq0: iso.f lstT.val = fgLst := congr rfl eq.symm
                    let eq1: iso.f lstT.val = some lstT.val := fgLstEq ▸ eq0
                    let lt: iso.f lstT.val < iso.f lstT.val := eq1 ▸ gt
                    wfRel.irefl (iso.f lstT.val) lt)
            fun eq => lstT.property.left eq)
      else
        let allId t: iso.f t = some t :=
          if hh: iso.f t = some t then
            hh
          else
            False.elim (h ⟨t, fun nope => hh nope⟩)
        
        let gNone := iso.g none
        let fgNone := iso.f gNone
        let fgNoneNone: fgNone = none := iso.bijB none
        let fgNoneSome: fgNone = some _ := allId gNone
        Option.noConfusion (fgNoneNone.symm.trans fgNoneSome)
  
  
  @[reducible] def pred.lt
    (w: WellOrder)
    (t0 t1: { t: w.T // ¬ isGreatest w t })
  :=
    t0.val < t1.val
  
  @[reducible] def pred.wf
    (w: WellOrder)
    (t: { t: w.T // ¬ isGreatest w t })
  :
    Acc (pred.lt w) t
  :=
    Acc.intro t fun tt _ => pred.wf w tt
  termination_by pred.wf w tt => tt.val
  
  -- When I only used `pred`, I wasn't able to derive that
  -- `wPred` had the properties of `predNoOpt` from the equation
  -- `w.pred = some wPred`. Is this possible?
  noncomputable def predNoOpt (w: WellOrder): WellOrder := {
    T := { t: w.T // ¬ isGreatest w t }
    
    lt := pred.lt w
    
    total := fun t0 t1 => (w.total t0 t1).elim
      (fun lt01 => Or.inl lt01)
      (fun lt10eq => lt10eq.elim
        (fun lt10 => Or.inr (Or.inl lt10))
        -- https://proofassistants.stackexchange.com/a/1757/1695
        (fun eq => Or.inr (Or.inr (by
          cases t0
          cases t1
          cases eq
          rfl
        ))))
    
    wf := ⟨
      fun t: { t: w.T // ¬ isGreatest w t } => pred.wf w t
    ⟩
  }
  
  noncomputable def predNoOpt.eqT (w: WellOrder):
    (a b: w.predNoOpt.T) → (eq: a.val = b.val) → a = b
  
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
  
  noncomputable def predProp (w: WellOrder):
    { wPredOpt: Option WellOrder //
      ∀ wPred, wPredOpt = some wPred → wPred.succ.isIsomorphic w }
  :=
    if h: ∃ gst: w.T, isGreatest w gst then
      ⟨
        some (predNoOpt w),
        fun wPred wPredEqSome => ⟨
          let wPredEq: predNoOpt w = wPred := Option.noConfusion wPredEqSome id
          
          let A := (predNoOpt w).succ.T
          let B := w.T
          let gst := choiceEx h
          
          let f: A → B
            | none => gst
            | some a => a.val
          
          let g (t: B): A :=
            if h: t = gst.val then
              none
            else
              some ⟨
                t,
                fun isGst => h (isGreatest.eq isGst gst.property)
              ⟩
          
          let predNGreatest (aa: (predNoOpt w).T):
            aa.val ≠ gst.val
          :=
            fun eq =>
              let aaNGreatest := aa.property
              let gstGreatest := gst.property
              let gstNGreatest := eq ▸ aaNGreatest
              gstNGreatest gstGreatest
          
          let fMono :=
            fun a b =>
              (fun aLtB =>
                match a, b with
                  | none, _ => False.elim aLtB
                  | some aa, none =>
                      let aNeqGst: f (some aa) ≠ gst :=
                        let fEq: f (some aa) = aa.val := rfl
                        let aNegGst: aa.val ≠ gst := predNGreatest aa
                        fun eq => aNegGst (fEq.symm.trans eq)
                      (gst.property (f (some aa))).elim
                        (fun eq => False.elim (aNeqGst eq)) id
                  | some _, some _ => aLtB)
          
          wPredEq ▸ {
            f := f
            g := g
            
            bijA := fun a =>
              match a with
                | none =>
                    let eqF: f none = gst := rfl
                    let eqG: g gst = none :=
                      dif_pos (show gst.val = gst.val from rfl)
                    eqF ▸ eqG
                | some aa =>
                    let eqF: f (some aa) = aa.val := rfl
                    let eqG: g aa.val = (some aa) := dif_neg (predNGreatest aa)
                    eqF.symm ▸ eqG
            
            bijB := fun b =>
              if h: b = gst then
                let eqG: g b = none := dif_pos h
                let eqF: f none = b := h ▸ rfl
                eqG ▸ eqF
              else
                -- Thanks o Mighty Lean that you can infer the
                -- values of the underscores here. I bashed you
                -- in other comments, but now I must praise you instead.
                let eqG: g b = some ⟨b, _⟩ := dif_neg h
                let eqF: f (some ⟨b, _⟩) = b := rfl
                eqG ▸ eqF
            
            ordPres := fun a b => Iff.intro
              (fMono a b)
              fun ltFA => (@monoInvMono A B f a b
                (wfWT (predNoOpt w).succ) (wfWT w)
                ltFA (predNoOpt w).succ.total fMono)
          },
          trivial
        ⟩
      ⟩
    else
      ⟨none, fun _ nope => Option.noConfusion nope⟩
  
  noncomputable def pred (w: WellOrder): Option WellOrder :=
    if ∃ gst: w.T, isGreatest w gst then
      some (predNoOpt w)
    else
      none
  
  def pred.eqPredProp (w: WellOrder): w.pred = w.predProp :=
    if h: ∃ gst: w.T, isGreatest w gst then
      let wPredEq: w.pred = some (predNoOpt w) := if_pos h
      let wPredPropEq: w.predProp = ⟨some (predNoOpt w), _⟩ := dif_pos h
      let wPredPropValEq: w.predProp.val = some (predNoOpt w) :=
        congr rfl wPredPropEq
      
      wPredEq.trans wPredPropValEq.symm
    else
      let wPredEq: w.pred = none := if_neg h
      let wPredPropEq: w.predProp = ⟨none, _⟩ := dif_neg h
      let wPredPropValEq: w.predProp.val = none :=
        congr rfl wPredPropEq
      
      wPredEq.trans wPredPropValEq.symm
  
  
  def ifPred.hasGreatest
    (w: WellOrder)
    (pred: { pred: WellOrder // w.pred = some pred })
  :
    ∃ gst: w.T, isGreatest w gst
  :=
    if h: ∃ gst: w.T, isGreatest w gst then
      h
    else
      let nope: w.pred = none := if_neg h
      False.elim (Option.noConfusion (pred.property ▸ nope))
    
  
  noncomputable def predNoOpt.iso
    (wa wb: WellOrder)
    (isIsoAB: WellOrder.isIsomorphic wa wb)
  :
    WellOrder.Isomorphism wa.predNoOpt wb.predNoOpt
  :=
    let isoAB := (choiceEx isIsoAB).val
    
    let f (a: wa.predNoOpt.T): wb.predNoOpt.T := nGreatestIso wa wb isoAB a
    let g (b: wb.predNoOpt.T): wa.predNoOpt.T := nGreatestIso wb wa isoAB.symm b
    
    {
      f := f
      g := g
      
      bijA := fun a =>
        let eqVal: (g (f a)).val = a.val := isoAB.bijA a.val ▸ rfl
        
        predNoOpt.eqT wa (g (f a)) a eqVal
      bijB := fun b =>
        let eqVal: (f (g b)).val = b.val := isoAB.bijB b.val ▸ rfl
        
        predNoOpt.eqT wb (f (g b)) b eqVal
      
      ordPres := fun a b => Iff.intro (
        fun waPredLtAB => (isoAB.ordPres a.val b.val).mp waPredLtAB
      ) (
        fun wbPredLtAB => (isoAB.ordPres a.val b.val).mpr wbPredLtAB
      )
    }
  
  noncomputable def pred.iso
    (wa wb: WellOrder)
    (isIsoAB: WellOrder.isIsomorphic wa wb)
    (waPred: { waPred: WellOrder // wa.pred = some waPred })
  :
    { wbPred: WellOrder //
        wb.pred = some wbPred ∧ WellOrder.isIsomorphic waPred wbPred }
  :=
    let isoAB := (choiceEx isIsoAB).val
    
    -- How could I implement this function in a normal way?
    -- I can only describe the following code as... sinful.
    
    let wbPred: { wbPred: WellOrder // wb.pred = some wbPred }
    :=
      if h: ∃ gst, isGreatest wb gst then
        match hh: wb.pred with
          | none =>
              let eq: wb.pred = some wb.predNoOpt := by
                unfold pred
                simp [h]
              Option.noConfusion (hh ▸ eq)
          | some wbp => ⟨wbp, rfl⟩
      else
        let waGst := choiceEx (ifPred.hasGreatest wa waPred)
        let wbGst := greatestIso wa wb isoAB waGst
        let nope: False := h ⟨wbGst, wbGst.property⟩
        -- How can I do this without choice?
        let nopeEx: ∃ wbPred: WellOrder, _ := False.elim nope
        choiceEx nopeEx
    
    
    let waPredEq: wa.predNoOpt = waPred.val :=
      if h: ∃ gst, isGreatest wa gst then
        let eqL: some wa.predNoOpt = wa.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (Eq.trans eqL waPred.property) id
      else
        let eq: none = wa.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (Eq.trans eq waPred.property)
    
    let wbPredEq: wb.predNoOpt = wbPred.val :=
      if h: ∃ gst, isGreatest wb gst then
        let eqL: some wb.predNoOpt = wb.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (Eq.trans eqL wbPred.property) id
      else
        let eq: none = wb.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (Eq.trans eq wbPred.property)
    
    let isoPred: isIsomorphic waPred wbPred :=
      waPredEq ▸ wbPredEq ▸ ⟨predNoOpt.iso wa wb ⟨isoAB, trivial⟩, trivial⟩
    
    ⟨wbPred, And.intro wbPred.property isoPred⟩
  
  
  def metaLt (wa wb: WellOrder): Prop :=
    ¬ isIsomorphic wa wb ∧ ∃ _: Morphism wa wb, True
  
  noncomputable def ordIn.prop
    (m: Morphism wa wb)
  :
    Minimal
      -- Should have been `some b < bSucc → m.bound b` (I think),
      -- but I don't wanna touch certain code below again.
      -- Now I will suffer for my mystakes.
      (fun bSucc: wb.succ.T => ∀ b: wb.T, bSucc = some b → m.free b)
      wb.succ.lt
  :=
    @minimal wb.succ.T (wfWT wb.succ)
      (fun bSucc => ∀ b: wb.T, bSucc = some b → m.free b)
      ⟨none, fun _ nope => False.elim (Option.noConfusion nope)⟩
  
  noncomputable def ordIn (m: Morphism wa wb): wb.succ.T
  :=
    (ordIn.prop m).val
  
  namespace ordIn
    def ltNFree
      (m: Morphism.Initial wa wb)
      (b: wb.T)
      (bLtOrd: wb.succ.lt (some b) (ordIn m.val))
    :
      ¬ m.val.free b
    :=
      let notAll: ¬ ∀ bb: wb.T,
        some b = some bb → Morphism.free m.val bb :=
      (ordIn.prop m.val).property.right (some b) bLtOrd
      
      let exTmp: ∃ _: wb.T,
        ¬ (some b = some b → Morphism.free m.val b)
        --some mabOrdC = some c ∧ ¬ Morphism.free mac.val c
      :=
        ⟨b, fun p => notAll
          fun _ eqSome => Option.noConfusion eqSome id ▸ (p rfl)⟩
      
      exTmp.elim fun _ p =>
        -- All hail classical logic.
        if hRight: Morphism.free m.val b then
          False.elim (p fun _ => hRight)
        else if hLeft: some b = some b then
          Option.noConfusion hLeft fun eq => eq ▸ hRight
        else False.elim (p fun left => False.elim (hLeft left))
    
    def ltBound
      (m: Morphism.Initial wa wb)
      (b: wb.T)
      (bLtOrd: wb.succ.lt (some b) (ordIn m.val))
    :
      m.val.bound b
    :=
      byContradiction fun nope =>
        Morphism.nFreeBound (ltNFree m b bLtOrd) nope
    
    noncomputable def eqIso
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (ordInEq: ordIn mac.val = ordIn mbc.val)
    :
      Isomorphism wa wb
    :=
      let mirrorBound
        {w wo: WellOrder}
        (mwc: Morphism.Initial w wc)
        (moc: Morphism.Initial wo wc)
        (a: w.T)
        (ordInEq: ordIn mwc.val = ordIn moc.val)
      :
        moc.val.bound (mwc.val.f a)
      :=
        let c: wc.T := mwc.val.f a
        let mwcOrd := ordIn mwc.val
        let mocOrd := ordIn moc.val
        let ordEq: mwcOrd = mocOrd := ordInEq
        
        let someCLtMwcOrd: wc.succ.lt (some c) mwcOrd :=
          let ccLtBound (cc: wc.T) (ccLtC: cc < c): mwc.val.bound cc :=
            mwc.property a cc ccLtC
          (wc.succ.total (some c) mwcOrd).elim id
            (fun gtOrEq => gtOrEq.elim
              (fun gt =>
                let mwcOrdInner: { c // mwcOrd = some c } :=
                  match mwcOrd with
                    | none => False.elim gt
                    | some c => ⟨c, rfl⟩
                
                let gtPrev: mwcOrdInner < c :=
                  (succ.ordPress wc mwcOrdInner c).mpr (mwcOrdInner.property ▸ gt)
                let mwcOrdBound: mwc.val.bound mwcOrdInner :=
                  ccLtBound mwcOrdInner gtPrev
                let mwcOrdFree: mwc.val.free mwcOrdInner :=
                  (ordIn.prop mwc.val).property.left mwcOrdInner mwcOrdInner.property
                Morphism.freeBound mwcOrdFree mwcOrdBound)
              (fun eq =>
                let mwcOrdBound: mwc.val.bound c := ⟨a, rfl⟩
                let mwcOrdFree: mwc.val.free c :=
                  (ordIn.prop mwc.val).property.left c eq.symm
                Morphism.freeBound mwcOrdFree mwcOrdBound))
        
        let someCLtMocOrd: wc.succ.lt (some c) mocOrd := ordEq ▸ someCLtMwcOrd
        ordIn.ltBound moc c someCLtMocOrd
      
      let f (a: wa.T): { b: wb.T // mac.val.f a = mbc.val.f b } :=
        let c: wc.T := mac.val.f a
        let cBoundMbc: mbc.val.bound c := mirrorBound mac mbc a ordInEq
        
        choiceEx cBoundMbc
      
      let g (b: wb.T): { a: wa.T // mbc.val.f b = mac.val.f a } :=
        let c: wc.T := mbc.val.f b
        let cBoundMbc: mac.val.bound c := mirrorBound mbc mac b ordInEq.symm
        
        choiceEx cBoundMbc
      
      let fMono (a0 a1: wa.T) (ltA: a0 < a1): (f a0).val < (f a1).val :=
        let c0 := mac.val.f a0
        let c1 := mac.val.f a1
        let ltC: c0 < c1 := (mac.val.ordPres a0 a1).mp ltA
        
        let cf0 := mbc.val.f (f a0)
        let cf1 := mbc.val.f (f a1)
        
        let eqCf0: cf0 = c0 := (f a0).property.symm
        let eqCf1: cf1 = c1 := (f a1).property.symm
        
        let ltCf: cf0 < cf1 := eqCf0 ▸ eqCf1 ▸ ltC
        (mbc.val.ordPres (f a0) (f a1)).mpr ltCf
      
      {
        f := fun a => f a
        g := fun a => g a
        
        bijA := fun a =>
          let c: wc.T := mac.val.f a
          let faBoundMbc: c = mbc.val.f (f a) := (f a).property
          
          let faBoundMac: c = mac.val.f (g (f a)) :=
            faBoundMbc.symm ▸ (g (f a)).property
          
          (mac.val.ordPresEq faBoundMac).symm
        
        bijB := fun b =>
          let c: wc.T := mbc.val.f b
          let faBoundMbc: c = mac.val.f (g b) := (g b).property
          
          let faBoundMac: c = mbc.val.f (f (g b)) :=
            faBoundMbc.symm ▸ (f (g b)).property
          
          (mbc.val.ordPresEq faBoundMac).symm
        
        ordPres := fun a0 a1 =>
          Iff.intro
            (fMono a0 a1)
            fun ltFA => @monoInvMono wa.T wb.T (fun a => f a)
              a0 a1 (wfWT wa) (wfWT wb) ltFA wa.total fMono
      }
    
    def eqIsIso
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (ordInEq: ordIn mac.val = ordIn mbc.val)
    :
      isIsomorphic wa wb
    :=
      ⟨eqIso mac mbc ordInEq, trivial⟩
    
    -- TODO do I need you?
    def self.eqNone (m: Morphism.Initial w w): ordIn m.val = none :=
      let mOrdEq: (ordIn.prop m.val).val = ordIn m.val := rfl
      match h: ordIn.prop m.val with
        | ⟨none, _⟩ => mOrdEq ▸ (congr rfl h)
        | ⟨some b, prop⟩ =>
          let bFree := prop.left b rfl
          let bNFree: m.val.bound b := ⟨
            b,
            (Morphism.self.initial.eqId m) ▸ rfl
          ⟩
          Morphism.freeBound bFree bNFree
    
    def ltIfMetaLt
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (mlt: metaLt wa wb)
    :
      ordIn mac.val < ordIn mbc.val
    :=
      let mab: Morphism.Initial wa wb := Morphism.initial (choiceEx mlt.right)
      let mbb: Morphism.Initial wb wb := Morphism.refl wb
      
      let mbbOrdEq: (ordIn.prop mbb.val).val = ordIn mbb.val := rfl
      
      let mbbOrdNone: ordIn mbb.val = none :=
        match h: ordIn.prop mbb.val with
          | ⟨none, _⟩ => mbbOrdEq ▸ (congr rfl h)
          | ⟨some b, prop⟩ =>
            let bFree := prop.left b rfl
            let bNFree: mbb.val.bound b := ⟨b, rfl⟩
            Morphism.freeBound bFree bNFree
      
      let mabOrdSome: ordIn mab.val ≠ none :=
        fun eqTmp =>
          let eq: ordIn mab.val = ordIn mbb.val := mbbOrdNone ▸ eqTmp
          let isIso := ordIn.eqIsIso mab mbb eq
          mlt.left isIso
      
      let mabOrd: { b: wb.T // some b = ordIn mab.val } :=
        match h: ordIn mab.val with
          | none => False.elim (mabOrdSome h)
          | some a => ⟨a, rfl⟩
      
      let mabOrdC := (mbc.val.f mabOrd.val)
      
      let mabOrdBoundInMbc: mbc.val.bound mabOrdC :=
        ⟨mabOrd.val, rfl⟩
      
      let mabOrdNBoundInMac: ¬ mac.val.bound mabOrdC :=
        fun bound =>
          let a := choiceEx bound
          let mabA := mab.val.f a
          let mabBoundA: mab.val.bound mabA := ⟨a, rfl⟩
          (wb.total mabA mabOrd.val).elim
            (fun lt =>
              let eqTmpTmp: mac.val.f a.val = mbc.val.f (mabA) :=
                (initial.trans.eq.helper mab mbc mac a).symm
              let eqTmp: mabOrdC = mbc.val.f (mabA) :=
                a.property ▸ eqTmpTmp
              let eq: mabOrd.val = mabA := mbc.val.ordPresEq eqTmp
              wfRel.irefl mabA (eq ▸ lt))
            fun gtOrEq =>
              let mabOrdBound: mab.val.bound mabOrd := gtOrEq.elim
                (fun gt => mab.property a mabOrd.val gt)
                (fun eq => eq ▸ mabBoundA)
              let mabOrdFree: mab.val.free mabOrd :=
                (ordIn.prop mab.val).property.left mabOrd mabOrd.property.symm
              Morphism.freeBound mabOrdFree mabOrdBound
      
      let ordMbcGtMabOrdC:
        wc.succ.lt (some mabOrdC) (ordIn.prop mbc.val).val
      :=
        match h: (ordIn.prop mbc.val).val with
          | none => trivial
          | some obc =>
              (wc.total mabOrdC obc).elim id
                fun gtOrEq =>
                  let obcFree: mbc.val.free obc :=
                    (ordIn.prop mbc.val).property.left obc h
                  let obcBound: mbc.val.bound obc :=
                    gtOrEq.elim
                      (fun gt => mbc.property mabOrd.val obc gt)
                      (fun eq => eq ▸ mabOrdBoundInMbc)
                  Morphism.freeBound obcFree obcBound
      
      
      let ordMacLtMabOrdC:
        wc.succ.lt (ordIn mac.val) (some mabOrdC) ∨ ordIn mac.val = some mabOrdC
      :=
        (wc.succ.total (ordIn mac.val) (some mabOrdC)).elim
          (fun lt => Or.inl lt)
          fun gtOrEq => gtOrEq.elim
            (fun gt => Morphism.nFreeBound
              (ltNFree mac mabOrdC gt) mabOrdNBoundInMac)
          (fun eq => Or.inr eq)
        
      
      ordMacLtMabOrdC.elim
        (fun lt => WellOrder.lt.trans lt ordMbcGtMabOrdC)
        (fun eq => eq ▸ ordMbcGtMabOrdC)
  end ordIn  
  
  def metaWf (wc: WellOrder): Acc metaLt wc :=
    let fix := WellFounded.fix wc.succ.wf fun
      (tSucc: wc.succ.T)
      (rc:
        (ttSucc: wc.succ.T) →
        wc.succ.lt ttSucc tSucc →
        (wa: { wa: WellOrder //
          ∃ m: Morphism wa wc, Morphism.isInitial m ∧
            (ordIn m < ttSucc ∨ ordIn m = ttSucc) }) →
        Acc metaLt wa)
      =>
        fun wb => Acc.intro wb.val fun wa waLtWb =>
          let mbc := choiceEx wb.property
          let mbcIni: Morphism.Initial wb wc := ⟨mbc.val, mbc.property.left⟩
          
          let mbtOrd: ordIn mbc.val < tSucc ∨ ordIn mbc.val = tSucc :=
            mbc.property.right
          
          let mab: Morphism wa wb := choiceEx waLtWb.right
          let mabIni := Morphism.initial mab
          
          let mac := mabIni.val.trans mbc.val
          let macIni := Morphism.initial mac
          
          let mabOrdLt: (ordIn macIni.val) < (ordIn mbc.val) :=
            (ordIn.ltIfMetaLt macIni mbcIni) waLtWb
          
          let macOrdLtTSucc: (ordIn macIni.val) < tSucc := mbtOrd.elim
            (fun lt => WellOrder.lt.trans mabOrdLt lt)
            (fun eq => eq ▸ mabOrdLt)
          
          let ex: ∃ m: Morphism wa wc, Morphism.isInitial m ∧
            (ordIn m < ordIn macIni.val ∨ ordIn m = ordIn macIni.val)
          :=
            ⟨macIni, And.intro macIni.property (Or.inr rfl)⟩
          
          rc (ordIn macIni.val) macOrdLtTSucc ⟨wa, ex⟩
    
    fix none ⟨
      wc,
      ⟨
        (WellOrder.Isomorphism.refl wc).morphismF,
        And.intro
          (WellOrder.Isomorphism.morphismF.isInitial
            (WellOrder.Isomorphism.refl wc))
          (
            let isoWc: Isomorphism wc wc := Isomorphism.refl wc
            let mf: Morphism wc wc := isoWc.morphismF
            
            let ordInMf := ordIn mf
            let ordInPropMf := ordIn.prop mf
            let ordInEq: ordInMf = ordInPropMf.val := rfl
            
            match h: ordInPropMf with
              | ⟨none, _⟩ =>
                  let eq: ordInPropMf.val = none := by simp [h]
                  Or.inr (ordInEq.trans eq)
              | ⟨some b, prf⟩ =>
                  let bNotFree := (Isomorphism.notFree isoWc b)
                  let bFree := prf.left b rfl
                  
                  False.elim (bNotFree bFree)
          )
      ⟩
    ⟩
  
end WellOrder


instance: WellFoundedRelation WellOrder where
  rel := WellOrder.metaLt
  wf := ⟨WellOrder.metaWf⟩


instance wellOrderSetoid: Setoid WellOrder where
  r (a b: WellOrder) := WellOrder.isIsomorphic a b
  iseqv := {
    -- `refl := fun x => ⟨x.Isomorphism.refl, trivial⟩` should work >:( 
    refl := fun x => ⟨WellOrder.Isomorphism.refl x, trivial⟩
    symm := fun isIsm => isIsm.elim fun i _ => ⟨i.symm, trivial⟩
    trans := fun ab bc =>
      ab.elim fun iab _ =>
        bc.elim fun ibc _ =>
          ⟨WellOrder.Isomorphism.trans iab ibc, trivial⟩
  }



@[reducible] noncomputable def getRep
  {s: Setoid T}
  (q: Quotient s)
:
  { t: T // Quotient.mk s t = q }
:=
  choiceEx (@Quotient.exists_rep T s q)

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
  
  def succ.iso
    (wa wb: WellOrder)
    (iso: WellOrder.Isomorphism wa wb)
  :
    WellOrder.Isomorphism wa.succ wb.succ
  := {
    f := fun a =>
      match a with
        | none => none
        | some a => some (iso.f a)
    g := fun b => 
      match b with
        | none => none
        | some b => some (iso.g b)
    
    -- I hate to admit it, but I'm starting to like tactics.
    -- But only because Lean needs better symbolic execution instead!!! ;)
    bijA := fun a => by cases a <;> simp [iso.bijA],
    bijB := fun b => by cases b <;> simp [iso.bijB],
    
    ordPres := fun a b =>
      match a, b with
        -- Lean's 'by simp' has issues if it cannot come up with
        -- the zeroth three.
        | none, none => Iff.intro id id
        | some a, none => Iff.intro id id
        | none, some a => Iff.intro id id
        | some a, some b => Iff.intro
            (fun succLtAB => (iso.ordPres a b).mp succLtAB)
            (fun succLtAB => (iso.ordPres a b).mpr succLtAB)
  }
  
  def succ: Ordinal → Ordinal := Quotient.lift (fun w => Ordinal.mk w.succ)
    fun (wa wb: WellOrder) (asimb: wa ≈ wb) =>
      let iso: WellOrder.Isomorphism wa wb := choiceEx asimb
      
      Quotient.sound ⟨succ.iso wa wb iso, trivial⟩
  
  noncomputable def pred.mid (w: WellOrder): Option Ordinal :=
    match w.pred with
      | none => none
      | some a => some (Ordinal.mk a)
  
  def predRespects
    (wa wb: WellOrder)
    (asimb: wa ≈ wb)
  :
    pred.mid wa = pred.mid wb
  :=    
    match wap: wa.pred, wbp: wb.pred with
      | none, none => by unfold pred.mid; simp [wap, wbp]
      | none, some b =>
          let waPred := WellOrder.pred.iso wb wa asimb.symm ⟨b, wbp⟩
          let nope: none = some waPred.val := wap ▸ waPred.property.left
          Option.noConfusion nope
      | some a, none =>
          let wbPred := WellOrder.pred.iso wa wb asimb ⟨a, wap⟩
          let nope: none = some wbPred.val := wbp ▸ wbPred.property.left
          Option.noConfusion nope
      | some a, some b =>
          let wbPred := WellOrder.pred.iso wa wb asimb ⟨a, wap⟩
          
          let isoAB: WellOrder.isIsomorphic a b :=
            WellOrder.isIsomorphic.trans
              wbPred.property.right
              (
                let someEq: some b = some wbPred.val := wbp ▸ wbPred.property.left
                let bEq: b = wbPred.val := Option.noConfusion someEq id
                bEq ▸ WellOrder.isIsomorphic.refl
              )
          
          let eqMkAB: mk a = mk b := Quotient.sound isoAB
          
          let waEq: pred.mid wa = some (Ordinal.mk a) := by
            unfold pred.mid
            rw [wap]
          let wbEq: pred.mid wb = some (Ordinal.mk b) := by
            unfold pred.mid
            rw [wbp]
          let mkSomeAB: some (mk a) = some (mk b) := congr rfl eqMkAB
          waEq ▸ wbEq ▸ mkSomeAB
  
  noncomputable def pred: Ordinal → Option Ordinal :=
    Quotient.lift pred.mid predRespects
  
  /-noncomputable def predProp.mid (w: WellOrder):
    { nPredOpt: Option Ordinal //
      ∀ nPred, nPredOpt = some nPred → nPred.succ = mk w }
  :=
    match h: w.predProp.val with
      | none => ⟨none, fun _ nope => Option.noConfusion nope⟩
      | some pred => ⟨some (Ordinal.mk pred),
          fun p eq =>
            let pEqMkPred: p = Ordinal.mk pred :=
              (Option.noConfusion eq id).symm
            let succPredIsoW := w.predProp.property pred h
            let succMkPredEq: succ (mk pred) = mk w :=
              Quotient.sound succPredIsoW
            pEqMkPred ▸ succMkPredEq⟩
  
  def predProp.helperNone (w: WellOrder) (eq: w.predProp.val = none):
    predProp.mid w = ⟨none, fun _ nope => Option.noConfusion nope⟩
  :=
    sorry
  
  
  def predProp.helperSome (w a: WellOrder) (eqW: w.predProp.val = some a):
    predProp.mid w = ⟨some (mk a), fun p eq =>
            let pEqMkPred: p = Ordinal.mk a :=
              (Option.noConfusion eq id).symm
            let succPredIsoW := w.predProp.property a eqW
            let succMkPredEq: succ (mk a) = mk w :=
              Quotient.sound succPredIsoW
            pEqMkPred ▸ succMkPredEq⟩
  :=
    sorry
  
  /-noncomputable def pred.eqPredProp (n: Ordinal): n.pred = n.predProp :=
    { nPredOpt: Option Ordinal //
      ∀ nPred, nPredOpt = some nPred → nPred.succ = n }
  :=
    Quotient.rec predProp.mid fun wa wb (simAB: wa ≈ wb) =>-/
  
  noncomputable def predProp (n: Ordinal):
    { nPredOpt: Option Ordinal //
      ∀ nPred, nPredOpt = some nPred → nPred.succ = n }
  :=
    Quotient.hrecOn n predProp.mid fun wa wb (simAB: wa ≈ wb) =>
      let nEq: mk wa = mk wb := Quotient.sound simAB
      
      let predMidEq: pred.mid wa = pred.mid wb := predRespects wa wb simAB
      
      let predEqPropMid (wa: WellOrder): pred.mid wa = predProp.mid wa :=
        let aPredEqProp: wa.pred = wa.predProp.val := WellOrder.pred.eqPredProp wa
        match h: wa.pred with
          | none =>
              let predMidWaNone: pred.mid wa = none :=
                by unfold pred.mid; simp [h]
              let waPredPropNone: (wa.predProp).val = none := aPredEqProp ▸ h
              let propNone: predProp.mid wa = ⟨none, _⟩ :=
                predProp.helperNone wa waPredPropNone
              let propNoneVal: (predProp.mid wa).val = none := congr rfl propNone
              predMidWaNone.trans propNoneVal.symm
          | some a =>
              let predMidWaNone: pred.mid wa = some (mk a) :=
                by unfold pred.mid; simp [h]
              let waPredPropNone: (wa.predProp).val = (some a) :=
                aPredEqProp ▸ h
              let propNone: predProp.mid wa = ⟨some (mk a), _⟩ :=
                predProp.helperSome wa a waPredPropNone
              let propNoneVal: (predProp.mid wa).val = some (mk a) :=
                congr rfl propNone
              predMidWaNone.trans propNoneVal.symm
      
      let aPredEqPropMid: pred.mid wa = predProp.mid wa := predEqPropMid wa
      let bPredEqPropMid: pred.mid wb = predProp.mid wb := predEqPropMid wb
      
      let predPropEq: (predProp.mid wa).val = (predProp.mid wb).val :=
        (aPredEqPropMid.symm.trans predMidEq).trans bPredEqPropMid
      
      sorry-/
  
  def isLimit (o: Ordinal): Prop := o.pred = none
  
  
  noncomputable def predProp (n: Ordinal):
    { nPredOpt: Option Ordinal //
      ∀ nPred: Ordinal, nPredOpt = some nPred → nPred.succ = n }
  :=
    if isLimit n then
      ⟨none, by simp⟩
    else ⟨
      n.pred,
      fun pred eqNPred =>
        let nRep := getRep n
        let predRep := getRep pred
        
        let eqNPredMid: Ordinal.pred n = Ordinal.pred.mid nRep.val :=
          Quotient.lift.eq Ordinal.pred.mid predRespects
            nRep.val n nRep.property.symm
        
        let eqPredMid: Ordinal.pred.mid nRep.val = some pred :=
          eqNPred ▸ eqNPredMid.symm
        
        match h: nRep.val.pred with
          | none =>
              let midSimp: Ordinal.pred.mid nRep.val = none :=
                by unfold pred.mid; rw [h]
              let nope: Ordinal.pred n = none := nRep.property ▸ midSimp
              
              False.elim (Option.noConfusion (eqNPred ▸ nope))
          | some nRepPred =>
              let midSimp: Ordinal.pred.mid nRep.val = some (mk nRepPred) :=
                by unfold pred.mid; rw [h]
              
              let someEq: some (mk nRepPred) = some pred :=
                midSimp.symm.trans eqPredMid
              
              let mkEq: mk nRepPred = mk predRep :=
                Option.noConfusion someEq
                  fun eq => eq.trans predRep.property.symm
              
              let isoPred: WellOrder.isIsomorphic nRepPred predRep.val :=
                Quotient.exact mkEq
              
              let eqProp: nRep.val.pred = nRep.val.predProp :=
                WellOrder.pred.eqPredProp nRep
              
              let hh: nRep.val.predProp = some nRepPred := eqProp ▸ h
              
              let isIsoNRepPred: WellOrder.isIsomorphic nRepPred.succ nRep :=
                nRep.val.predProp.property nRepPred (eqProp ▸ hh ▸ eqProp)
              
              let isIsoPredRep:
                WellOrder.isIsomorphic predRep.val.succ nRepPred.succ
              := ⟨
                succ.iso predRep.val nRepPred (choiceEx isoPred).val.symm,
                trivial
              ⟩
              
              let isIso: WellOrder.isIsomorphic predRep.val.succ nRep :=
                isIsoPredRep.trans isIsoNRepPred
              
              predRep.property ▸ nRep.property ▸ Quotient.sound isIso
    ⟩
  
  noncomputable def pred.eqPredProp (n: Ordinal): n.pred = n.predProp :=
    if h: n.isLimit then
      let nPredPropEq: n.predProp = ⟨none, _⟩ := if_pos h
      let nPredPropEqVal: n.predProp.val = none := congr rfl nPredPropEq
      let nPredEq: n.pred = none := h
      nPredEq.trans nPredPropEqVal.symm
    else
      let nPredPropEq: ⟨n.pred, _⟩ = n.predProp := (if_neg h).symm
      congr (show Subtype.val = Subtype.val from rfl) nPredPropEq
  
  noncomputable def predSucc (n: Ordinal) (isSucc: ¬ isLimit n):
    { pred: Ordinal // pred.succ = n }
  :=
    match hh: n.predProp with
      | ⟨none, _⟩ =>
          let predPropNone: n.predProp.val = none := congr rfl hh
          False.elim (isSucc ((pred.eqPredProp n).trans predPropNone))
      | ⟨some nn, succN⟩ => ⟨nn, succN nn rfl⟩
  
  def lt: Ordinal → Ordinal → Prop :=
    Quotient.lift₂ WellOrder.metaLt
      fun
        (wa0 wb0 wa1 wb1: WellOrder)
        (simA: wa0 ≈ wa1)
        (simB: wb0 ≈ wb1)
      =>
        let mp
          (wx0 wy0 wx1 wy1: WellOrder)
          (simX: wx0 ≈ wx1)
          (simY: wy0 ≈ wy1)
        :
          wx0.metaLt wy0 → wx1.metaLt wy1
        :=
          fun lt0 =>
            let xyNIso0: ¬ WellOrder.isIsomorphic wx0 wy0 := lt0.left
            let xyNIso1: ¬ WellOrder.isIsomorphic wx1 wy1 :=
              fun iso1 => xyNIso0 ((simX.trans iso1).trans simY.symm)
                
            let isoX: WellOrder.Isomorphism wx0 wx1 := choiceEx simX
            let isoY: WellOrder.Isomorphism wy0 wy1 := choiceEx simY
            
            let mxy0: WellOrder.Morphism wx0 wy0 := choiceEx lt0.right
            let mxy1: WellOrder.Morphism wx1 wy1 :=
              (isoX.morphismG.trans mxy0).trans isoY.morphismF
            
            And.intro xyNIso1 ⟨mxy1, trivial⟩
        
        let iff: wa0.metaLt wb0 ↔ wa1.metaLt wb1 :=
          Iff.intro
            (mp wa0 wb0 wa1 wb1 simA simB)
            (mp wa1 wb1 wa0 wb0 simA.symm simB.symm)
        
        propext iff
  
  def wfLt (w: WellOrder): Acc lt (Ordinal.mk w) :=
    Acc.intro (Ordinal.mk w) fun wwOrd wwLtW =>
      let ww := choiceEx (Quotient.exists_rep wwOrd)
      
      let eq: wwOrd = Ordinal.mk ww := ww.property.symm
      
      let lt: lt (Ordinal.mk ww) (Ordinal.mk w) := eq ▸ wwLtW
      
      have: WellOrder.metaLt ww w := lt
      ww.property ▸ wfLt ww
    termination_by wfLt w => w
  
  def wf (o: Ordinal): Acc lt o := Quotient.ind wfLt o
end Ordinal

instance: LT Ordinal where
  lt := Ordinal.lt

instance: WellFoundedRelation Ordinal where
  rel := Ordinal.lt
  wf := ⟨Ordinal.wf⟩

instance: Coe (Ordinal) (Type 1) where
  coe o := { oo: Ordinal // oo < o }
