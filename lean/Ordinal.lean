/-
  Defines ordinals and some well-known facts about them.
  
  Don't look inside. It's embarrassing. (And also supposed
  to be write-once, forget and don't ever read again.)
-/

import Set

open Classical


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


def subtypeWellFounded
  {T: Type u}
  (s: Set T)
  [wf : WellFoundedRelation T]
:
  WellFoundedRelation (Subtype s)
:=
  invImage Subtype.val wf


def Minimal.{u} (s: Set T) (lt: T → T → Prop): Type u :=
  { t: T // t ∈ s ∧ ∀ tt: T, lt tt t → tt ∉ s }

noncomputable def minimal
  {T: Type}
  [wf: WellFoundedRelation T]
  (s: Set T)
  (nonempty: ↑s)
:
  Minimal s wf.rel
:= (
  WellFounded.fix (subtypeWellFounded s).wf fun
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

def Minimal.total.nlt
  {T: Type}
  {sa sb: Set T}
  [wf: WellFoundedRelation T]
  (ma: Minimal sa wf.rel)
  (mb: Minimal sb wf.rel)
  (setEq: sa = sb)
:
  ¬ wf.rel ma.val mb.val
:=
  fun lt =>
    mb.property.right ma.val lt (setEq ▸ ma.property.left)

def Minimal.total.eq
  {T: Type}
  {sa sb: Set T}
  [wf: WellFoundedRelation T]
  (total: ∀ a b: T, wf.rel a b ∨ wf.rel b a ∨ a = b)
  (ma: Minimal sa wf.rel)
  (mb: Minimal sb wf.rel)
  (setEq: sa = sb)
:
  ma.val = mb.val
:=
  (total ma.val mb.val).elim
    (fun lt => False.elim (nlt ma mb setEq lt))
    (fun gtOrEq => gtOrEq.elim
      (fun gt => False.elim (nlt mb ma setEq.symm gt))
      id)


def wfRel.irefl [wf: WellFoundedRelation T] (a: T):
  ¬ wf.rel a a
:=
  -- The following crashes Lean:
  -- https://github.com/leanprover/lean4/issues/1673
  --
  -- fun aLtA => False.elim ((wfRel.irefl a) aLtA)
  -- termination_by wfRel.irefl a => a
  let A := { t: T // t = a }
  let wfSub := subtypeWellFounded (fun t => t = a)
  
  fun aLtA =>
    let f := WellFounded.fix wfSub.wf fun
      (x: A)
      (rc: (xx: A) → wf.rel xx x → ¬ wf.rel a a)
    =>
      match h: x with
        | ⟨xVal, eqA⟩ =>
            rc ⟨a, rfl⟩ (eqA ▸ aLtA)
    
    f ⟨a, rfl⟩ aLtA

def wfRel.antisymm {T: Type u} [wf: WellFoundedRelation T] {a b: T}:
  wf.rel a b → wf.rel b a → a = b
:=
  let AOrB := { t: T // t = a ∨ t = b }
  let wfSub := subtypeWellFounded (fun t => t = a ∨ t = b)
  
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

-- I'd replace the former with this one, but it throws
-- "typeclass instance problem is stuck" errors :shrug:
def wfRel.antisymm.any
  {p: Prop} {T: Type u} [wf: WellFoundedRelation T] {a b: T}
:
  wf.rel a b → wf.rel b a → p
:=
  fun ab ba => False.elim (wfRel.irefl a (wfRel.antisymm ab ba ▸ ab))

-- I'd replace the former with this one, but it throws
-- "typeclass instance problem is stuck" errors :shrug:
def wfRel.antisymm.false
  {T: Type u} [wf: WellFoundedRelation T] {a b: T}
:
  wf.rel a b → ¬ wf.rel b a
:=
  fun ab ba => False.elim (wfRel.irefl a (wfRel.antisymm ab ba ▸ ab))

def wfRel.total.trans
  {T: Type u} [wf: WellFoundedRelation T] {a b c: T}
  (total: ∀ t0 t1: T, wf.rel t0 t1 ∨ wf.rel t1 t0 ∨ t0 = t1)
:
  wf.rel a b → wf.rel b c → wf.rel a c
:= (
  WellFounded.fix wf.wf fun
    (c: T)
    (rc:
      (cc: T) →
      wf.rel cc c →
      ∀ a b: T, wf.rel a b → wf.rel b cc → wf.rel a cc
    )
  =>
    fun (a b: T) aLtB bLtC =>
      (total a c).elim id (
        fun gtOrEq =>
          let cLtB: wf.rel c b := gtOrEq.elim
            (fun cLtA => rc b bLtC c a cLtA aLtB)
            (fun aEqC => aEqC ▸ aLtB)
          let bEqC: b = c := wfRel.antisymm bLtC cLtB
          let bLtB: wf.rel b b := bEqC ▸ cLtB
          let bNLtB: ¬ wf.rel b b := wfRel.irefl b
          False.elim (bNLtB bLtB)
      )
) c a b
  

def monoInvMono
  (f: A → B)
  (a0 a1: A)
  (aOrd: WellFoundedRelation A)
  (bOrd: WellFoundedRelation B)
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

namespace WellOrder
  instance wellFoundedT (w: WellOrder): WellFoundedRelation w.T where
    rel := w.lt
    wf := w.wf
  
  instance ltT (w: WellOrder): LT w.T where
    lt := w.lt
  
  def sub (w: WellOrder) (s: Set w.T): WellOrder := {
    T := Subtype s
    lt := fun t0 t1 => w.lt t0 t1
    total := fun t0 t1 => (w.total t0 t1).elim
      (fun lt => Or.inl lt) (fun gtOrEq => gtOrEq.elim
        (fun gt => Or.inr (Or.inl gt))
        (fun eq => Or.inr (Or.inr (Subtype.eq eq))))
    wf := (subtypeWellFounded s).wf
  }
  
  def lt.trans {w: WellOrder} {a b c: w.T}:
    a < b → b < c → a < c
  := 
    wfRel.total.trans w.total
  
  
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
    
    def nFree {m: Morphism wa wb} {b: wb.T} (isBound: m.bound b): ¬ m.free b :=
      fun isFree => freeBound isFree isBound
    
    def nBound {m: Morphism wa wb} {b: wb.T} (isFree: m.free b): ¬ m.bound b :=
      fun isBound => freeBound isFree isBound
    
    def nnFree {m: Morphism wa wb} {b: wb.T} (isNBound: ¬ m.bound b): m.free b :=
      dne (fun isNFree => nFreeBound isNFree isNBound)
    
    def nnBound {m: Morphism wa wb} {b: wb.T} (isNFree: ¬ m.free b): m.bound b :=
      dne (fun isNBound => nFreeBound isNFree isNBound)
    
    
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
    
    def sub (w: WellOrder) (s: Set w.T): Morphism (sub w s) w :=
      {
        f := fun t => t.val
        ordPres := fun _ _ => Iff.intro id id
      }
  end Morphism
  
  
  inductive ZeroT
  
  def zero: WellOrder := {
    T := ZeroT,
    lt := fun _ _ => False,
    total := fun nope _ => ZeroT.rec nope,
    wf := ⟨fun nope => ZeroT.rec nope⟩
  }
  
  noncomputable def zero.morphism (w: WellOrder): Morphism zero w := {
    f := fun zt => ZeroT.rec zt
    ordPres := fun zt _ => ZeroT.rec zt
  }
  
  
  structure Isomorphism (wa wb: WellOrder) where
    f: wa.T → wb.T
    g: wb.T → wa.T
    
    bijA: ∀ a: wa.T, g (f a) = a
    bijB: ∀ b: wb.T, f (g b) = b
    
    ordPres: ∀ a b: wa.T, a < b ↔ f a < f b
  
  def isIsomorphic (wa wb: WellOrder) := ∃ _: Isomorphism wa wb, True
  
  namespace Isomorphism
    def morphismF (i: Isomorphism wa wb): Morphism.Initial wa wb := ⟨
      {
        f := i.f
        ordPres := i.ordPres
      },
      fun _ b _ => ⟨i.g b, (i.bijB b).symm⟩
    ⟩
    
    def morphismG (i: Isomorphism wa wb): Morphism.Initial wb wa := ⟨
      {
        f := i.g
        ordPres := fun (a b: wb.T) => Iff.intro (
          fun ltAb =>
            ((i.bijB a) ▸ (i.bijB b) ▸ (i.ordPres (i.g a) (i.g b)).mpr) ltAb
        ) (
          fun ltAb =>
            ((i.bijB a) ▸ (i.bijB b) ▸ (i.ordPres (i.g a) (i.g b)).mp) ltAb
        )
      },
      fun _ a _ => ⟨i.f a, (i.bijA a).symm⟩
    ⟩
    
    def morphismF.isInitial
      (i: Isomorphism wa wb)
    :
      Morphism.isInitial i.morphismF.val
    :=
      fun _ b _ => ⟨i.morphismG.val.f b, (i.bijB b).symm⟩
    
    def notFree
      (i: Isomorphism wa wb)
      (b: wb.T)
    :
      ¬ Morphism.free i.morphismF.val b
    :=
      fun allFANeqB =>
        let a := i.morphismG.val.f b
        let bEqFA: b = i.morphismF.val.f a := (i.bijB b).symm
        let bNeqFA: b ≠ i.morphismF.val.f a := allFANeqB a
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
  
  instance: HasEquiv WellOrder where
    Equiv := isIsomorphic
  
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
  
  def succ.morphism (w: WellOrder): Morphism.Initial w w.succ := ⟨
    {
      f := fun a => some a
      
      -- This is another trivial statement that your theorem
      -- prover should be able to derive on its own.
      ordPres := fun _ _ => Iff.intro id id
    },
    fun _ tSucc ltTSuccT =>
      match tSucc with
        | none => False.elim ltTSuccT
        | some tt => ⟨tt, rfl⟩
  ⟩
  
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
  
  noncomputable def Morphism.initial.f.monotonic
    (m: Morphism wa wb)
    (a0 a1: wa.T)
    (ltAA: a0 < a1)
  :
    (f m a0).val < (f m a1).val
  :=
    -- I have to put parts of the implementation of `Morphism.initial.f`
    -- here, because Lean cannot mention the function in its return type.
    -- Or is there a better way?
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
          (fun ltFA => monoInvMono f a0 a1
            (wellFoundedT wa) (wellFoundedT wb) ltFA (wa.total) (initial.f.monotonic m))
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
        let isBound: mac.val.bound abc := mac.property a abc lt
        let bound := choiceEx isBound
        let boundAC := mac.val.f bound
        let boundABC := mtr.f bound
        False.elim ((wa.total bound.val a).elim
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
              wfRel.irefl abc (eq1 ▸ lt)))))
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
  
  noncomputable def Morphism.Initial.self.eqId
    (m: Morphism.Initial w w)
  :
    m.val.f = id
  :=
    let mwId: Morphism.Initial w w := Morphism.refl w
    let eq: mwId.val.trans mwId.val = m := initial.trans.eq mwId mwId m
    let leftId: (mwId.val.trans mwId.val).f = id := rfl
    eq ▸ leftId
  
  def Morphism.Initial.eq
    {mab0: Morphism.Initial wa wb}
    {mab1: Morphism.Initial wa wb}
  :
    mab0 = mab1
  :=
    let mbb: Morphism.Initial wb wb := (Morphism.refl wb)
    
    let mabMid: Morphism.Initial wa wb := ⟨
      mab0.val.trans mbb,
      let eq: mab0.val.trans mbb = mab0.val := rfl
      eq ▸ mab0.property
    ⟩
    
    let eqLeft: mab0 = mabMid := rfl
    let eqRight: mabMid = mab1 := Subtype.eq (initial.trans.eq mab0 mbb mab1)
    
    eqLeft.trans eqRight
  
  def Morphism.Initial.trans
    (iniMab: Morphism.Initial wa wb)
    (iniMbc: Morphism.Initial wb wc)
  :
    Morphism.Initial wa wc
  := ⟨
    iniMab.val.trans iniMbc,
    let iniMac: Morphism.Initial wa wc :=
      Morphism.initial (iniMab.val.trans iniMbc)
    initial.trans.eq iniMab iniMbc iniMac ▸ iniMac.property
  ⟩
  
  
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
  
  def isGreatest.iso
    {wa wb: WellOrder}
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
  
  def isNotGreatest.iso
    (wa wb: WellOrder)
    (isoAB: Isomorphism wa wb)
    (a: { t: wa.T // ¬ isGreatest wa t })
  :
    { t: wb.T // ¬ isGreatest wb t }
  := ⟨
    isoAB.f a.val,
    fun nope =>
      let aGst := (isGreatest.iso isoAB.symm ⟨isoAB.f a, nope⟩)
      a.property ((isoAB.bijA a) ▸ aGst.property)
  ⟩
  
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
    -- But there sure must be a better non-tactic way anyway! ;)
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
  
  def succ.none.isGreatest {w: WellOrder}: isGreatest w.succ none
    | none => Or.inl rfl
    | some _ => Or.inr trivial
  
  def succ.isoFNone
    {wa wb: WellOrder}
    {iso: Isomorphism wa.succ wb.succ}
  :
    iso.f none = none
  :=
    let gstA: isGreatest wa.succ none := succ.none.isGreatest
    let gstB: isGreatest wb.succ none := succ.none.isGreatest
    
    let gstF: isGreatest wb.succ (iso.f none) :=
      (isGreatest.iso iso ⟨none, gstA⟩).property
    
    isGreatest.eq gstF gstB
  
  def succ.isoGNone
    {wa wb: WellOrder}
    {iso: Isomorphism wa.succ wb.succ}
  :
    iso.g none = none
  :=
    let gstA: isGreatest wa.succ none := succ.none.isGreatest
    let gstB: isGreatest wb.succ none := succ.none.isGreatest
    
    let gstG: isGreatest wa.succ (iso.g none) :=
      (isGreatest.iso iso.symm ⟨none, gstB⟩).property
    
    isGreatest.eq gstG gstA
  
  def succ.isoFSome
    {wa wb: WellOrder}
    {iso: Isomorphism wa.succ wb.succ}
    (a: wa.T)
  :
    iso.f (some a) ≠ none
  :=
    fun eq =>
        let eqNope: iso.morphismF.val.f none = iso.morphismF.val.f (some a) :=
          succ.isoFNone.trans eq.symm
        Option.noConfusion (iso.morphismF.val.ordPresEq eqNope)
  
  def succ.isoGSome
    {wa wb: WellOrder}
    {iso: Isomorphism wa.succ wb.succ}
    (b: wb.T)
  :
    iso.g (some b) ≠ none
  :=
    fun eq =>
        let eqNope: iso.morphismG.val.f none = iso.morphismG.val.f (some b) :=
          succ.isoGNone.trans eq.symm
        Option.noConfusion (iso.morphismG.val.ordPresEq eqNope)
  
  def succ.isoInv
    (wa wb: WellOrder)
    (iso: Isomorphism wa.succ wb.succ)
  :
    Isomorphism wa wb
  :=
    let f (a: wa.T): { b: wb.T // some b = iso.f (some a) } :=
      match h: iso.f (some a) with
        | none => False.elim (succ.isoFSome a h)
        | some b => ⟨b, rfl⟩
    
    let g (b: wb.T): { a: wa.T // some a = iso.g (some b) } :=
      match h: iso.g (some b) with
        | none => False.elim (succ.isoGSome b h)
        | some b => ⟨b, rfl⟩
    
    let fMono (a0 a1: wa.T) (lta: a0 < a1): (f a0).val < (f a1).val :=
      let isoFALt: iso.f (some a0) < iso.f (some a1) :=
        (iso.ordPres (some a0) (some a1)).mp lta
      let a0Eq: iso.f (some a0) = some (f a0).val := (f a0).property.symm
      let a1Eq: iso.f (some a1) = some (f a1).val := (f a1).property.symm
      
      show wb.succ.lt (some (f a0).val) (some (f a1).val) from
        a0Eq ▸ a1Eq ▸ isoFALt
    
    {
      f := fun a => f a
      g := fun b => g b
      
      bijA := fun a =>
        let isoFSA: wb.succ.T := iso.f (some a)
        let someFA: wb.succ.T := some (f a).val
        let someGFA: wa.succ.T := some (g ((f a).val)).val
        
        let fEq: isoFSA = someFA := (f a).property.symm
        let gEq: iso.g someFA = someGFA := (g (f a).val).property.symm
        
        let gfEq: iso.g isoFSA = someGFA := by rw [fEq]; exact gEq
        -- One shame point for lean. Cannot do in one step.
        let gfEq: iso.g (iso.f (some a)) = some (g ((f a).val)).val := gfEq
        let bijA: iso.g (iso.f (some a)) = some a := iso.bijA (some a)
        
        Option.noConfusion (gfEq.symm.trans bijA) id
      
      bijB := fun b =>
        let isoGSA: wa.succ.T := iso.g (some b)
        let someGA: wa.succ.T := some (g b).val
        let someFGA: wb.succ.T := some (f ((g b).val)).val
        
        let gEq: isoGSA = someGA := (g b).property.symm
        let fEq: iso.f someGA = someFGA := (f (g b).val).property.symm
        
        let fgEq: iso.f isoGSA = someFGA := by rw [gEq]; exact fEq
        -- One shame point for lean. Cannot do in one step.
        let fgEq: iso.f (iso.g (some b)) = some (f ((g b).val)).val := fgEq
        let bijB: iso.f (iso.g (some b)) = some b := iso.bijB (some b)
        
        Option.noConfusion (fgEq.symm.trans bijB) id
      
      ordPres := fun a0 a1 => Iff.intro (fMono a0 a1)
        fun ltf => (monoInvMono (fun a => f a) a0 a1
          (wellFoundedT wa) (wellFoundedT wb) ltf wa.total fMono)
    }
  
  def succ.noMorphismBack (w: WellOrder): ¬ ∃ _: Morphism w.succ w, True :=
    fun mEx =>
      let m: Morphism.Initial w.succ w := Morphism.initial (choiceEx mEx)
      
      if h: ∃ t: w.T, m.val.f (some t) ≠ t then
        let leastT := minimal (fun t => m.val.f (some t) ≠ t) (choiceEx h)
        let fLeastT := m.val.f (some leastT.val)
        
        (w.total leastT.val fLeastT).elim
          (fun ltLeastFLeast =>
            let nBound: ¬ m.val.bound leastT.val :=
              fun isBound =>
                let bound := choiceEx isBound
                (w.succ.total (some leastT.val) bound.val).elim
                  (fun ltLeastBound =>
                    let ltBoundLeast: w.succ.lt bound.val (some leastT.val) :=
                      (m.val.ordPres bound.val (some leastT.val)).mpr
                        (bound.property ▸ ltLeastFLeast)
                    let eq: bound.val = some leastT.val :=
                      wfRel.antisymm ltBoundLeast ltLeastBound
                    leastT.property.left (eq ▸ bound.property.symm))
                  (fun gtOrEq =>
                    gtOrEq.elim
                      (fun ltBoundLeast =>
                        match h: bound.val with
                          | none => show w.succ.lt none (some leastT.val)
                              from h ▸ ltBoundLeast
                          | some bnd =>
                              let fBoundEqBound: m.val.f bound = bnd :=
                                let ltBndLeast:
                                  w.succ.lt (some bnd) (some leastT.val) :=
                                  h.symm ▸ ltBoundLeast
                                h ▸ dne (leastT.property.right bnd ltBndLeast)
                              let eq: bnd = leastT.val :=
                                fBoundEqBound.symm.trans bound.property.symm
                              leastT.property.left (eq ▸ h ▸ fBoundEqBound))
                      (fun eq => leastT.property.left (eq ▸ bound.property.symm)))
            nBound (m.property (some leastT.val) leastT.val ltLeastFLeast))
            (fun gtOrEq =>
              gtOrEq.elim
                (fun ltFLeastLeast =>
                  let ffLeastTEq := dne (leastT.property.right fLeastT ltFLeastLeast)
                  let ffLeastTLt :=
                    (m.val.ordPres (some fLeastT) (some leastT.val)).mp
                      ltFLeastLeast
                  let nope: fLeastT < fLeastT :=
                    by conv => lhs; rw [ffLeastTEq.symm] exact ffLeastTLt
                  wfRel.irefl fLeastT (nope))
                fun eq => leastT.property.left (eq.symm))
      else
        let allTId: ∀ t: w.T, m.val.f (some t) = t :=
          fun t => byContradiction fun neq => h ⟨t, neq⟩
        let tNone := m.val.f none
        let fTNone := m.val.f (some tNone)
        let fTNoneEq: fTNone = tNone := allTId tNone
        let nope: none = some tNone := m.val.ordPresEq fTNoneEq.symm
        Option.noConfusion nope
  
  def succ.nIso (w: WellOrder): ¬ w ≈ w.succ :=
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
            
            @wfRel.irefl w.succ.T (wellFoundedT w.succ) (some fLstT.val) lt2)
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
      ∀ wPred, wPredOpt = some wPred → wPred.succ ≈ w }
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
              fun ltFA => (monoInvMono f a b
                (wellFoundedT (predNoOpt w).succ) (wellFoundedT w)
                ltFA (predNoOpt w).succ.total fMono)
          },
          trivial
        ⟩
      ⟩
    else
      ⟨none, fun _ nope => Option.noConfusion nope⟩
  
  @[reducible]
  def hasGreatest (w: WellOrder): Prop := ∃ gst: w.T, isGreatest w gst
  
  noncomputable def pred (w: WellOrder): Option WellOrder :=
    if w.hasGreatest then
      some (predNoOpt w)
    else
      none
  
  def succ.hasGreatest (w: WellOrder): w.succ.hasGreatest := ⟨
    none,
    fun t =>
      match t with
        | none => Or.inl rfl
        | some _ => Or.inr trivial
  ⟩
  
  def succ.hasPred (w: WellOrder): w.succ.pred ≠ none :=
    let eq: w.succ.pred = some (predNoOpt w.succ) :=
      if_pos (WellOrder.succ.hasGreatest w)
    fun nope => Option.noConfusion (nope.symm.trans eq)
  
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
    (isIsoAB: wa ≈ wb)
  :
    WellOrder.Isomorphism wa.predNoOpt wb.predNoOpt
  :=
    let isoAB := (choiceEx isIsoAB).val
    
    let f (a: wa.predNoOpt.T): wb.predNoOpt.T :=
      isNotGreatest.iso wa wb isoAB a
    let g (b: wb.predNoOpt.T): wa.predNoOpt.T :=
      isNotGreatest.iso wb wa isoAB.symm b
    
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
    {wa wb: WellOrder}
    (isIsoAB: wa ≈ wb)
    (waPred: { waPred: WellOrder // wa.pred = some waPred })
  :
    { wbPred: WellOrder //
        wb.pred = some wbPred ∧ waPred.val ≈ wbPred }
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
        let wbGst := isGreatest.iso isoAB waGst
        let nope: False := h ⟨wbGst, wbGst.property⟩
        -- How can I do this without choice?
        let nopeEx: ∃ wbPred: WellOrder, _ := False.elim nope
        choiceEx nopeEx
    
    
    let waPredEq: wa.predNoOpt = waPred.val :=
      if h: ∃ gst, isGreatest wa gst then
        let eqL: some wa.predNoOpt = wa.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (eqL.trans waPred.property) id
      else
        let eq: none = wa.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (eq.trans waPred.property)
    
    let wbPredEq: wb.predNoOpt = wbPred.val :=
      if h: ∃ gst, isGreatest wb gst then
        let eqL: some wb.predNoOpt = wb.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (eqL.trans wbPred.property) id
      else
        let eq: none = wb.pred := by
          unfold pred
          simp [h]
        Option.noConfusion (eq.trans wbPred.property)
    
    let isoPred: waPred.val ≈ wbPred.val :=
      waPredEq ▸ wbPredEq ▸ ⟨predNoOpt.iso wa wb ⟨isoAB, trivial⟩, trivial⟩
    
    ⟨wbPred, And.intro wbPred.property isoPred⟩
  
  
  def metaLt (wa wb: WellOrder): Prop :=
    ¬ wa ≈ wb ∧ ∃ _: Morphism wa wb, True
  
  instance: LT WellOrder where
    lt := WellOrder.metaLt
  
  -- Should have been `some b < bSucc → m.bound b` (I think),
  -- but I don't wanna touch certain code below again.
  -- Now I will suffer for my mystakes.
  noncomputable def ordIn.set (m: Morphism wa wb): Set wb.succ.T :=
    fun bSucc: wb.succ.T => ∀ b: wb.T, bSucc = some b → m.free b
  
  noncomputable def ordIn.prop
    (m: Morphism wa wb)
  :
    Minimal (ordIn.set m) wb.succ.lt
  :=
    @minimal wb.succ.T (wellFoundedT wb.succ) (ordIn.set m)
      ⟨none, fun _ nope => False.elim (Option.noConfusion nope)⟩
  
  noncomputable def ordIn (m: Morphism wa wb): wb.succ.T
  :=
    (ordIn.prop m).val
  
  namespace ordIn
    def eq
      {mac: Morphism wa wc}
      {mbc: Morphism wb wc}
      (setEq: ordIn.set mac = ordIn.set mbc)
    :
      ordIn mac = ordIn mbc
    :=
      Minimal.total.eq wc.succ.total (ordIn.prop mac) (ordIn.prop mbc) setEq
    
    def set.eq
      {mac: Morphism wa wc}
      {mbc: Morphism wb wc}
      (boundEq: ∀ c: wc.T, mac.bound c ↔ mbc.bound c)
    :
      ordIn.set mac = ordIn.set mbc
    :=
      let mp
        {wx wy wz: WellOrder}
        {mxz: Morphism wx wz}
        {myz: Morphism wy wz}
        (boundImpl: ∀ z: wz.T, mxz.bound z → myz.bound z)
        (zSucc: wz.succ.T)
      : set myz zSucc → set mxz zSucc
      :=
        let freeImpl: ∀ z: wz.T, myz.free z → mxz.free z :=
          fun z freeYZ =>
            let nBoundYZ: ¬ myz.bound z := myz.nBound freeYZ
            let nBoundXZ := contra (boundImpl z) nBoundYZ
            Morphism.nnFree nBoundXZ
        
        fun setY =>
          match zSucc with
            | none => fun _ nope => Option.noConfusion nope
            | some z =>
                let freeZY: myz.free z := setY z rfl
                fun zAgain eqSome =>
                  let eq: z = zAgain := Option.noConfusion eqSome id
                  eq ▸ freeImpl z freeZY
      
      funext (fun cSucc => propext (Iff.intro
        (fun setA => (mp (fun c => (boundEq c).mpr) cSucc) setA)
        (fun setB => (mp (fun c => (boundEq c).mp) cSucc) setB)))
    
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
    
    def boundLt
      (m: Morphism.Initial wa wb)
      (b: wb.T)
      (bIsBound: m.val.bound b)
    :
      wb.succ.lt (some b) (ordIn m.val)
    :=
    let a := choiceEx bIsBound
    
    (wb.succ.total (some b) (ordIn m.val)).elim id
      (fun gtOrEq =>
        gtOrEq.elim
          (fun gt =>
            match h: ordIn m.val with
                                    -- Fuck you, Lean.
              | none => False.elim (show wb.succ.lt none (some _) from h ▸ gt)
              | some ord =>
                  let ltSucc: wb.succ.lt (some ord) (some (m.val.f a)) :=
                    h ▸ a.property ▸ gt
                  Morphism.freeBound
                    ((ordIn.prop m.val).property.left ord h)
                    (m.property a ord ltSucc))
          fun eq => False.elim
            (Morphism.freeBound
              ((ordIn.prop m.val).property.left b eq.symm)
              bIsBound))
    
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
            fun ltFA => monoInvMono (fun a => f a)
              a0 a1 (wellFoundedT wa) (wellFoundedT wb) ltFA wa.total fMono
      }
    
    def eqIsIso
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (ordInEq: ordIn mac.val = ordIn mbc.val)
    :
      wa ≈ wb
    :=
      ⟨eqIso mac mbc ordInEq, trivial⟩
    
    noncomputable def isoLE
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (mab: Morphism.Initial wa wb)
      (c: wc.T)
      (isBoundAC: mac.val.bound c)
    :
      mbc.val.bound c
    :=
      let mabc: Morphism.Initial wa wc :=
        Morphism.Initial.trans mab mbc
      let mEq: mac = mabc := Morphism.Initial.eq
      
      let boundAC: { a: wa.T // c = mac.val.f a } := choiceEx isBoundAC
      let boundBC: wb.T := mab.val.f boundAC.val
      
      -- Definitional equality showing its limitations once again.. >:
      -- Rewriting `(mab.val.f boundAC.val)` to `boundBC` causes an error.
      let isBoundABC: c = mbc.val.f (mab.val.f boundAC.val) :=
        mEq ▸ boundAC.property
      
      ⟨boundBC, isBoundABC⟩
    
    noncomputable def isoEq
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (iab: Isomorphism wa wb)
    :
      ordIn mac.val = ordIn mbc.val
    :=
      ordIn.eq (ordIn.set.eq (fun c => Iff.intro
        (isoLE mac mbc iab.morphismF c) (isoLE mbc mac iab.morphismG c)))
    
    def self.eqNone (m: Morphism.Initial w w): ordIn m.val = none :=
      let mOrdEq: (ordIn.prop m.val).val = ordIn m.val := rfl
      match h: ordIn.prop m.val with
        | ⟨none, _⟩ => mOrdEq ▸ (congr rfl h)
        | ⟨some b, prop⟩ =>
          let bFree := prop.left b rfl
          let bNFree: m.val.bound b := ⟨
            b,
            (Morphism.Initial.self.eqId m) ▸ rfl
          ⟩
          Morphism.freeBound bFree bNFree
    
    def lt.notNone
      (mab: Morphism.Initial wa wb)
      (ab: wa < wb)
    :
      ordIn mab.val ≠ none
    :=
      let mbb: Morphism.Initial wb wb := Morphism.refl wb
      let mbbOrdEq: (ordIn.prop mbb.val).val = ordIn mbb.val := rfl
      
      let mbbOrdNone: ordIn mbb.val = none :=
        match h: ordIn.prop mbb.val with
          | ⟨none, _⟩ => mbbOrdEq ▸ (congr rfl h)
          | ⟨some b, prop⟩ =>
            let bFree := prop.left b rfl
            let bNFree: mbb.val.bound b := ⟨b, rfl⟩
            Morphism.freeBound bFree bNFree
      
      fun eqTmp =>
        let eq: ordIn mab.val = ordIn mbb.val := mbbOrdNone ▸ eqTmp
        let isIso := ordIn.eqIsIso mab mbb eq
        ab.left isIso
    
    
    def ltIfMetaLt
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (ab: wa < wb)
    :
      ordIn mac.val < ordIn mbc.val
    :=
      let mab: Morphism.Initial wa wb := Morphism.initial (choiceEx ab.right)
      
      let mabOrdSome: ordIn mab.val ≠ none := lt.notNone mab ab
      
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
  
    def metaLtIfLt
      {wa wb wc: WellOrder}
      (mac: Morphism.Initial wa wc)
      (mbc: Morphism.Initial wb wc)
      (ordInLt: ordIn mac.val < ordIn mbc.val)
    :
      wa < wb
    :=
      And.intro
        (fun isIso =>
          let iso: Isomorphism wa wb := choiceEx isIso
          let ordEq: ordIn mac.val = ordIn mbc.val := isoEq mac mbc iso
          let ltSelf: ordIn mac.val < ordIn mac.val := ordEq ▸ ordInLt
          wfRel.irefl (ordIn mac.val) ltSelf)
        ⟨
          let ltOrdIn (b: wb.T) := wc.succ.lt (some (mbc.val.f b)) (ordIn mac.val)
          let wbSub: WellOrder := wb.sub ltOrdIn
          let mbSubB: Morphism.Initial wbSub wb := ⟨
            Morphism.sub wb ltOrdIn,
            fun bSub b bLtFBSub => ⟨
              let ltLeft:
                wc.succ.lt (some (mbc.val.f b)) (some (mbc.val.f bSub.val))
              :=
                (mbc.val.ordPres b bSub.val).mp bLtFBSub
              let ltRight:
                wc.succ.lt (some (mbc.val.f bSub.val)) (ordIn mac.val)
              :=
                bSub.property
              ⟨b, WellOrder.lt.trans ltLeft ltRight⟩,
              rfl
            ⟩
          ⟩
          let mbSubC: Morphism.Initial wbSub wc :=
            Morphism.Initial.trans mbSubB mbc
          
          let ltr (c: wc.T) (boundInA: mac.val.bound c): mbSubC.val.bound c :=
            let cLtMacOrd: wc.succ.lt (some c) (ordIn mac.val) :=
              ordIn.boundLt mac c boundInA
            let cLtMbSubCOrd: wc.succ.lt (some c) (ordIn mbc.val) :=
              WellOrder.lt.trans cLtMacOrd ordInLt
            let cBoundB: mbc.val.bound c := ordIn.ltBound mbc c cLtMbSubCOrd
            let b := choiceEx cBoundB
            let ltOrdInB: wc.succ.lt (some (mbc.val.f b)) (ordIn mac.val) :=
              b.property ▸ cLtMacOrd
            let ltOrdInB: ltOrdIn b := ltOrdInB -- Fuck you Lean.
            ⟨⟨b.val, ltOrdInB⟩, b.property⟩
          
          let rtl (c: wc.T) (boundInA: mbSubC.val.bound c): mac.val.bound c :=
            let bSub := choiceEx boundInA
            let ltOrdInBSub: ltOrdIn bSub.val.val := bSub.val.property
            let ltC: wc.succ.lt (some c) (ordIn mac.val) :=
              bSub.property ▸ ltOrdInBSub
            ordIn.ltBound mac c ltC
          
          let setEq: ordIn.set mac.val = ordIn.set mbSubC.val :=
            ordIn.set.eq fun c => Iff.intro (ltr c) (rtl c)
          
          let ordEq: ordIn mac.val = ordIn mbSubC.val :=
            ordIn.eq setEq
          
          let mabSub: Morphism wa wbSub := (eqIso mac mbSubC ordEq).morphismF
          mabSub.trans mbSubB,
          trivial
        ⟩
    
    def succ.eqSomeNone
      {wa: WellOrder}
    : ordIn (succ.morphism wa).val = some none
    :=
      let wc := wa.succ
      let iniMac := succ.morphism wa
      let someBound (a: wa.T): Morphism.bound iniMac.val (some a) := ⟨a, rfl⟩
      let noneFree: Morphism.free iniMac.val none := fun _ => Option.noConfusion
      
      match h: ordIn iniMac.val with
        | none =>
            let ordInLtNone: wc.succ.lt (some none) (ordIn iniMac.val) :=
              h ▸ trivial
            False.elim
              ((ordIn.prop iniMac.val).property.right (some none) ordInLtNone
                (fun x someXNone =>
                  let xNone: none = x := Option.noConfusion someXNone id;
                  xNone ▸ noneFree))
        | some none => rfl
        | some (some a) =>
            Morphism.freeBound
              ((ordIn.prop iniMac.val).property.left (some a) h)
              (someBound a)
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
  
  instance wellFounded: WellFoundedRelation WellOrder where
    rel := WellOrder.metaLt
    wf := ⟨WellOrder.metaWf⟩
  
  
  def le (wa wb: WellOrder): Prop := wa < wb ∨ wa ≈ wb
  
  instance: LE WellOrder where
    le := le
  
  noncomputable def Morphism.le
    {wa wb: WellOrder}
    (mab: Morphism wa wb)
  :
    wa ≤ wb
  :=
    let wc := wb.succ;
    
    let iniMbc: Morphism.Initial wb wc := succ.morphism wb
    let iniMab: Morphism.Initial wa wb := Morphism.initial mab
    let iniMac: Morphism.Initial wa wc := Morphism.Initial.trans iniMab iniMbc
    
    let ordBNone: ordIn iniMbc.val = some none := ordIn.succ.eqSomeNone
    
    match h: ordIn iniMac.val with
      | none =>
          let mcc: Morphism.Initial wc wc := Morphism.refl wc
          let cOrdIn: ordIn mcc.val = none := ordIn.self.eqNone mcc
          let isoCA: Isomorphism wc wa :=
            ordIn.eqIso mcc iniMac (cOrdIn.trans h.symm)
          let mcb: Morphism wc wb :=
            isoCA.morphismF.trans iniMab
          False.elim (succ.noMorphismBack wb ⟨mcb, trivial⟩)
      | some none =>
          let ordEq: ordIn iniMac.val = ordIn iniMbc.val
            := h.trans ordBNone.symm
          Or.inr ⟨ordIn.eqIso iniMac iniMbc ordEq, trivial⟩
      | some (some _) =>
          let ordLt: ordIn iniMac.val < ordIn iniMbc.val :=
            ordBNone ▸ h ▸ trivial
          Or.inl (ordIn.metaLtIfLt iniMac iniMbc ordLt)
  
  noncomputable def isIsomorphic.fromMorphisms
    {wa wb: WellOrder}
    (mab: Morphism wa wb)
    (mba: Morphism wb wa)
  :
    wa ≈ wb
  :=
    mab.le.symm.elim id fun ltAB =>
      mba.le.symm.elim
        (fun isIso => isIso.symm)
        fun ltBA =>
          let eqAB: wa = wb := wfRel.antisymm ltAB ltBA
          eqAB ▸ isIsomorphic.refl
  
  noncomputable def Isomorphism.fromMorphisms
    {wa wb: WellOrder}
    (mab: Morphism wa wb)
    (mba: Morphism wb wa)
  :
    Isomorphism wa wb
  :=
    choiceEx (isIsomorphic.fromMorphisms mab mba)
  
  noncomputable def lt.succ.morphism {wa wb: WellOrder}
    (abs: wa < wb.succ): Morphism wa wb
  :=
    let iniABS: Morphism.Initial wa wb.succ :=
      Morphism.initial (choiceEx abs.right)
    
    match h: ordIn iniABS.val with
      | none =>
          False.elim
            (ordIn.lt.notNone iniABS abs h)
      | some ord =>
          let fNotNone
            (a: wa.T)
            (eqNone: iniABS.val.f a = none)
          :
            False
          :=
            let ltOrd: wb.succ.succ.lt (some none) (ordIn iniABS.val) :=
              ordIn.boundLt iniABS none ⟨a, eqNone.symm⟩
            show wb.succ.succ.lt (some none) (some ord) from h ▸ ltOrd
          
          let f (a: wa.T): { b: wb.T // iniABS.val.f a = some b } :=
            match h: iniABS.val.f a with
              | none => False.elim (fNotNone a h)
              | some b => ⟨b, rfl⟩
          
          let fMono (a0 a1: wa.T) (ab: a0 < a1): (f a0).val < (f a1).val :=
            let iniFLt: iniABS.val.f a0 < iniABS.val.f a1 :=
              (iniABS.val.ordPres a0 a1).mp ab
            
            let someLt
              (b0: { b0: wb.T // iniABS.val.f a0 = some b0 })
              (b1: { b1: wb.T // iniABS.val.f a1 = some b1 })
            :
              b0.val < b1.val
            :=
              show wb.succ.lt (some b0) (some b1) from
                b0.property ▸ b1.property ▸ iniFLt
            
            someLt (f a0) (f a1)
          
          {
            f := fun a => f a
            
            ordPres := fun a0 a1: wa.T => Iff.intro (fMono a0 a1)
              (fun ltFA => monoInvMono (fun a => f a)
                      a0 a1 (wellFoundedT wa) (wellFoundedT wb) ltFA wa.total fMono)
          }
  
  def ltSucc.le {wa wb: WellOrder} (abs: wa < wb.succ): wa ≤ wb :=
    let mab: Morphism wa wb := lt.succ.morphism abs
    
    if h: ∃ _: Morphism wb wa, True then
      Or.inr ⟨Isomorphism.fromMorphisms mab (choiceEx h), trivial⟩
    else
      Or.inl
        (And.intro
          (fun iso => h ⟨(choiceEx iso).val.morphismG, trivial⟩)
          ⟨mab, trivial⟩)
  
  def lt.noMiddle {p: Prop} {a b: WellOrder} (ab: a < b) (bas: b < a.succ): p :=
    let leBA: b < a ∨ b ≈ a := ltSucc.le bas
    False.elim (leBA.elim
      (fun ba => ((wfRel.irefl a) ((wfRel.antisymm ab ba) ▸ ab)))
      (fun iso => ab.left iso.symm))
  
  
  def succGt (w: WellOrder): w < w.succ :=
    And.intro (succ.nIso w) ⟨succ.morphism w, trivial⟩
  
  def succIsoGt
    (w wSucc: WellOrder)
    (iso: Isomorphism wSucc w.succ)
  :
    w < wSucc
  :=
    let nIso: ¬ ∃ _: Isomorphism w wSucc, True :=
      fun iEx =>
        let i := (choiceEx iEx).val
        (succ.nIso w) ⟨i.trans iso, trivial⟩
    
    And.intro nIso ⟨(succ.morphism w).val.trans iso.morphismG, trivial⟩
  
  def plus (wa wb: WellOrder): WellOrder :=
    let lt: (t0 t1: Sum wa.T wb.T) → Prop
      | Sum.inl a0, Sum.inl a1 => a0 < a1
      | Sum.inl _0, Sum.inr _1 => True
      | Sum.inr _0, Sum.inl _1 => False
      | Sum.inr b0, Sum.inr b1 => b0 < b1
    
    let total: (t0 t1: Sum wa.T wb.T) → lt t0 t1 ∨ lt t1 t0 ∨ t0 = t1
      | Sum.inl a0, Sum.inl a1 =>
          (wa.total a0 a1).elim
            (fun lt => Or.inl lt)
            (fun gtOrEq => gtOrEq.elim
              (fun gt => Or.inr (Or.inl gt))
              (fun eq => Or.inr (Or.inr (eq ▸ rfl))))
      | Sum.inl _0, Sum.inr _1 => Or.inl trivial
      | Sum.inr _0, Sum.inl _1 => Or.inr (Or.inl trivial)
      | Sum.inr b0, Sum.inr b1 =>
          -- How could I do this without the code duplication?
          -- TODO perhaps it's easy, and I'm just tired.
          (wb.total b0 b1).elim
            (fun lt => Or.inl lt)
            (fun gtOrEq => gtOrEq.elim
              (fun gt => Or.inr (Or.inl gt))
              (fun eq => Or.inr (Or.inr (eq ▸ rfl))))
    
    let wfLeft.fix: ∀ (a : wa.T), Acc lt (Sum.inl a) :=
        WellFounded.fix wa.wf fun
          (t: wa.T)
          (rc: (tt: wa.T) → wa.lt tt t → Acc lt (Sum.inl tt))
        =>
          Acc.intro (Sum.inl t) fun tt ltTtT =>
            match tt with
              | Sum.inl tta => rc tta ltTtT
              -- So cool Lean knows the other option is impossible! (But how?)
    
    let wfLeft (t: Sum wa.T wb.T) {a: wa.T} (tIsLeft: t = Sum.inl a):
      Acc lt t
    :=
      tIsLeft ▸ wfLeft.fix a
    
    let wfRight (t: Sum wa.T wb.T) {b: wb.T} (tIsRight: t = Sum.inr b):
      Acc lt t
    :=
      let fix: ∀ (b : wb.T), Acc lt (Sum.inr b) :=
        WellFounded.fix wb.wf fun
          (t: wb.T)
          (rc: (tt: wb.T) → wb.lt tt t → Acc lt (Sum.inr tt))
        =>
          Acc.intro (Sum.inr t) fun tt ltTtT =>
            match tt with
              | Sum.inl tta => wfLeft.fix tta
              | Sum.inr ttb => rc ttb ltTtT
      
      tIsRight ▸ fix b
    
    let wf (t: Sum wa.T wb.T): Acc lt t :=
      Acc.intro t (
        fun tt ltTt =>
          match hh: tt, h: t with
            | Sum.inl _, _ => hh ▸ wfLeft tt hh
            | Sum.inr _, Sum.inl _ => False.elim ltTt
            | Sum.inr _, Sum.inr _ => hh ▸ wfRight tt hh
      )
    
    {
      T := Sum wa.T wb.T
      lt := lt
      total := total
      wf := ⟨wf⟩
    }
  
  def plus.morphism.left (wa wb: WellOrder): Morphism wa (wa.plus wb) :=
    let wab := wa.plus wb
    let fMono (a0 a1: wa.T) (lt: a0 < a1): wab.lt (Sum.inl a0) (Sum.inl a1) :=
      lt
    {
      f := fun a => Sum.inl a
      ordPres := fun a0 a1 => Iff.intro (fMono a0 a1)
        fun lt => (monoInvMono Sum.inl a0 a1
          (wellFoundedT wa) (wellFoundedT wab) lt wa.total fMono)
    }
  
  def plus.morphism.right (wa wb: WellOrder): Morphism wb (wa.plus wb) :=
    let wab := wa.plus wb
    let fMono (b0 b1: wb.T) (lt: b0 < b1): wab.lt (Sum.inr b0) (Sum.inr b1) :=
      lt
    {
      f := fun b => Sum.inr b
      ordPres := fun b0 b1 => Iff.intro (fMono b0 b1)
        fun lt => (monoInvMono Sum.inr b0 b1
          (wellFoundedT wb) (wellFoundedT wab) lt wb.total fMono)
    }
  
  noncomputable def Morphism.either (wa wb: WellOrder):
    Sum (Morphism wa wb) (Morphism wb wa)
  :=
    let wab := wa.plus wb
    let mac: Morphism wa wab := plus.morphism.left wa wb
    let mbc: Morphism wb wab := plus.morphism.right wa wb
    
    let iniAC := Morphism.initial mac
    let iniBC := Morphism.initial mbc
    
    if hAB: wab.succ.lt (ordIn iniAC.val) (ordIn iniBC.val) then
      Sum.inl (choiceEx (ordIn.metaLtIfLt iniAC iniBC hAB).right)
    else if hBA: wab.succ.lt (ordIn iniBC.val) (ordIn iniAC.val) then
      Sum.inr (choiceEx (ordIn.metaLtIfLt iniBC iniAC hBA).right)
    else
      let eq: ordIn iniAC.val = ordIn iniBC.val :=
        (wab.succ.total (ordIn iniAC.val) (ordIn iniBC.val)).elim
          (fun lt => False.elim (hAB lt))
          (fun gtOrEq => gtOrEq.elim (fun gt => False.elim (hBA gt)) id)
      Sum.inl (ordIn.eqIso iniAC iniBC eq).morphismF
  
  def metaLt.total (wa wb: WellOrder):
    wa < wb ∨ wb < wa ∨ wa ≈ wb
  :=
    let eitherMorphism := Morphism.either wa wb
    
    match eitherMorphism with
      | Sum.inl mab => (Morphism.le mab).elim
          (fun lt => Or.inl lt) (fun iso => Or.inr (Or.inr iso))
      | Sum.inr mba => (Morphism.le mba).elim
          (fun lt => Or.inr (Or.inl lt)) (fun iso => Or.inr (Or.inr iso.symm))
  
  
  def isIso.metaLt {wa wb wc: WellOrder}:
    wa ≈ wb → wb < wc → wa < wc
  :=
    fun isIsoAB bc =>
      let mab := (choiceEx isIsoAB).val.morphismF.val
      let mbc := (choiceEx bc.right).val
      
      And.intro
        (fun isIsoAC => bc.left (isIsoAB.symm.trans isIsoAC))
        ⟨mab.trans mbc, trivial⟩
  
  def metaLt.isIso {wa wb wc: WellOrder}:
    wa < wb → wb ≈ wc → wa < wc
  :=
    fun ab isIsoBC =>
      let mab := (choiceEx ab.right).val
      let mbc := (choiceEx isIsoBC).val.morphismF.val
      
      And.intro
        (fun isIsoAC => ab.left (isIsoAC.trans isIsoBC.symm))
        ⟨mab.trans mbc, trivial⟩
    
  
  def metaLt.trans {wa wb wc: WellOrder}:
    wa < wb → wb < wc → wa < wc
  :=
    fun ab bc =>
      And.intro
        (fun isIsoAC =>
          ab.left
            ⟨
              Isomorphism.fromMorphisms
                (choiceEx ab.right).val
                (Morphism.trans
                  (choiceEx bc.right).val
                  (choiceEx isIsoAC).val.morphismG.val),
              trivial
            ⟩)
        ⟨Morphism.trans
          (choiceEx ab.right).val
          (choiceEx bc.right).val,
        trivial⟩
  
  def ltle.trans {a b c: WellOrder}:
    a < b → b ≤ c → a < c
  := 
    fun ab bc =>
      bc.elim
        (fun bc => metaLt.trans ab bc)
        (fun isIsoBC => metaLt.isIso ab isIsoBC)
  
  def lelt.trans {a b c: WellOrder}:
    a ≤ b → b < c → a < c
  := 
    fun ab bc =>
      ab.elim
        (fun ab => metaLt.trans ab bc)
        (fun isIsoAB => isIso.metaLt isIsoAB bc)
  
end WellOrder


instance wellOrderSetoid: Setoid WellOrder where
  r (a b: WellOrder) := a ≈ b
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

@[reducible] def Ordinal := Quotient wellOrderSetoid

namespace Ordinal
  def mk (w: WellOrder): Ordinal := Quotient.mk' w
  
  def zero: Ordinal := mk WellOrder.zero
  
  def isZero (n: Ordinal): Prop := n = Ordinal.zero
  
  def succ.mid (w: WellOrder) := Ordinal.mk w.succ
  
  def succ: Ordinal → Ordinal := Quotient.lift succ.mid
    fun (wa wb: WellOrder) (asimb: wa ≈ wb) =>
      let iso: WellOrder.Isomorphism wa wb := choiceEx asimb
      
      Quotient.sound ⟨WellOrder.succ.iso wa wb iso, trivial⟩
  
  def succ.inj
    {na nb: Ordinal}
    (eq: succ na = succ nb)
  :
    na = nb
  :=
    let naRep := getRep na
    let nbRep := getRep nb
    
    let naEq: mk naRep = na := naRep.property
    let nbEq: mk nbRep = nb := nbRep.property
    
    let succEqOrd: succ (mk naRep) = succ (mk nbRep) :=
      by rw [naEq, nbEq]; exact eq
    
    let succEqMid: succ.mid naRep = succ.mid nbRep := succEqOrd
    
    let succEqW: mk naRep.val.succ = mk nbRep.val.succ := succEqMid
    
    let isoExSuccW: naRep.val.succ ≈ nbRep.val.succ :=
      Quotient.exact succEqW
    
    let isoSuccW: WellOrder.Isomorphism naRep.val.succ nbRep.val.succ :=
      choiceEx isoExSuccW
    
    let isoW := WellOrder.succ.isoInv naRep.val nbRep.val isoSuccW
    
    naRep.property ▸ nbRep.property ▸ (Quotient.sound ⟨isoW, trivial⟩)
  
  
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
          let waPred := WellOrder.pred.iso asimb.symm ⟨b, wbp⟩
          let nope: none = some waPred.val := wap ▸ waPred.property.left
          Option.noConfusion nope
      | some a, none =>
          let wbPred := WellOrder.pred.iso asimb ⟨a, wap⟩
          let nope: none = some wbPred.val := wbp ▸ wbPred.property.left
          Option.noConfusion nope
      | some a, some b =>
          let wbPred := WellOrder.pred.iso asimb ⟨a, wap⟩
          
          let isoAB: a ≈ b :=
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
  
  def isLimit (n: Ordinal): Prop := n.pred = none
  
  def isInfLimit (n: Ordinal): Prop := n.isLimit ∧ ¬n.isZero
  
  def hasPred.isNotLimit (n nPred: Ordinal) (eq: n.pred = nPred): ¬ n.isLimit
  :=
    fun isLimit => Option.noConfusion (isLimit ▸ eq)
  
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
              
              let isoPred: nRepPred ≈ predRep.val := Quotient.exact mkEq
              
              let eqProp: nRep.val.pred = nRep.val.predProp :=
                WellOrder.pred.eqPredProp nRep
              
              let hh: nRep.val.predProp = some nRepPred := eqProp ▸ h
              
              let isIsoNRepPred: nRepPred.succ ≈ nRep :=
                nRep.val.predProp.property nRepPred (eqProp ▸ hh ▸ eqProp)
              
              let isIsoPredRep:
                predRep.val.succ ≈ nRepPred.succ
              := ⟨
                WellOrder.succ.iso predRep.val nRepPred (choiceEx isoPred).val.symm,
                trivial
              ⟩
              
              let isIso: predRep.val.succ ≈ nRep :=
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
  
  noncomputable def nLimit.pred (n: Ordinal) (isSucc: ¬ isLimit n):
    { pred: Ordinal // pred.succ = n }
  :=
    match hh: n.predProp with
      | ⟨none, _⟩ =>
          let predPropNone: n.predProp.val = none := congr rfl hh
          False.elim (isSucc ((pred.eqPredProp n).trans predPropNone))
      | ⟨some nn, succN⟩ => ⟨nn, succN nn rfl⟩
  
  def pred.succ.eq {n nPred: Ordinal} (eq: n.pred = some nPred):
    nPred.succ = n
  :=
    let eq0: n.predProp = n.pred := (pred.eqPredProp n).symm
    (predProp n).property nPred (eq0.trans eq)
  
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
          wx0 < wy0 → wx1 < wy1
        :=
          fun lt0 =>
            let xyNIso0: ¬ wx0 ≈ wy0 := lt0.left
            let xyNIso1: ¬ wx1 ≈ wy1 :=
              fun iso1 => xyNIso0 ((simX.trans iso1).trans simY.symm)
                
            let isoX: WellOrder.Isomorphism wx0 wx1 := choiceEx simX
            let isoY: WellOrder.Isomorphism wy0 wy1 := choiceEx simY
            
            let mxy0: WellOrder.Morphism wx0 wy0 := choiceEx lt0.right
            let mxy1: WellOrder.Morphism wx1 wy1 :=
              (isoX.morphismG.val.trans mxy0).trans isoY.morphismF
            
            And.intro xyNIso1 ⟨mxy1, trivial⟩
        
        let iff: wa0 < wb0 ↔ wa1 < wb1 :=
          Iff.intro
            (mp wa0 wb0 wa1 wb1 simA simB)
            (mp wa1 wb1 wa0 wb0 simA.symm simB.symm)
        
        propext iff
  
  def succ.hasPred (n: Ordinal): n.succ.pred ≠ none :=
    let nRep := getRep n
    let nSuccRep := getRep n.succ
    
    let eqOrdLeft: (mk nRep).succ = n.succ := congr rfl nRep.property
    let eqOrd: (mk nRep).succ = mk nSuccRep :=
      eqOrdLeft.trans nSuccRep.property.symm
    
    let iso: nRep.val.succ ≈ nSuccRep.val := Quotient.exact eqOrd
    
    let nRepSuccHasPred: nRep.val.succ.pred ≠ none :=
      WellOrder.succ.hasPred nRep.val
    
    let nRepSuccPred: { p // nRep.val.succ.pred = some p } :=
      match h: nRep.val.succ.pred with
        | none => False.elim (nRepSuccHasPred h)
        | some p => ⟨p, rfl⟩
    
    let nSuccRepHasPred: nSuccRep.val.pred ≠ none :=
      let eqSome := (WellOrder.pred.iso iso nRepSuccPred).property.left
      fun eqNone =>
        Option.noConfusion
          (eqNone.symm.trans eqSome)
    
    fun eqNone =>
      let nSuccRepEq: (mk nSuccRep) = n.succ := nSuccRep.property
      let nSuccRepMkHasNoPred: (mk nSuccRep).pred = none :=
        nSuccRepEq.symm ▸ eqNone
      let nSuccRepPredEq: (mk nSuccRep).pred = Ordinal.pred.mid nSuccRep.val :=
        rfl
      let nSuccRepMidHasNoPred: Ordinal.pred.mid nSuccRep.val = none :=
        nSuccRepPredEq ▸ nSuccRepMkHasNoPred
      let nSuccRepHasNoPred: nSuccRep.val.pred = none :=
        match h: nSuccRep.val.pred with
          | none => rfl
          | some p =>
              let nSuccRepMidHasPred:
                Ordinal.pred.mid nSuccRep.val = some (Ordinal.mk p)
              :=
                by unfold Ordinal.pred.mid; rw [h]
              Option.noConfusion
                (nSuccRepMidHasNoPred.symm.trans nSuccRepMidHasPred)
      nSuccRepHasPred nSuccRepHasNoPred
  
  def succ.pred.eq {nSucc n: Ordinal} (eq: n.succ = nSucc):
    nSucc.pred = some n
  :=
    match h: nSucc.pred with
      | none => False.elim (succ.hasPred n (eq ▸ h))
      | some nsp =>
          let nspSuccEq: succ nsp = succ n := (pred.succ.eq h).trans eq.symm
          let nspEq: nsp = n := succ.inj nspSuccEq
          nspEq ▸ rfl
  
  def le (a b: Ordinal): Prop := lt a b ∨ a = b
  def le.toLt {a b: Ordinal} (leAB: le a b) (neq: a ≠ b): lt a b :=
    leAB.elim id (fun eq => False.elim (neq eq))
  def lt.toLe {a b: Ordinal} (ltAB: lt a b): le a b :=
    Or.inl ltAB
  
  instance: LT Ordinal where
    lt := Ordinal.lt
  
  instance: LE Ordinal where
    le := Ordinal.le
  
  def le.fromWO {wa wb: WellOrder} (le: wa ≤ wb):
    Ordinal.mk wa ≤ Ordinal.mk wb
  :=
    le.elim
      (fun lt => Or.inl lt)
      (fun iso => Or.inr (Quotient.sound iso))
  
  def wfLt (w: WellOrder): Acc lt (Ordinal.mk w) :=
    Acc.intro (Ordinal.mk w) fun wwOrd wwLtW =>
      let ww := choiceEx (Quotient.exists_rep wwOrd)
      
      let eq: wwOrd = Ordinal.mk ww := ww.property.symm
      
      let lt: Ordinal.mk ww < Ordinal.mk w := eq ▸ wwLtW
      
      have: ww < w := lt
      ww.property ▸ wfLt ww
    termination_by wfLt w => w
  
  def wf (o: Ordinal): Acc lt o := Quotient.ind wfLt o
  
  
  def succ.gt (n: Ordinal): n < n.succ :=
    let nRep := getRep n
    let nSuccRep := getRep n.succ
    
    let eq0: Ordinal.succ (mk nRep.val) = succ.mid nRep := rfl
    let eq1: Ordinal.succ (mk nRep.val) = Ordinal.mk nRep.val.succ := eq0
    let eq2: Ordinal.succ (mk nRep.val) = Ordinal.succ n := congr rfl nRep.property
    let eq3: Ordinal.succ (mk nRep.val) = mk nSuccRep :=
      eq2.trans nSuccRep.property.symm
    
    let eq: mk nSuccRep = mk nRep.val.succ := eq3.symm.trans eq1
    
    let isoEx: nSuccRep.val ≈ nRep.val.succ := Quotient.exact eq
    
    let lt0: nRep.val < nSuccRep.val :=
      WellOrder.succIsoGt nRep.val nSuccRep (choiceEx isoEx).val
    
    let lt1: mk nRep.val < mk nSuccRep.val := lt0
    
    let lt2: n < mk nSuccRep.val :=
      by conv =>
        lhs
        rw [nRep.property.symm]; exact lt1
    
    nSuccRep.property ▸ lt2
  
  def succ.ge (n: Ordinal): n ≤ n.succ := Or.inl (succ.gt n)
  
  def pred.lt {n nPred: Ordinal} (eq: n.pred = some nPred):
    lt nPred n
  :=
    let ltSucc: nPred < nPred.succ := succ.gt nPred
    (pred.succ.eq eq) ▸ ltSucc
  
  def nLimit.pred.lt (n: Ordinal) (isSucc: ¬ isLimit n):
    nLimit.pred n isSucc < n
  :=
    let p := nLimit.pred n isSucc
    
    let ltP: p.val < p.val.succ := succ.gt p
    let eq: p.val.succ = n := p.property
    
    let pVal := p.val -- Why tf is this necessary, Lean?
    show pVal < n from eq ▸ ltP
  
  def total.mid (a b: WellOrder):
    Ordinal.mk a < Ordinal.mk b ∨
    Ordinal.mk b < Ordinal.mk a ∨
    Ordinal.mk a = Ordinal.mk b
  :=
    (WellOrder.metaLt.total a b).elim
      (fun lt => Or.inl lt)
      (fun gtOrEq =>
        gtOrEq.elim
          (fun gt => Or.inr (Or.inl gt))
          (fun iso => Or.inr (Or.inr (Quotient.sound iso))))
  
  def total: (a b: Ordinal) → a < b ∨ b < a ∨ a = b :=
    Quotient.ind₂ total.mid
  
  def ofNat (n: Nat): Ordinal :=
    if n = 0 then Ordinal.zero else (Ordinal.ofNat (n - 1)).succ
  
  instance wellFounded: WellFoundedRelation Ordinal where
    rel := Ordinal.lt
    wf := ⟨Ordinal.wf⟩
  
  def lt.trans {a b c: Ordinal}:
    a < b → b < c → a < c
  := 
    wfRel.total.trans total
  
  def ltle.trans {a b c: Ordinal}:
    a < b → b ≤ c → a < c
  := 
    fun ab bc =>
      bc.elim
        (fun bc => wfRel.total.trans total ab bc)
        (fun eq => eq ▸ ab)
  
  def lelt.trans {a b c: Ordinal}:
    a ≤ b → b < c → a < c
  := 
    fun ab bc =>
      ab.elim
        (fun ab => wfRel.total.trans total ab bc)
        (fun eq => eq ▸ bc)
  
  def le.trans {a b c: Ordinal}:
    a ≤ b → b ≤ c → a ≤ c
  := 
    fun ab bc =>
      ab.elim
        (fun ab =>
          bc.elim
            (fun bc => Or.inl (lt.trans ab bc))
            (fun eq => Or.inl (eq ▸ ab)))
        (fun eq => eq ▸ bc)
  
  def le.refl (n: Ordinal): n ≤ n := Or.inr rfl
  
  def le.antisymm {a b: Ordinal}: a ≤ b → b ≤ a → a = b
    | Or.inr rfl, _ => rfl
    | _, Or.inr rfl => rfl
    | Or.inl ab, Or.inl ba => wfRel.antisymm ab ba
  
  instance partialOrder: PartialOrder Ordinal where
    le := Ordinal.le
    
    refl := le.refl
    antisymm := fun _ _ => le.antisymm
    trans := fun _ _ _ => le.trans
    
    ltToLeNeq := id
    leNeqToLt := id
  
  def ltSucc.le.mid (wa wb: WellOrder):
    (abs: wa < wb.succ) → mk wa ≤ mk wb
  :=
    fun abs =>
      (WellOrder.ltSucc.le abs).elim
        (fun lt => Or.inl lt)
        (fun eq => Or.inr (Quotient.sound eq))
  
  def ltSucc.le {na nb: Ordinal} (abs: na < nb.succ): na ≤ nb :=
    Quotient.ind₂ ltSucc.le.mid na nb abs
  
  def lt.noMiddle {p: Prop} {a b: Ordinal} (ab: a < b) (bas: b < a.succ): p :=
    (ltSucc.le bas).elim
      (fun ba => wfRel.antisymm.any ab ba)
      (fun eq => False.elim (wfRel.irefl a (eq ▸ ab)))
  
  def succ.le {a b: Ordinal} (asb: a < b): a.succ ≤ b :=
    (a.succ.total b).elim
      (fun lt => Or.inl lt)
      (fun gtOrEq =>
        gtOrEq.elim
          (fun gt => lt.noMiddle asb gt)
          (fun eq => Or.inr (eq ▸ rfl)))
  
  def le.ltSucc {n nn: Ordinal} (le: nn ≤ n): nn < n.succ :=
    Ordinal.lelt.trans le (succ.gt n)
  
  instance (n: Nat): OfNat Ordinal n where
    ofNat := Ordinal.ofNat n
  
  def zero.least (n: Ordinal): 0 ≤ n :=
    if h: zero = n then
      Or.inr h
    else
      let nRep := getRep n
      let mZeroN := WellOrder.zero.morphism nRep
      let nIso: ¬ WellOrder.zero ≈ nRep :=
        fun isIso =>
          let eq: zero = n := nRep.property ▸ Quotient.sound isIso
          h eq
      let lt: WellOrder.zero < nRep := And.intro nIso ⟨mZeroN, trivial⟩
      Or.inl (nRep.property ▸ lt)
  
  def zero.lt (n: Ordinal) (nNeqZero: n ≠ zero): 0 < n :=
    (zero.least n).elim id (fun eq => False.elim (nNeqZero eq.symm))
  
  def zero.nGreater (n: Ordinal): ¬ n < zero :=
    fun zeroLt =>
      (zero.least n).elim
        (fun lt => wfRel.antisymm.false zeroLt lt)
        (fun eq => wfRel.irefl n (eq ▸ zeroLt))
  
  def lt.notZero {a b: Ordinal} (ab: a < b): ¬b.isZero :=
    fun eq => zero.nGreater a (eq.symm ▸ ab)
  
  def zero.isLimit: zero.isLimit :=
    match h: zero.pred with
    | none => h
    | some zeroPred =>
        let predLt: zeroPred < zero := pred.lt h
        False.elim (zero.nGreater _ predLt)
  
  def succ.ltLimit
    {n nLim: Ordinal}
    (nLt: n < nLim)
    (isLimit: nLim.isLimit)
  :
    n.succ < nLim
  :=
    (total n.succ nLim).elim id (fun gtOrEq =>
      gtOrEq.elim
        (fun gt => lt.noMiddle nLt gt)
        (fun eq =>
          let hasPred: nLim.pred ≠ none := eq ▸ succ.hasPred n
          False.elim (hasPred isLimit)))
  
  def succ.notLimit {n: Ordinal}: ¬n.succ.isLimit :=
    fun isSuccLim =>
      let nSuccPred.eq: n.succ.pred = n := succ.pred.eq rfl
      Option.noConfusion (isSuccLim.symm.trans nSuccPred.eq)
  
  
  def isLeast (s: Set Ordinal): Set Ordinal :=
    fun n: Ordinal => n ∈ s ∧ ∀ nn: Ordinal, nn ∈ s → n ≤ nn
  def Least (s: Set Ordinal) := { n: Ordinal // isLeast s n }
  
  
  def isUpperBound (s: Set Ordinal): Set Ordinal :=
    fun n: Ordinal => ∀ nn: { nn: Ordinal // s nn }, nn ≤ n
  def UpperBound (s: Set Ordinal) := { n: Ordinal // isUpperBound s n }
  
  
  def isSupremum (s: Set Ordinal) := isLeast (isUpperBound s)
  def Supremum (s: Set Ordinal) := Least (isUpperBound s)
  
  def ltSet (n: Ordinal): Set Ordinal := fun nn => nn < n
  
  def never.lelt {p: Prop} {a b: Ordinal} (abLe: a ≤ b) (baLt: b < a): p :=
    abLe.elim
      (fun abLt =>
        let eq := wfRel.antisymm abLt baLt
        False.elim (wfRel.irefl a (eq ▸ baLt)))
      (fun eq =>
        False.elim (wfRel.irefl a (eq ▸ baLt)))
  
  def never.ltle {p: Prop} {a b: Ordinal} (abLt: a < b) (baLe: b ≤ a): p :=
    never.lelt baLe abLt
  
  def lele.eq {a b: Ordinal} (abLe: a ≤ b) (baLe: b ≤ a): a = b :=
    abLe.elim
      (fun abLt => never.lelt baLe abLt)
      (fun eq => eq)
  
  def notLe.gt {a b: Ordinal} (nle: ¬ a ≤ b): b < a :=
    (b.total a).elim id
      (fun ltOrEq => False.elim (ltOrEq.elim
        (fun lt => (nle lt.toLe))
        (fun eq => (eq ▸ nle) (Or.inr rfl))))
  
  def notLt.ge {a b: Ordinal} (nlt: ¬ a < b): b ≤ a :=
    (b.total a).elim (fun ba => Or.inl ba)
      (fun ltOrEq => (ltOrEq.elim
        (fun lt => False.elim (nlt lt))
        (fun eq => (eq ▸ (Or.inr rfl)))))
  
  def lt.leSucc {na nb: Ordinal} (ab: na < nb): na.succ ≤ nb :=
    (na.succ.total nb).elim
      (fun lt => lt.toLe)
      (fun gtOrEq => gtOrEq.elim
        (fun gt =>
          let le := ltSucc.le gt
          never.ltle ab le)
        (fun eq => eq ▸ (le.refl na.succ)))
  
  def zero.notSucc (n: Ordinal): n.succ ≠ Ordinal.zero :=
    fun eq =>
      let succLeN: n.succ ≤ n := eq ▸ zero.least n
      let succGeN: n < n.succ := succ.gt n
      
      never.lelt succLeN succGeN
  
  def limit.isSup (n: Ordinal) (isLimit: n.isLimit):
    isSupremum n.ltSet n
  :=
    And.intro
      (fun nn => Or.inl nn.property)
      (fun nOther nOtherUB =>
        (n.total nOther).elim
          (fun lt => Or.inl lt)
          (fun gtOrEq =>
            gtOrEq.elim
              (fun gt =>
                let nOtherSuccLtN: nOther.succ < n := succ.ltLimit gt isLimit
                let nOtherSuccLeNOther: nOther.succ ≤ nOther :=
                  nOtherUB ⟨nOther.succ, nOtherSuccLtN⟩
                let nOtherSuccGtNOther: nOther < nOther.succ := succ.gt nOther
                never.lelt nOtherSuccLeNOther nOtherSuccGtNOther)
              (fun eq => Or.inr eq)))
end Ordinal

instance: Coe Ordinal (Type 1) where
  coe n := { nn: Ordinal // nn < n }

namespace Ordinal
  def omega: Ordinal := Ordinal.mk {
    T := Nat
    
    lt := Nat.lt
    total := Nat.isTotal
    
    wf := Nat.lt_wfRel.wf
  }
  
  def zero.ltOmega: zero < omega :=
    And.intro
      (fun isIso => ((choiceEx isIso).val.g 0).rec)
      ⟨{ f := fun _ => 4, ordPres := fun a _ => a.rec }, trivial⟩
  
  inductive EqOrAB (n a b: Ordinal) where
    | eqA (gea: a = n)
    | eqB (geb: b = n)
  
  structure Max (a b: Ordinal) where
    n: Ordinal
    geA: a ≤ n
    geB: b ≤ n
    eqAB: EqOrAB n a b
  
  noncomputable def max (a b: Ordinal): Max a b :=
    (a.total b).Elim
      (fun lt => ⟨b, Or.inl lt, Or.inr rfl, EqOrAB.eqB rfl⟩)
      (fun gtOrEq => gtOrEq.Elim
        (fun gt => ⟨a, Or.inr rfl, Or.inl gt, EqOrAB.eqA rfl⟩)
        (fun eq => ⟨b, Or.inr eq, Or.inr rfl, EqOrAB.eqB rfl⟩))
  
  def Max.holds
    (max: Max a b)
    {p: Ordinal → Prop}
    (aHolds: p a)
    (bHolds: p b)
  :
    p max.n
  :=
    match max.eqAB with
      | EqOrAB.eqA eqA => eqA ▸ aHolds
      | EqOrAB.eqB eqB => eqB ▸ bHolds
  
  def isFinite (n: Ordinal): Prop :=
    ∀ (limOrd: Ordinal)
      (_isLim: limOrd.isLimit)
      (_notZero: limOrd ≠ Ordinal.zero)
    ,
      n < limOrd
  
  def isFinite.zero: zero.isFinite :=
    fun lim _ nz =>
      let leLim := zero.least lim
      leLim.toLt nz.symm
  
  def isFinite.succ {n: Ordinal} (isFin: n.isFinite): n.succ.isFinite :=
    fun limOrd isLim notZero =>
      Ordinal.succ.ltLimit (isFin limOrd isLim notZero) isLim
  
  def isFinite.ltFinite {a b: Ordinal}
    (ab: a < b)
    (bFin: b.isFinite)
  :
    a.isFinite
  :=
    fun n nLim nNotZero => Ordinal.lt.trans ab (bFin n nLim nNotZero)
  
  def isFinite.leFinite {a b: Ordinal}
    (ab: a ≤ b)
    (bFin: b.isFinite)
  :
    a.isFinite
  :=
    ab.elim (fun ab => isFinite.ltFinite ab bFin) (fun eq => eq ▸ bFin)
  
  def notFinite.gtNotFinite {a b: Ordinal}
    (ab: a < b)
    (aNotFin: ¬ a.isFinite)
  :
    ¬ b.isFinite
  :=
    fun bFin => aNotFin (isFinite.ltFinite ab bFin)
  
  def isFinite.zeroOrNotLimit {n: Ordinal} (isFin: n.isFinite):
    n = Ordinal.zero ∨ ¬n.isLimit
  :=
    if h: n = Ordinal.zero then
      Or.inl h
    else
      Or.inr fun isLim => wfRel.irefl n (isFin n isLim h)
  
  def isFinite.pos.notLimit {n: Ordinal} (isFin: n.isFinite) (notZero: n ≠ 0):
    ¬n.isLimit
  :=
    (isFinite.zeroOrNotLimit isFin).elim
      (fun isZero => False.elim (notZero isZero)) id
  
  def isFinite.pred {n: Ordinal} (isFin: n.isFinite) (notZero: n ≠ 0):
    (Ordinal.nLimit.pred n (isFinite.pos.notLimit isFin notZero)).val.isFinite
  :=
    let notLim := isFinite.pos.notLimit isFin notZero
    let nPred.lt := Ordinal.nLimit.pred.lt n notLim
    
    fun lim isLim notZero =>
      Ordinal.lt.trans nPred.lt (isFin lim isLim notZero)
  
  def isFinite.ltInfLim {n lim: Ordinal}
    (isFin: n.isFinite)
    (limInfLim: lim.isInfLimit)
  :
    n < lim
  :=
    isFin lim limInfLim.left limInfLim.right
  
  noncomputable def notFinite.geInfLim {n: Ordinal} (notFin: ¬n.isFinite):
    { lim: Ordinal // lim.isInfLimit ∧ lim ≤ n }
  :=
    let exLim:
      ∃ (limOrd: Ordinal)
        (_isLim: limOrd.isLimit)
        (_notZero: limOrd ≠ Ordinal.zero)
      ,
        limOrd ≤ n
      := -- Would be cool to have a function that does this
         -- to an arbitrary proposition.
        notAll.ex notFin
          (fun _ p => notAll.ex p
            (fun _ p => notAll.ex p
              (fun _ p => notLt.ge p)))
    
    let ⟨lim, prop⟩ := choiceEx exLim
    
    ⟨
      lim,
      prop.elim
        (fun isLim exNotZero =>
          exNotZero.elim (fun notZero leN =>
            And.intro (And.intro isLim notZero) leN))
    ⟩
  
  def isFinite.ltNotFin {nFin nNotFin: Ordinal}
    (isFin: nFin.isFinite)
    (isNotFin: ¬nNotFin.isFinite)
  :
    nFin < nNotFin
  :=
    let ⟨lim, isLim, limLe⟩ := notFinite.geInfLim isNotFin
    ltle.trans (isFin lim isLim.left isLim.right) limLe
  
  def notFinite.predNotFinite {n nPred: Ordinal}
    (nNotFin: ¬ n.isFinite)
    (nPredEq: nPred.succ = n)
  :
    ¬nPred.isFinite
  :=
    fun nPredFin => nNotFin (nPredEq ▸ isFinite.succ nPredFin)
  
  def notFinite.predGtFinite {fin n nPred: Ordinal}
    (finFin: fin.isFinite)
    (nNotFin: ¬ n.isFinite)
    (nPredEq: nPred.succ = n)
  :
    fin < nPred
  :=
    let nPred.notFin := notFinite.predNotFinite nNotFin nPredEq
    
    isFinite.ltNotFin finFin nPred.notFin
  
  def zero.nex (p: ↑zero → Prop): ¬∃ n: ↑zero, p n :=
    fun ex => ex.elim fun ltZero =>
      never.lelt (zero.least ltZero) ltZero.property
  
end Ordinal
