/-
  Defines ordinals. Takes heavy inspiration from mathlib
  (I guess -- I wrote this comment before defining them).
  Update: so I guess I freestyle a lot.
  
  Don't look inside. It's embarrassing. (And also supposed
  to be write-once, forget and don't ever read again.)
-/

import Set

open Classical


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

-- TODO do I need you?
def Least (s: Set T) (lt: T → T → Prop): Type :=
  { t: T // t ∈ s ∧ ∀ tt: T, tt ∈ s → lt t tt ∨ t = tt }


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



structure WellOrder where
  T: Type
  lt: T → T → Prop
  
  total: ∀ a b: T, lt a b ∨ lt b a ∨ a = b
  wf: WellFounded lt

instance wfWT (w: WellOrder): WellFoundedRelation w.T where
  rel := w.lt
  wf := w.wf

instance (w: WellOrder): LT w.T where
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
          fun cLtAOrCEqA =>
            let cLtB: c < b := cLtAOrCEqA.elim
              (fun cLtA =>rc b bLtC c a cLtA aLtB)
              (fun aEqC => aEqC ▸ aLtB)
            let bEqC: b = c := wfRel.antisymm bLtC cLtB
            let bLtB: b < b := bEqC ▸ cLtB
            let bNLtB: ¬ b < b := wfRel.irefl b
            False.elim (bNLtB bLtB)
        )
  ) c a b
  
  
  structure Morphism (wa wb: WellOrder) where
    f: wa.T → wb.T
    
    ordPres: ∀ a b: wa.T, a < b ↔ f a < f b
  
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
    ordPres := fun a b =>
      match a, b with
        | none, _ => Iff.intro False.elim False.elim
        | some _, none => Iff.intro id id
        | some a, some b => mab.ordPres a b
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
          -- This is a proof that the inverse of a monotonic function
          -- is monotonic. This comment is here so that you can Ctrl+Find
          -- "inverse" if you ever need it anywhere else.
          (fun ltFA => (wa.total a0 a1).elim id
            (fun gtOrEq =>
              let eq: f a0 = f a1 := gtOrEq.elim
                (fun gt =>
                  let gtFA := (initial.f.monotonic m a1 a0) gt
                  wfRel.antisymm ltFA gtFA)
                fun eq => congr rfl eq
              let irefl: f a0 < f a0 := eq ▸ ltFA
              False.elim (wfRel.irefl (f a0) irefl)))
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
    let rc (aa: wa.T) (lt: aa < a) :=
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
        (fun gt => sorry) id)
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
      | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl
  
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
  
  /- TODO do I need you?
  def succ.nIso (w: WellOrder): ¬ ∃ _: Isomorphism w w.succ, True :=
    fun isoEx =>
      let iso: Isomorphism w w.succ := choiceEx isoEx
      
      let succGst: { s: w.succ.T // isGreatest w.succ s } := ⟨
        none,
        fun s0 =>
          match h: s0 with
            | none => Or.inl rfl
            | some a => Or.inr trivial
      ⟩
      
      let wGst: { s: w.T // isGreatest w s } :=
        greatestIso w.succ w iso.symm succGst
      
      let succGstNope: w.succ.T := some wGst
    
    sorry-/
  
  
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
  
  noncomputable def pred (w: WellOrder): Option WellOrder :=
    if ∃ gst: w.T, isGreatest w gst then
      some (predNoOpt w)
    else
      none
  
  -- What's a normal way of proving X from `(if X then A else B) = A`?
  -- TODO ask on proofassistants.
  def ifPred.hasGreatest
    (w: WellOrder)
    (pred: { pred: WellOrder // w.pred = some pred })
  :
    ∃ gst: w.T, isGreatest w gst
  :=
    if h: ∃ gst: w.T, isGreatest w gst then
      h
    else
      let nope: w.pred = none := by
        conv =>
          lhs
          unfold WellOrder.pred
          simp [h]
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
        match nope: wb.pred with
          | none =>
              let eq: wb.pred = some wb.predNoOpt := by
                unfold pred
                simp [h]
              Option.noConfusion (nope ▸ eq)
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
  
  
  noncomputable def ordInProp
    (m: Morphism wa wb)
  :
    Minimal
      -- Should have been `some b < bSucc → m.bound b`,
      -- but I don't wanna touch certain code below again.
      (fun bSucc: wb.succ.T => ∀ b: wb.T, bSucc = some b → m.free b)
      wb.succ.lt
  :=
    @minimal wb.succ.T (wfWT wb.succ)
      (fun bSucc => ∀ b: wb.T, bSucc = some b → m.free b)
      ⟨none, fun _ nope => False.elim (Option.noConfusion nope)⟩
  
  noncomputable def ordIn (m: Morphism wa wb): wb.succ.T
  :=
    (ordInProp m).val
  
  def metaLt (wa wb: WellOrder): Prop :=
    ¬ isIsomorphic wa wb ∧ ∃ _: Morphism wa wb, True
  
  def ordIn.eqIsIso
    {wa wb wc: WellOrder}
    (mac: Morphism.Initial wa wc)
    (mbc: Morphism.Initial wb wc)
    (ordInEq: ordIn mac.val = ordIn mbc.val)
  :
    isIsomorphic wa wb
  :=
    sorry
  
  -- TODO do I need you?
  def ordIn.self.eqNone (m: Morphism.Initial w w): ordIn m.val = none :=
    let mOrdEq: (ordInProp m.val).val = ordIn m.val := rfl
    match h: ordInProp m.val with
      | ⟨none, _⟩ => mOrdEq ▸ (congr rfl h)
      | ⟨some b, prop⟩ =>
        let bFree := prop.left b rfl
        let bNFree: m.val.bound b := ⟨
          b,
          (Morphism.self.initial.eqId m) ▸ rfl
        ⟩
        Morphism.freeBound bFree bNFree
  
  def ltOrdIn
    {wa wb wc: WellOrder}
    (mac: Morphism.Initial wa wc)
    (mbc: Morphism.Initial wb wc)
    (mlt: metaLt wa wb)
  :
    ordIn mac.val < ordIn mbc.val
  :=
    let mab: Morphism.Initial wa wb := Morphism.initial (choiceEx mlt.right)
    let mbb: Morphism.Initial wb wb := Morphism.refl wb
    
    let mbbOrdEq: (ordInProp mbb.val).val = ordIn mbb.val := rfl
    
    let mbbOrdNone: ordIn mbb.val = none :=
      match h: ordInProp mbb.val with
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
              (ordInProp mab.val).property.left mabOrd mabOrd.property.symm
            Morphism.freeBound mabOrdFree mabOrdBound
    
    let ordMbcGtMabOrdC:
      wc.succ.lt (some mabOrdC) (ordInProp mbc.val).val
    :=
      match h: (ordInProp mbc.val).val with
        | none => trivial
        | some obc =>
            (wc.total mabOrdC obc).elim id
              fun gtOrEq =>
                let obcFree: mbc.val.free obc := (ordInProp mbc.val).property.left
                  obc h
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
          (fun gt =>
            let notAll: ¬ ∀ c: wc.T,
              some mabOrdC = some c → Morphism.free mac.val c :=
            (ordInProp mac.val).property.right (some mabOrdC) gt
            
            let exTmp: ∃ c: wc.T,
              ¬ (some mabOrdC = some c → Morphism.free mac.val c)
              --some mabOrdC = some c ∧ ¬ Morphism.free mac.val c
            :=
              ⟨mabOrdC, fun p => notAll
                fun _ eqSome => Option.noConfusion eqSome id ▸ (p rfl)⟩
            
            let mabOrdCNFree: ¬ Morphism.free mac.val mabOrdC
            :=
              exTmp.elim fun c p =>
                -- All hail classical logic.
                if hRight: Morphism.free mac.val c then
                  False.elim (p fun _ => hRight)
                else if hLeft: some mabOrdC = some c then
                  Option.noConfusion hLeft fun eq => eq ▸ hRight
                else False.elim (p fun left => False.elim (hLeft left))
            
            Morphism.nFreeBound mabOrdCNFree mabOrdNBoundInMac)
        (fun eq => Or.inr eq)
      
    
    ordMacLtMabOrdC.elim
      (fun lt => WellOrder.lt.trans lt ordMbcGtMabOrdC)
      (fun eq => eq ▸ ordMbcGtMabOrdC)
  
  
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
            (ltOrdIn macIni mbcIni) waLtWb
          
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
            let ordInPropMf := ordInProp mf
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
  
  noncomputable def predOrd (w: WellOrder): Option Ordinal :=
    match w.pred with
      | none => none
      | some a => some (Ordinal.mk a)
  
  noncomputable def pred: Ordinal → Option Ordinal :=
    Quotient.lift
      predOrd
      fun (wa wb: WellOrder) (asimb: wa ≈ wb) =>
        
        match wap: wa.pred, wbp: wb.pred with
          | none, none => by unfold predOrd; simp [wap, wbp]
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
              
              let waEq: predOrd wa = some (Ordinal.mk a) := by
                unfold predOrd
                rw [wap]
              let wbEq: predOrd wb = some (Ordinal.mk b) := by
                unfold predOrd
                rw [wbp]
              let mkSomeAB: some (mk a) = some (mk b) := congr rfl eqMkAB
              waEq ▸ wbEq ▸ mkSomeAB
  
  def isLimit (o: Ordinal): Prop := o.pred = none
end Ordinal

instance: WellFoundedRelation Ordinal where
  rel := sorry
  wf := sorry

