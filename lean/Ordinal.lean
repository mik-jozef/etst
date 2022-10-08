/-
  Defines ordinals. Takes heavy inspiration from mathlib
  (I guess -- I wrote this comment before defining them).
  Update: so I guess I freestyle a lot.
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


-- Should be called minimal, I guess.
def Least (s: Set T) (lt: T → T → Prop): Type :=
  { t: T // t ∈ s ∧ ∀ tt: T, lt tt t → tt ∉ s }

noncomputable def least
  {T: Type}
  [wf: WellFoundedRelation T]
  (s: Set T)
  (nonempty: ↑s)
:
  Least s wf.rel
:= (
  WellFounded.fix (subtypeWellfounded s).wf fun
    (t: ↑s)
    (rc: (tt: ↑s) → wf.rel tt t → Least s wf.rel)
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
    def free (m: Morphism wa wb) (b: wb.T): Prop :=
      ∀ aa: wa.T, b ≠ m.f aa
    
    -- Not sure if the terminology corresponds to category
    -- theory. An initial morphism picks the least elements possible.
    def isInitial (m: Morphism wa wb): Prop :=
      ∀ a: wa.T, ∀ b: wb.T, b < m.f a → ∃ aa: wa.T, b = m.f aa
    
    def nInitial.helperHelper
      (m: Morphism wa wb)
      (a: wa.T)
      (prop: ¬ (b < m.f a ∧ ∀ aa: wa.T, b ≠ m.f aa))
    :
      b < m.f a → ∃ aa: wa.T, b = m.f aa
    :=
      fun bLtMfA =>
        let notAll: ¬ ∀ aa: wa.T, b ≠ m.f aa := fun all =>
          prop (And.intro bLtMfA all)
        
        byContradiction fun nope =>
          let ini: ∀ aa: wa.T, b ≠ m.f aa :=
            fun aa => fun p => nope ⟨aa, p⟩
          notAll ini
    
    def nInitial.helper
      (m: Morphism wa wb)
      (a: wa.T)
      (prop: ¬ ∃ b: wb.T, b < m.f a ∧ ∀ aa: wa.T, b ≠ m.f aa)
    :
      ∀ b: wb.T, b < m.f a → ∃ aa: wa.T, b = m.f aa
    :=
      fun b => nInitial.helperHelper m a fun p => prop ⟨b, p⟩
    
    def nInitial
      {m: Morphism wa wb}
      (nIni: ¬ isInitial m)
    :
      ∃ a: wa.T, ∃ b: wb.T, b < m.f a ∧ (free m b)
    :=
      byContradiction fun nope =>
        let ini: ∀ a: wa.T, ∀ b: wb.T, b < m.f a → ∃ aa: wa.T, b = m.f aa :=
          fun a => nInitial.helper m a fun ex => nope ⟨a, ex⟩
        nIni ini
    
    
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
            let wLtAC: c < a = lt (some c) (some a) := rfl
            have: c < a := wLtAC ▸ ltB
            wf c
    ) -- It's also a shame that you have significant whitespace.
     wf a
    termination_by succ.wf w a => a
    -/
    
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
  
  
  def Morphism.helperOut
    {wa: WellOrder}
    (fA: wa.T)
    (aSucc: wa.succ.T)
    (aa: wa.T)
    (a: aSucc = some fA)
    (b: wa.succ.lt (some aa) aSucc)
  := a ▸ b
  
  noncomputable def Morphism.initial.helper
    (m: Morphism wa wb)
    (aSucc: wa.succ.T)
  :
    { mi: Morphism wa wb //
      (∀ a: wa.T, mi.f a < m.f a ∨ mi.f a = m.f a) ∧
      ∀ (a: wa.T) (b: wb.T),
        wa.succ.lt (some a) aSucc →
        b < mi.f a ∨ b = mi.f a →
        ¬ Morphism.free mi b
    }
  :=
    let rc (aa: { aa: wa.T // wa.succ.lt (some aa) aSucc }) :=
      let wf: wa.succ.lt (some aa.val) aSucc := aa.property
      initial.helper m (some aa)
    
    let leEq (fA: wa.T) (b: wb.T) :=
      ∃ aa: { aa: wa.T // wa.succ.lt (some aa) aSucc }, (rc aa).val.f fA = b
    
    let leNeq (b: wb.T) :=
      ∀ aa: { aa: wa.T // wa.succ.lt (some aa) aSucc }, (rc aa).val.f aa ≠ b
    
    
    let partLt (fA: wa.T) (hLt: wa.succ.lt (some fA) aSucc) :=
      least (leEq fA) ⟨(rc ⟨fA, hLt⟩).val.f fA, ⟨⟨fA, hLt⟩, rfl⟩⟩
    
    let partEq (fA: wa.T) (hEq: some fA = aSucc) :=
      least leNeq
        ⟨
          m.f fA,
          fun aa eq =>
            let aaLtA: aa < fA := Morphism.helperOut fA aSucc aa hEq.symm aa.property
            let prevF := (rc aa).val.f
            
            let prevFAaLeMfA: prevF aa < m.f aa ∨ prevF aa = m.f aa :=
              (rc aa).property.left aa
            
            let mfAaLtMfFA: m.f aa < m.f fA := (m.ordPres aa fA).mp aaLtA
            
            let prevFAaLtFFA: prevF aa < m.f fA := prevFAaLeMfA.elim
              (fun lt => WellOrder.lt.trans lt mfAaLtMfFA)
              (fun eq => eq ▸ mfAaLtMfFA)
            
            wfRel.irefl (m.f fA) (eq ▸ prevFAaLtFFA)
        ⟩
    
    
    let f (fA: wa.T): wb.T :=
      if hLt: wa.succ.lt (some fA) aSucc then
        (partLt fA hLt).val
      else if hEq: some fA = aSucc then
        (partEq fA hEq).val
      else m.f fA
    
    
    let mi: Morphism wa wb := {
      f := f
      ordPres := fun a0 a1 => Iff.intro (
        fun a0LtA1 =>
          let ifLtASucc: wa.succ.lt (some a1) aSucc → f a0 < f a1 :=
            fun ltA1 =>
              let ltSomeA0: wa.succ.lt (some a0) (some a1) := a0LtA1
              let ltA0: wa.succ.lt (some a0) aSucc :=
                lt.trans ltSomeA0 ltA1
              
              let fA0Prop: Least (leEq a0) wb.lt := partLt a0 ltA0
              let eqA0: fA0Prop.val = f a0 := (if_pos ltA0).symm
              
              let fA1Prop: Least (leEq a1) wb.lt := partLt a1 ltA1
              let eqA1: fA1Prop.val = f a1 := (if_pos ltA1).symm
              
              let aDefA1 := choiceEx fA1Prop.property.left
              let mid := (rc aDefA1).val.f a0
              
              let ltEqLeft: f a0 < mid ∨ f a0 = mid :=
                let leEqMid: leEq a0 mid := ⟨aDefA1, rfl⟩
                let fA0PropLtAll:
                  fA0Prop.val < mid ∨ fA0Prop.val = mid
                :=
                  (wb.total mid fA0Prop.val).elim
                    (fun ltMid =>
                      let nLeEqMid := fA0Prop.property.right mid ltMid
                      False.elim (nLeEqMid leEqMid))
                    (fun eqOrGt => eqOrGt.elim
                      (fun gtMid => Or.inl gtMid)
                      (fun eq => Or.inr eq.symm))
                eqA0 ▸ fA0PropLtAll
              let eqRight: (rc aDefA1).val.f a1 = f a1 :=
                aDefA1.property.trans eqA1
              
              let ltMidTmp: mid < (rc aDefA1).val.f a1 :=
                ((rc aDefA1).val.ordPres a0 a1).mp a0LtA1
              let ltMid: mid < f a1 :=
                eqRight ▸ ltMidTmp
              
              ltEqLeft.elim
                (fun ltLeft => lt.trans ltLeft ltMid)
                (fun eqLeft => eqLeft ▸ ltMid)
          
          let ifEqASucc: some a1 = aSucc → f a0 < f a1 :=
            fun eqFA =>
              sorry
          
          let ifGtASucc:  wa.succ.lt aSucc (some a1) → f a0 < f a1 :=
            fun gtFA =>
              sorry
          
          (wa.succ.total (some a1) aSucc).elim
            ifLtASucc (fun ge => ge.elim ifGtASucc ifEqASucc)
        ) (
          fun fALtFB => sorry
        )
    }
    
    ⟨mi, sorry⟩
    termination_by initial.helper m a => a
  
  noncomputable def Morphism.initial (m: Morphism wa wb): Morphism.Initial wa wb :=
    let mIni := Morphism.initial.helper m none
    ⟨
      mIni,
      fun a b bLt =>
        let bNotFree := mIni.property.right a b trivial (Or.inl bLt)
        
        byContradiction fun nope =>
          let ini: ∀ aa: wa.T, b ≠ mIni.val.f aa :=
            fun aa => fun p => nope ⟨aa, p⟩
          bNotFree ini
    ⟩
  
  
  structure PreIsomorphism -- TODO do I even need you?
    (wa wb: WellOrder)
    (a: wa.succ.T)
    (fOrig: wa.T → wb.T)
  where
    f: wa.T → wb.T
    g: wb.T → wa.T
    
    fLe: ∀ a: wa.T, f a < fOrig a ∨ f a = fOrig a
    
    bijA: ∀ aa: wa.T, wa.succ.lt (some aa) a              → g (f aa) = aa
    bijB: ∀ bb: wb.T, wb.succ.lt (some bb) ((succ.f f) a) → f (g bb) = bb
    
    ordPres: ∀ a b: wa.T, a < b ↔ f a < f b
  
  noncomputable def Isomorphism.fromMorphisms -- TODO do I even need you?
    {wa wb: WellOrder}
    (ma: Morphism wa wb)
    (mb: Morphism wb wa)
  :
    Isomorphism wa wb
  :=
    let preIso: PreIsomorphism wa wb none ma.f
    := (
      WellFounded.fix wa.succ.wf fun
        (aSucc: wa.succ.T)
        (rc:
          (aaSucc: wa.succ.T) →
          wa.succ.lt aaSucc aSucc →
          PreIsomorphism wa wb aaSucc ma.f)
      =>
        let f := fun a => if h0: wa.succ.lt (some a) aSucc then
          (rc (some a) h0).f a
        else if h1: some a = aSucc then
          (
            least (
              fun b: wb.T =>
                ∀ aa: wa.T,
                  (h: wa.lt aa a) →
                  wb.lt ((rc (some aa) (by rw [h1.symm]; exact h)).f aa) b
            ) ⟨
              ma.f a,
              fun aa aaLtA =>
                let prevPreIso: PreIsomorphism wa wb (some aa) ma.f :=
                  (rc (some aa) (by rw [h1.symm]; exact aaLtA))
                
                let fAaLeFOrigAa:
                  prevPreIso.f aa < ma.f aa ∨ prevPreIso.f aa = ma.f aa
                :=
                  prevPreIso.fLe aa
                
                let fAaLeFOrigA: prevPreIso.f aa < ma.f a :=
                  fAaLeFOrigAa.elim (
                    fun lt =>
                      WellOrder.lt.trans lt ((ma.ordPres aa a).mp aaLtA)
                  ) (
                    fun eq => eq ▸ ((ma.ordPres aa a).mp aaLtA)
                  )
                
                let asdf := ma.ordPres
                sorry
            ⟩
          ).val
        else sorry
        
        let g := sorry
        
        {
          f := f
          g := g
        }
    ) none
    
    {
      f := preIso.f
      g := preIso.g
      
      bijA := fun a => (preIso.bijA a) trivial
      bijB := fun b => (preIso.bijB b) trivial
      
      ordPres := preIso.ordPres
    }
  
  
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
  
  -- TODO do I need you?
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
    
    sorry
  
  
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
    Least
      (fun bSucc: wb.succ.T => ∀ b: wb.T, bSucc = some b → m.free b)
      wb.succ.lt
  :=
    @least wb.succ.T (wfWT wb.succ)
      (fun bSucc => ∀ b: wb.T, bSucc = some b → m.free b)
      ⟨none, fun _ nope => False.elim (Option.noConfusion nope)⟩
  
  noncomputable def ordIn (m: Morphism wa wb): wb.succ.T
  :=
    (ordInProp m).val
  
  def metaLt (wa wb: WellOrder): Prop :=
    ¬ isIsomorphic wa wb ∧ ∃ _: Morphism wa wb, True
  
  def ordInEqIff
    {wa wb wc: WellOrder}
    (mac: Morphism.Initial wa wc)
    (mbc: Morphism.Initial wb wc)
  :
    ordIn mac.val = ordIn mbc.val ↔ isIsomorphic wa ab
  :=
    sorry
  
  def ordInLtIff
    {wa wb wc: WellOrder}
    (mac: Morphism.Initial wa wc)
    (mbc: Morphism.Initial wb wc)
  :
    ordIn mac.val < ordIn mbc.val ↔ metaLt wa wb
  :=
    sorry
  
  
  def metaWf (wc: WellOrder): Acc metaLt wc :=
    -- The syntax `wc.succ.morphism` should be a shorthand
    -- for `WellOrder.succ.morphism wc`.
    -- Also, what's a normal way of proving this from `ordInLtIff`?
    
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
            (ordInLtIff macIni mbcIni).mpr waLtWb
          
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
    
    ordPres := fun a b => -- asdf
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

