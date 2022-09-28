/-
  Defines ordinals. Takes heavy inspiration from mathlib
  (I guess -- I wrote this comment before defining them).
  Update: so I guess I freestyle a lot.
-/

import Set

open Classical


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
  
  def isIsomorphic.refl: isIsomorphic wa wa :=
     ⟨WellOrder.selfIsomorphism wa, trivial⟩
  
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
    | some a, some b => w.lt a b
  
  def succ.wf (w: WellOrder) (a: w.T): Acc (succ.lt w) (some a) :=
      Acc.intro (some a) fun (b: Option w.T) ltB =>
        match b with
        | none => False.elim ltB
        | some c =>
            let wLtAC: w.lt c a = lt w (some c) (some a) := rfl
            have: w.lt c a := wLtAC ▸ ltB
            have: WellFounded w.lt := w.wf
            succ.wf w c
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
            let wLtAC: w.lt c a = lt (some c) (some a) := rfl
            have: w.lt c a := wLtAC ▸ ltB
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
            let a: w.lt x y = succ.lt w (some x) (some y) := rfl
            let b: w.lt y x = succ.lt w (some y) (some x) := rfl
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
  
  def isGreatest (w: WellOrder) (gst: w.T) := ∀ t: w.T, t = gst ∨ w.lt t gst
  
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
  
  @[reducible] def pred.lt
    (w: WellOrder)
    (t0 t1: { t: w.T // ¬ isGreatest w t })
  :=
    w.lt t0.val t1.val
  
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
end WellOrder


instance wellOrderSetoid: Setoid WellOrder where
  r (a b: WellOrder) := WellOrder.isIsomorphic a b
  iseqv := {
    -- When `selfIsomorphism` is renamed to `Isomorphism.refl`, this
    -- should work >:(
    -- 
    -- refl := fun x => ⟨x.Isomorphism.refl, trivial⟩
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

