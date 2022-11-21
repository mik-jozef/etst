import Ordinal

open Classical


-- Named after https://xkcd.com/468/.
def notOnYourList
  (f: T → Set T)
:
  { s: Set T // ∀ t: T, f t ≠ s }
:= ⟨
  fun t => ¬ (f t t),
  fun t eq =>
    if h: t ∈ f t then
      (eq ▸ h) h
    else
      (eq ▸ h) h
⟩


def isInjection (f: A → B): Prop := ∀ a0 a1: A, f a0 = f a1 → a0 = a1

def range (f: A → B): Set B :=
  fun b => ∃ a, f a = b


noncomputable def inverse (f: A → B):
  ↑(range f) → A
:=
  fun t => choiceEx t.property

def inverse.eqRight (f: A → B) (b: ↑(range f)):
  f (inverse f b) = b
:=
  (choiceEx b.property).property

def inverse.inj
  (f: A → B)
  (b0 b1: ↑(range f))
  (eq: inverse f b0 = inverse f b1)
:
    b0 = b1
:=
  let eq0: f (inverse f b1) = b0 :=
    eq.symm ▸ inverse.eqRight f b0
  
  let eq1: f (inverse f b1) = b1 :=
    inverse.eqRight f b1
  
  Subtype.eq (eq0.symm.trans eq1)

def inverse.eqLeft (f: A → B) (fInj: isInjection f) {b: B} (eq: f a = b):
  inverse f ⟨b, ⟨a, eq⟩⟩ = a
:=
  let bInRange: { b // b ∈ range f } := ⟨b, ⟨a, eq⟩⟩
  let eqRight := inverse.eqRight f bInRange
  fInj _ _ (eqRight.trans eq.symm)


@[reducible] def initialWellOrder.TT
  {T: Type}
  (f: Ordinal → T)
  (n: Ordinal)
:
  Type
:=
  { t: T // ∃ nn: ↑n, f nn = t }

def initialWellOrder.wfRel
  (f: Ordinal → T)
  (n: Ordinal)
:
  WellFoundedRelation (TT f n)
:=
  let toOrdinal (t: TT f n): Ordinal :=
  let tInv := choiceEx t.property
  let tInRange: t.val ∈ range f := ⟨tInv.val, tInv.property⟩
  inverse f ⟨t, tInRange⟩

invImage toOrdinal Ordinal.wfOrd

def initialWellOrder
  (f: Ordinal → T)
  (fInj: isInjection f)
  (n: Ordinal)
:
  WellOrder
:=
  let lt :=
    fun t0 t1: initialWellOrder.TT f n =>
      let t0Inv := choiceEx t0.property
      let t1Inv := choiceEx t1.property
      
      let t0InRange: t0.val ∈ range f := ⟨t0Inv.val, t0Inv.property⟩
      let t1InRange: t1.val ∈ range f := ⟨t1Inv.val, t1Inv.property⟩
      
      inverse f ⟨t0, t0InRange⟩ < inverse f ⟨t1, t1InRange⟩
  
  {
    T := initialWellOrder.TT f n
    lt := lt
    
    total :=
      -- TODO replace with sth general, similar to `invImage`?
      fun t0 t1: initialWellOrder.TT f n =>
        let t0Inv := choiceEx t0.property
        let t1Inv := choiceEx t1.property
        
        let t0IsInRange: t0.val ∈ range f := ⟨t0Inv.val, t0Inv.property⟩
        let t1IsInRange: t1.val ∈ range f := ⟨t1Inv.val, t1Inv.property⟩
        
        let t0InRange: { t: T // t ∈ range f } := ⟨t0, t0IsInRange⟩
        let t1InRange: { t: T // t ∈ range f } := ⟨t1, t1IsInRange⟩
        
        let t0InverseEq := inverse.eqRight f t0InRange
        let t1InverseEq := inverse.eqRight f t1InRange
        
        let t0InvEq: t0Inv.val = inverse f t0InRange :=
          fInj _ _ (t0Inv.property.trans t0InverseEq.symm)
        let t1InvEq: t1Inv.val = inverse f t1InRange :=
          fInj _ _ (t1Inv.property.trans t1InverseEq.symm)
        
        (t0Inv.val.val.total t1Inv.val).elim
          (fun lt =>
            let ltOut: inverse f t0InRange < inverse f t1InRange :=
              t0InvEq ▸ t1InvEq ▸ lt
              
            Or.inl ltOut)
          (fun gtOrEq => gtOrEq.elim
            (fun gt =>
              let gtOut: inverse f t1InRange < inverse f t0InRange :=
                t0InvEq ▸ t1InvEq ▸ gt
              
              Or.inr (Or.inl gtOut))
            (fun eq =>
              let eqInRange :=
                inverse.inj f t0InRange t1InRange (t0InvEq ▸ t1InvEq ▸ eq)
              
              let eqVal: t0.val = t1.val := Subtype.noConfusion eqInRange id
              
              Or.inr (Or.inr (Subtype.eq eqVal))))
    
    wf :=
      let toOrdinal (t: initialWellOrder.TT f n): Ordinal :=
        let tInv := choiceEx t.property
        let tInRange: t.val ∈ range f := ⟨tInv.val, tInv.property⟩
        inverse f ⟨t, tInRange⟩
      
      (invImage toOrdinal Ordinal.wfOrd).wf
  }

def initialWellOrder.monoSucc
  (f: Ordinal → T)
  (fInj: isInjection f)
  (nn n: Ordinal)
  (nLt: nn < n)
:
  (initialWellOrder f fInj nn).succ ≤ initialWellOrder f fInj n
:=
  let iniWONnSucc := (initialWellOrder f fInj nn).succ
  let iniWON := initialWellOrder f fInj n
  let TT := Option { t: T // ∃ nnn: ↑nn, f nnn = t }
  
  let mf (tOpt: TT): iniWON.T :=
    match tOpt with
      | none => ⟨f nn, ⟨⟨nn, nLt⟩, rfl⟩⟩
      | some t =>
          let tIndex := choiceEx t.property
          let tIndexLt := ⟨
            tIndex.val,
            Ordinal.lt.trans tIndex.val.property nLt
          ⟩
          
          ⟨t, ⟨tIndexLt, tIndex.property⟩⟩
  
  let ordPres: (a b: TT) → iniWONnSucc.lt a b ↔ iniWON.lt (mf a) (mf b)
    | none, none =>
        Iff.intro
          (fun nope => False.elim nope)
          (fun nope => wfRel.irefl (mf none) nope)
    | none, some t1 =>
        Iff.intro
          (fun nope => False.elim nope)
          (fun ltMfAMfB =>
            let t1Index := choiceEx t1.property
            let t1IndexEq: t1 = f t1Index.val := t1Index.property.symm
            let ltTIndexNn: t1Index.val < nn := t1Index.val.property
            let ltTIndexN: t1Index.val < n := Ordinal.lt.trans ltTIndexNn nLt
            
            let fNn: iniWON.T := ⟨f nn, ⟨⟨nn, nLt⟩, rfl⟩⟩
            let fT1Index: iniWON.T :=
              ⟨f t1Index.val, ⟨⟨t1Index.val, ltTIndexN⟩, rfl⟩⟩
            
            let fNnIsInRange: fNn.val ∈ range f := ⟨nn, rfl⟩
            let fT1IsIndexInRange: fT1Index.val ∈ range f := ⟨t1Index.val, rfl⟩
            
            let fNnInRange: ↑(range f) := ⟨fNn.val, fNnIsInRange⟩
            let fT1IndexInRange: ↑(range f) := ⟨fT1Index.val, fT1IsIndexInRange⟩
            
            let mfAEq: mf none = fNn := Subtype.eq rfl
            let mfBEq: mf (some t1) = fT1Index := Subtype.eq t1IndexEq
            
            let invEqT1: inverse f fT1IndexInRange = t1Index.val :=
              inverse.eqLeft f fInj rfl
            
            let invEqNn: inverse f fNnInRange = nn :=
              inverse.eqLeft f fInj rfl
            
            let invLt: inverse f fT1IndexInRange < inverse f fNnInRange :=
              invEqNn ▸ invEqT1 ▸ ltTIndexNn
            
            let ltMfBMfA: mf (some t1) < mf none := mfAEq ▸ mfBEq ▸ invLt
            
            False.elim
              (@wfRel.antisymm.false
                iniWON.T
                (initialWellOrder.wfRel f n)
                (mf none)
                (mf (some t1))
                ltMfAMfB
                ltMfBMfA))
    | some t0, none =>
        Iff.intro
          (fun _ =>
            let t0Index := choiceEx t0.property
            let t0IndexEq: t0 = f t0Index.val := t0Index.property.symm
            let ltTIndexNn: t0Index.val < nn := t0Index.val.property
            let ltTIndexN: t0Index.val < n := Ordinal.lt.trans ltTIndexNn nLt
            
            let fNn: iniWON.T := ⟨f nn, ⟨⟨nn, nLt⟩, rfl⟩⟩
            let fT0Index: iniWON.T :=
              ⟨f t0Index.val, ⟨⟨t0Index.val, ltTIndexN⟩, rfl⟩⟩
            
            let fNnIsInRange: fNn.val ∈ range f := ⟨nn, rfl⟩
            let fT0IsIndexInRange: fT0Index.val ∈ range f := ⟨t0Index.val, rfl⟩
            
            let fNnInRange: ↑(range f) := ⟨fNn.val, fNnIsInRange⟩
            let fT0IndexInRange: ↑(range f) := ⟨fT0Index.val, fT0IsIndexInRange⟩
            
            let mfAEq: mf none = fNn := Subtype.eq rfl
            let mfBEq: mf (some t0) = fT0Index := Subtype.eq t0IndexEq
            
            let invEqT0: inverse f fT0IndexInRange = t0Index.val :=
              inverse.eqLeft f fInj rfl
            
            let invEqNn: inverse f fNnInRange = nn :=
              inverse.eqLeft f fInj rfl
            
            let invLt: inverse f fT0IndexInRange < inverse f fNnInRange :=
              invEqNn ▸ invEqT0 ▸ ltTIndexNn
            
            mfAEq ▸ mfBEq ▸ invLt)
          (fun _ => trivial)
    | some _, some _ => Iff.intro id id
  
  WellOrder.Morphism.le {
    f := mf
    ordPres := ordPres
  }

def initialWellOrder.monoLt
  (f: Ordinal → T)
  (fInj: isInjection f)
  (nn n: Ordinal)
  (nLt: nn < n)
:
  initialWellOrder f fInj nn < initialWellOrder f fInj n
:=
  let ltSucc:
    initialWellOrder f fInj nn < (initialWellOrder f fInj nn).succ
  :=
    WellOrder.succGt (initialWellOrder f fInj nn)
  WellOrder.ltle.trans ltSucc (initialWellOrder.monoSucc f fInj nn n nLt)

def initialWellOrder.monoLe
  (f: Ordinal → T)
  (fInj: isInjection f)
  (nn n: Ordinal)
  (nLt: nn ≤ n)
:
  initialWellOrder f fInj nn ≤ initialWellOrder f fInj n
:=
  nLt.elim
    (fun lt =>
      Or.inl (initialWellOrder.monoLt f fInj nn n lt))
    (fun eq => Or.inr (eq ▸ WellOrder.isIsomorphic.refl))

def initialWellOrder.le
  (f: Ordinal → T)
  (fInj: isInjection f)
  (n: Ordinal)
:
  n ≤ Ordinal.mk (initialWellOrder f fInj n)
:=
  let iniWO := initialWellOrder f fInj n
  let iniOrd := Ordinal.mk iniWO
  
  if h: n.isLimit then
    let isUB (nn: ↑n): nn ≤ iniOrd :=
      let leIniNn: nn ≤ Ordinal.mk (initialWellOrder f fInj nn) :=
        have: nn < n := nn.property
        initialWellOrder.le f fInj nn
      
      let leNnNWO := initialWellOrder.monoLe f fInj nn.val n (Or.inl nn.property)
      
      Ordinal.le.trans leIniNn (Ordinal.le.fromWO leNnNWO)
    
    (Ordinal.limit.isSup n h).right iniOrd isUB
  else
    let nPred := Ordinal.nLimit.pred n h
    let nPredLt := Ordinal.nLimit.pred.lt n h
    
    let iniWO := initialWellOrder f fInj n
    let iniOrd := Ordinal.mk iniWO
    
    let iniWOPred := initialWellOrder f fInj nPred
    let iniOrdPred := Ordinal.mk iniWOPred
    
    --let le: iniWO ≤ iniWOPred := initialWellOrder.le f fInj nPred
    let le: nPred ≤ iniOrdPred := initialWellOrder.le f fInj nPred
    
    let monoLt: iniOrdPred < iniOrd :=
      initialWellOrder.monoLt f fInj nPred n nPredLt
    
    let lt: nPred < iniOrd := Ordinal.lelt.trans le monoLt
    
    let succLe: nPred.val.succ ≤ iniOrd := Ordinal.lt.succLe lt
    
    by conv =>
      lhs
      rw [nPred.property.symm]; exact succLe
termination_by initialWellOrder.le f fInj n => n

def hartogsNumber.pred.wellOrder (f: Ordinal → T): WellOrder :=
  let R := range f
  
  let lt := fun t0 t1 => inverse f t0 < inverse f t1
  
  {
    T := R
    lt := lt
    
    total :=
      fun t0 t1 =>
        ((inverse f t0).total (inverse f t1)).elim
          (fun lt => Or.inl lt)
          (fun gtOrEq => gtOrEq.elim
            (fun gt => Or.inr (Or.inl gt))
            (fun eq =>
              Or.inr (Or.inr (inverse.inj f t0 t1 eq))))
    
    wf := (
      invImage (fun t: ↑R => inverse f t) Ordinal.wfOrd
    ).wf
  }

def hartogsNumber.pred (f: Ordinal → T): Ordinal :=
  Ordinal.mk (hartogsNumber.pred.wellOrder f)

-- TODO From this, it follows that the inverse cannot be the Hartogs'
-- number, because then the Hartogs' number would be less than its predecessor.
def hartogsNumber.pred.le
  (f: Ordinal → T)
  (fInj: isInjection f)
  (t: ↑(range f))
:
  inverse f t ≤ hartogsNumber.pred f
:=
  let tInv := inverse f t
  
  let iiWO := initialWellOrder f fInj tInv
  let hnPredWO := hartogsNumber.pred.wellOrder f
  let hnPred := hartogsNumber.pred f
  
  let m: WellOrder.Morphism iiWO hnPredWO := {
    f := fun t =>
      let whatIsThis := choiceEx t.property
      ⟨t.val, ⟨whatIsThis.val, whatIsThis.property⟩⟩
    ordPres := fun _ _ => Iff.intro id id
  }
  
  let leWO: iiWO ≤ hnPredWO := WellOrder.Morphism.le m
  
  let leOrd: Ordinal.mk iiWO ≤ hnPred := Ordinal.le.fromWO leWO
  
  let le: inverse f t ≤ Ordinal.mk iiWO :=
    initialWellOrder.le f fInj tInv
  
  Ordinal.le.trans le leOrd


-- This definition is probably not equivalent to the standard
-- one, but I don't care. Morally, it is close enough, and all
-- I care about is proving `allOrdMapsRepeat`.
def hartogsNumber (f: Ordinal → T): Ordinal :=
  (hartogsNumber.pred f).succ

def hartogsNumber.lt
  (f: Ordinal → T)
  (fInj: isInjection f)
  (t: ↑(range f))
:
  inverse f t < hartogsNumber f
:=
  let le := hartogsNumber.pred.le f fInj t
  let ltSucc: hartogsNumber.pred f < hartogsNumber f :=
    Ordinal.succGt (hartogsNumber.pred f)
  
  Ordinal.lelt.trans le ltSucc


def ordinalMap.notInjection
  (f: Ordinal → T)
:
  ¬ isInjection f
:=
  fun fInj =>
    let R := range f
    
    let t := f (hartogsNumber f)
    let tIsInRange: t ∈ R := ⟨hartogsNumber f, rfl⟩
    let tInRange: ↑(range f) := ⟨t, tIsInRange⟩
    
    
    let invEqHN: inverse f tInRange = hartogsNumber f :=
      inverse.eqLeft f fInj rfl
    
    let invLtHN: inverse f tInRange < hartogsNumber f :=
      hartogsNumber.lt f fInj tInRange
    
    wfRel.irefl (hartogsNumber f) (invEqHN ▸ invLtHN)

/-
def initiallyInjection.range.eq -- TODO do I need you?
  (f: Ordinal → T)
  (fInj: isInjection f)
:
  range f = (fun _ => True)
:=
  byContradiction fun rangeLt =>
    let exNotInRange: ∃ t: T, t ∉ range f :=
      byContradiction fun nEx =>
        let allInRange: ∀ t: T, t ∈ range f :=
          fun t =>
            if h: t ∈ range f then
              h
            else
              False.elim (nEx ⟨t, h⟩)
        
        rangeLt
          (funext
            (fun t =>
              propext
                (Iff.intro
                  (fun _ => trivial)
                  (fun _ => allInRange t))))
    sorry
-/


noncomputable def allOrdMapsRepeat
  (f: Ordinal → T)
:
  ∃ n0 n1: Ordinal, f n0 = f n1
:=
  if h: isInjection f then
    False.elim (ordinalMap.notInjection f h)
  else
    byContradiction fun nope =>
      h (fun n0 n1 eq => False.elim (nope ⟨n0, ⟨n1, eq⟩⟩))
