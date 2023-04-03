import Set
import Fixpoint

open Classical


structure Set3 (D: Type u) where
  defMem: Set D -- The definitive members
  posMem: Set D -- The possible members
  defLePos: defMem ≤ posMem

namespace Set3
  protected def eq:
    {a b: Set3 D} →
    a.defMem = b.defMem →
    a.posMem = b.posMem
  →
    a = b
  -- Thanks to answerers of https://proofassistants.stackexchange.com/q/1747
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl
  
  def empty {D: Type}: Set3 D := ⟨Set.empty, Set.empty, PartialOrder.refl _⟩
  
  def undetermined {D: Type}: Set3 D := ⟨Set.empty, Set.full, fun _ => False.elim⟩
  
  def just {D: Type} (d: D): Set3 D := ⟨Set.just d, Set.just d, PartialOrder.refl _⟩
  
  
  def empty.nin.def (d: D): d ∉ Set3.empty.defMem := False.elim
  def empty.nin.pos (d: D): d ∉ Set3.empty.posMem := False.elim
  
  -- :( def empty.fromNoPos (noPos (d: D):)
  def empty.fromNoPos (noPos: ∀ d: D, d ∉ s.posMem): s = Set3.empty :=
    Set3.eq
      (funext fun d =>
        propext
          (Iff.intro
            (fun dInSDef =>
              let dInSPos := s.defLePos d dInSDef
              noPos d dInSPos)
            (fun nope => False.elim nope)))
      (funext fun d =>
        propext
          (Iff.intro
            (fun dInSPos => noPos d dInSPos)
            (fun nope => False.elim nope)))
  
  
  instance: LE (Set3 D) where
    le (a b: Set3 D) := a.defMem ≤ b.defMem  ∧  a.posMem ≤ b.posMem
  
  instance: SqLE (Set3 D) where
    le (a b: Set3 D) := a.defMem ≤ b.defMem  ∧  b.posMem ≤ a.posMem
  
  
  instance ord.standard.st (D: Type): PartialOrderSt (Set3 D) where
    refl (a: Set3 D) :=
      And.intro (PartialOrder.refl (a.defMem)) (PartialOrder.refl (a.posMem))
    
    antisymm (a b: Set3 D) (ab: a ≤ b) (ba: b ≤ a) :=
      let defEq: a.defMem = b.defMem :=
        PartialOrder.antisymm a.defMem b.defMem ab.left ba.left;
      let posEq: a.posMem = b.posMem :=
        PartialOrder.antisymm a.posMem b.posMem ab.right ba.right;
      Set3.eq defEq posEq
    
    trans (a b c: Set3 D) (ab: a ≤ b) (bc: b ≤ c) :=
      And.intro
        (PartialOrder.trans a.defMem b.defMem c.defMem ab.left bc.left)
        (PartialOrder.trans a.posMem b.posMem c.posMem ab.right bc.right)
    
    ltToLeNeq := id
    leNeqToLt := id
  
  def ord.standard (D: Type) := (ord.standard.st D).toPartialOrder
  
  def ord.standard.sup (s: Set (Set3 D)): Supremum (standard D) s :=
    let sup := {
      defMem := fun d => ∃s: ↑s, d ∈ s.val.defMem
      posMem := fun d => ∃s: ↑s, d ∈ s.val.posMem
      defLePos :=
        fun d dDef =>
          let s := choiceEx dDef
          ⟨s, s.val.val.defLePos d s.property⟩
    }
    ⟨
      sup,
      And.intro
        (fun s =>
          And.intro
            -- Why tf is this unfolding required???
            (fun d dMem => by unfold defMem; exact ⟨s, dMem⟩)
            (fun d dMem => by unfold posMem; exact ⟨s, dMem⟩))
        fun ub ubIsUB =>
          And.intro
            (fun d dMemSupWtf =>
              -- WHAT THE ACTUAL FLYING why is `by exact` necessary here???
              let dMemSup: ∃s: ↑s, d ∈ s.val.defMem := by exact dMemSupWtf;
              let s := choiceEx dMemSup
              let sLeUb: s.val.val .≤ ub := ubIsUB s
              let dInS: d ∈ s.val.val.defMem := s.property
              sLeUb.left d dInS)
            (fun d dMemSupWtf =>
              let dMemSup: ∃s: ↑s, d ∈ s.val.posMem := by exact dMemSupWtf;
              let s := choiceEx dMemSup
              let sLeUb: s.val.val .≤ ub := ubIsUB s
              let dInS: d ∈ s.val.val.posMem := s.property
              sLeUb.right d dInS)
    ⟩
  
  
  instance ord.approximation.sq (D: Type): PartialOrderSq (Set3 D) where
    refl (a: Set3 D) :=
      And.intro (PartialOrder.refl (a.defMem)) (PartialOrder.refl (a.posMem))
    
    antisymm (a b: Set3 D) (ab: a ⊑ b) (ba: b ⊑ a) :=
      let defEq: a.defMem = b.defMem :=
        PartialOrder.antisymm a.defMem b.defMem ab.left ba.left;
      let posEq: a.posMem = b.posMem :=
        PartialOrder.antisymm a.posMem b.posMem ba.right ab.right;
      Set3.eq defEq posEq
    
    trans (a b c: Set3 D) (ab: a ⊑ b) (bc: b ⊑ c) :=
      And.intro
        (PartialOrder.trans a.defMem b.defMem c.defMem ab.left bc.left)
        (PartialOrder.trans c.posMem b.posMem a.posMem bc.right ab.right)
    
    ltToLeNeq := id
    leNeqToLt := id
  
  def ord.approximation (D: Type) := (ord.approximation.sq D).toPartialOrder
  
  def ord.approximation.sup (ch: Chain (approximation D)):
    Supremum (approximation D) ch.val
  :=
    let sup: Set3 D := {
      defMem := fun d => ∃s: ↑ch.val, d ∈ s.val.defMem
      posMem := fun d => ∀s: ↑ch.val, d ∈ s.val.posMem
      defLePos :=
        fun d dDef s =>
          let sOfD := choiceEx dDef
          let sSOfDComparable := ch.property s sOfD
          
          sSOfDComparable.elim
            (fun sLt =>
              let dSOfDPos: d ∈ sOfD.val.val.posMem :=
                sOfD.val.val.defLePos d sOfD.property
              sLt.right d dSOfDPos)
            (fun sGt =>
              let dSDef: d ∈ s.val.defMem :=
                sGt.left d sOfD.property
              s.val.defLePos d dSDef)
    }
    ⟨
      sup,
      And.intro
        (fun s =>
          And.intro
            (fun _ dMem => ⟨s, dMem⟩)
            (fun _ dMemSup => dMemSup s))
        fun ub ubIsUB =>
          And.intro
            (fun d dMemSup =>
              let s := choiceEx dMemSup
              let sLeUb: s.val.val .≤ ub := ubIsUB s
              let dInS: d ∈ s.val.val.defMem := s.property
              sLeUb.left d dInS)
            (fun d dMemUB s =>
              let sLeUb: s.val .≤ ub := ubIsUB s
              sLeUb.right d dMemUB)
    ⟩
  
  
  def ord.standard.isChainComplete (D: Type):
    isChainComplete (ord.standard D)
  :=
    fun ch => ⟨(sup ch.val).val, (sup ch.val).property⟩
  
  def ord.approximation.isChainComplete (D: Type):
    isChainComplete (ord.approximation D)
  :=
    fun ch => ⟨(sup ch).val, (sup ch).property⟩
  
  
  def ninPos.ninDef {s: Set3 D} (dNin: d ∉ s.posMem): d ∉ s.defMem :=
    fun dIn => dNin (s.defLePos d dIn)
  
  
  def without (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => dd ∈ s.defMem ∧ dd ≠ d
    posMem := fun dd => dd ∈ s.posMem ∧ dd ≠ d
    defLePos :=
      fun dd ddDef =>
        And.intro (s.defLePos dd ddDef.left) ddDef.right
  }
  
  def without.ninPos (s: Set3 D) (d: D): d ∉ (s.without d).posMem :=
    fun dIn => dIn.right rfl
  
  def without.ninDef (s: Set3 D) (d: D): d ∉ (s.without d).defMem :=
    fun dIn => dIn.right rfl
  
  def without.ltStd (s: Set3 D) (d: D) (dInS: d ∈ s.posMem):
    s.without d < s
  :=
    And.intro
      (And.intro (fun _ dIn => dIn.left) (fun _ dIn => dIn.left))
      (fun eq =>
        let dNinSWithout: d ∉ (s.without d).posMem := Set3.without.ninPos _ _
        let dNinS: d ∉ s.posMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  
  def withoutDef (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => dd ∈ s.defMem ∧ dd ≠ d
    posMem := fun dd => dd ∈ s.posMem
    defLePos := fun d dDef => (s.defLePos d dDef.left)
  }
  
  def withoutDef.ninDef (s: Set3 D) (d: D): d ∉ (s.withoutDef d).defMem :=
    fun dIn => dIn.right rfl
  
  def withoutDef.ltStd (s: Set3 D) (d: D) (dInS: d ∈ s.defMem):
    s.withoutDef d < s
  :=
    And.intro
      (And.intro (fun _dd ddIn => ddIn.left) (fun _dd ddIn => ddIn))
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem := Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  def withoutDef.ltApx (s: Set3 D) (d: D) (dInS: d ∈ s.defMem):
    s.withoutDef d ⊏ s
  :=
    And.intro
      (And.intro (fun _dd ddIn => ddIn.left) (fun _dd ddIn => ddIn))
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem := Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  
  def _root_.Set3.with (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => dd ∈ s.defMem ∨ dd = d
    posMem := fun dd => dd ∈ s.posMem ∨ dd = d
    defLePos :=
      fun dd ddDef =>
        ddDef.elim
          (fun ddInS => Or.inl (s.defLePos dd ddInS))
          (fun eq => Or.inr eq)
  }
  
  def with.inPos (s: Set3 D) (d: D): d ∈ (s.with d).posMem :=
    Or.inr rfl
  
  def with.inDef (s: Set3 D) (d: D): d ∈ (s.with d).defMem :=
    Or.inr rfl
  
  def with.gtStd (s: Set3 D) (d: D) (dNinS: d ∉ s.posMem):
    s < s.with d
  :=
    And.intro
      (And.intro (fun _dd ddIn => Or.inl ddIn) (fun _dd ddIn => Or.inl ddIn))
      (fun eq =>
        let dInSWith: d ∈ (s.with d).posMem := Set3.with.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  
  def withPos (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => dd ∈ s.defMem
    posMem := fun dd => dd ∈ s.posMem ∨ dd = d
    defLePos := fun dd ddDef => Or.inl (s.defLePos dd ddDef)
  }
  
  def withPos.defMemEq (s: Set3 D) (d: D):
    s.defMem = (s.withPos d).defMem
  :=
    funext (fun _ => (propext (Iff.intro id id)))
  
  def withPos.inPos (s: Set3 D) (d: D): d ∈ (s.withPos d).posMem :=
    Or.inr rfl
  
  def withPos.gtStd (s: Set3 D) (d: D) (dNinS: d ∉ s.posMem):
    s < s.withPos d
  :=
    And.intro
      (And.intro (fun _dd ddIn => ddIn) (fun _dd ddIn => Or.inl ddIn))
      (fun eq =>
        let dInSWith: d ∈ (s.withPos d).posMem := Set3.withPos.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  def withPos.ltApx (s: Set3 D) (d: D) (dNinS: d ∉ s.posMem):
     s.withPos d ⊏ s
  :=
    And.intro
      (And.intro (fun _dd ddIn => ddIn) (fun _dd ddIn => Or.inl ddIn))
      (fun eq =>
        let dInSWith: d ∈ (s.withPos d).posMem := Set3.withPos.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  
  def ord.standard.inChain.inSup.defMem
    (ch: Chain (standard D))
    (s: ↑ch.val)
    (d: D)
    (dInSDef: d ∈ s.val.defMem)
  :
    d ∈ (ch.sup (standard D) cc).val.defMem
  :=
    let sup := ch.sup (standard D) cc
    let supGeS := sup.property.left s
    
    supGeS.left d dInSDef
  
  def ord.standard.inChain.inSup.posMem
    (ch: Chain (standard D))
    (s: ↑ch.val)
    (d: D)
    (dInSDef: d ∈ s.val.posMem)
  :
    d ∈ (ch.sup (standard D) cc).val.posMem
  :=
    let sup := ch.sup (standard D) cc
    let supGeS := sup.property.left s
    
    supGeS.right d dInSDef
  
  
  def ord.standard.ninChain.ninSup.defMem
    (ch: Chain (standard D))
    (d: D)
    (allNin: ∀ (s: ↑ch.val), d ∉ s.val.defMem)
  :
    d ∉ (ch.sup (standard D) cc).val.defMem
  :=
    let sup := ch.sup (standard D) cc
    let supWithoutD := sup.val.withoutDef d;
    
    let withoutLe: supWithoutD ≤ sup.val :=
      if h: d ∈ sup.val.defMem then
        (Set3.withoutDef.ltStd sup.val d h).left
      else
        let eq: sup.val = supWithoutD :=
          Set3.eq
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => And.intro ddIn (fun eq => h (eq ▸ ddIn)))
              (fun ddIn => ddIn.left)))))
            rfl
        eq ▸ ((standard D).refl sup.val)
    
    let isUB: supWithoutD ∈ isUpperBound (standard D) ch.val :=
      fun s =>
        And.intro
          (fun dd ddInS =>
            let dInSup := (sup.property.left s).left dd ddInS
            let dNinS := allNin s
            And.intro dInSup (fun eq => dNinS (eq ▸ ddInS)))
          (fun dd ddInS => (sup.property.left s).right dd ddInS)
    
    let withoutGe: sup.val ≤ supWithoutD := sup.property.right supWithoutD isUB
    let eq: sup.val = supWithoutD :=
      PartialOrder.antisymm sup.val supWithoutD withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.right rfl)
  

  def ord.standard.ninChain.ninSup.posMem
    (ch: Chain (standard D))
    (d: D)
    (allNin: ∀ (s: ↑ch.val), d ∉ s.val.posMem)
  :
    d ∉ (ch.sup (standard D) cc).val.posMem
  :=
    let sup := ch.sup (standard D) cc
    let supWithoutD := sup.val.without d;
    
    let withoutLe: supWithoutD ≤ sup.val :=
      if h: d ∈ sup.val.posMem then
        (Set3.without.ltStd sup.val d h).left
      else
        let eq: sup.val = supWithoutD :=
          Set3.eq
            (funext (fun dd => (propext (Iff.intro
              (fun ddIn => And.intro
                ddIn (fun eq => h (eq ▸ (sup.val.defLePos dd ddIn))))
              (fun ddIn => ddIn.left)))))
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => And.intro
                ddIn (fun eq => h (eq ▸ ddIn)))
              (fun ddIn => ddIn.left)))))
        eq ▸ ((standard D).refl sup.val)
    
    let isUB: supWithoutD ∈ isUpperBound (standard D) ch.val :=
      fun s =>
        And.intro
          (fun dd ddInS =>
            let dInSup := (sup.property.left s).left dd ddInS
            let dNinS := allNin s
            And.intro dInSup (fun eq => dNinS (eq ▸ (s.val.defLePos dd ddInS))))
          (fun dd ddInS =>
            let ddInSup := (sup.property.left s).right dd ddInS
            let dNinS := allNin s
            And.intro ddInSup (fun eq => dNinS (eq ▸ ddInS)))
    
    let withoutGe: sup.val ≤ supWithoutD := sup.property.right supWithoutD isUB
    let eq: sup.val = supWithoutD :=
      (standard D).antisymm sup.val supWithoutD withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.right rfl)
  
  
  def ord.standard.inSup.inChain.defMem.ex
    (ch: Chain (standard D))
    (d: D)
    (dIn: d ∈ (ch.sup
      (standard D) (standard.isChainComplete D)).val.defMem)
  :
    ∃ s: ↑ch.val, d ∈ s.val.defMem
  :=
    byContradiction fun notEx =>
      let allNin: ∀ s: ↑ch.val, d ∉ s.val.defMem :=
        fun s =>
          if h: d ∈ s.val.defMem then
            False.elim (notEx ⟨s, h⟩)
          else
            h
      
      let ninSup := ord.standard.ninChain.ninSup.defMem ch d allNin
      
      ninSup dIn

  def ord.standard.inSup.inChain.posMem.ex
    (ch: Chain (standard D))
    (d: D)
    (dIn: d ∈ (ch.sup (standard D) cc).val.posMem)
  :
    ∃ s: ↑ch.val, d ∈ s.val.posMem
  :=
    byContradiction fun notEx =>
      let allNin: ∀ s: ↑ch.val, d ∉ s.val.posMem :=
        fun s =>
          if h: d ∈ s.val.posMem then
            False.elim (notEx ⟨s, h⟩)
          else
            h
      
      let ninSup := ord.standard.ninChain.ninSup.posMem ch d allNin
      
      ninSup dIn
  
  
  def ord.approximation.inChain.inSup.defMem
    (ch: Chain (approximation D))
    (s: ↑ch.val)
    (d: D)
    (dInSDef: d ∈ s.val.defMem)
  :
    d ∈ (ch.sup (approximation D) cc).val.defMem
  :=
    let sup := ch.sup (approximation D) cc
    let supGeS := sup.property.left s
    
    supGeS.left d dInSDef
  
  def ord.approximation.inChain.inSup.posMem
    (ch: Chain (approximation D))
    (d: D)
    (allIn: ∀ s: ↑ch.val, d ∈ s.val.posMem)
  :
    d ∈ (ch.sup (approximation D) cc).val.posMem
  :=
    let sup := ch.sup (approximation D) cc
    let supWithPosD := sup.val.withPos d;
    
    let withoutLe: supWithPosD ⊑ sup.val :=
      if h: d ∈ sup.val.posMem then
        let eq: sup.val = supWithPosD :=
          Set3.eq
            (Set3.withPos.defMemEq sup.val d)
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => Or.inl ddIn)
              (fun ddIn => ddIn.elim id (fun eq => eq ▸ h))))))
        eq ▸ ((standard D).refl sup.val)
      else
        (Set3.withPos.ltApx sup.val d h).left
    
    let isUB: supWithPosD ∈ isUpperBound (approximation D) ch.val :=
      fun s =>
        And.intro
          (fun dd ddInS => (sup.property.left s).left dd ddInS)
          (fun dd ddInSupPos => ddInSupPos.elim
            (fun ddInSup => (sup.property.left s).right dd ddInSup)
            (fun eq => eq ▸ allIn s))
    
    let withoutGe: sup.val ⊑ supWithPosD := sup.property.right supWithPosD isUB
    let eq: sup.val = supWithPosD :=
      (approximation D).antisymm sup.val supWithPosD withoutGe withoutLe
    
    eq ▸ (Or.inr rfl)
  
  
  def ord.approximation.ninChain.ninSup.defMem
    (ch: Chain (approximation D))
    (d: D)
    (allNin: ∀ (s: ↑ch.val), d ∉ s.val.defMem)
  :
    d ∉ (ch.sup (approximation D) cc).val.defMem
  :=
    let sup := ch.sup (approximation D) cc
    let supWithoutD := sup.val.withoutDef d;
    
    let withoutLe: supWithoutD ⊑ sup.val :=
      if h: d ∈ sup.val.defMem then
        (Set3.withoutDef.ltApx sup.val d h).left
      else
        let eq: sup.val = supWithoutD :=
          Set3.eq
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => And.intro ddIn (fun eq => h (eq ▸ ddIn)))
              (fun ddIn => ddIn.left)))))
            rfl
        eq ▸ ((approximation D).refl sup.val)
    
    let isUB: supWithoutD ∈ isUpperBound (approximation D) ch.val :=
      fun s =>
        And.intro
          (fun dd ddInS =>
            let dInSup := (sup.property.left s).left dd ddInS
            let dNinS := allNin s
            And.intro dInSup (fun eq => dNinS (eq ▸ ddInS)))
          (fun dd ddInS => (sup.property.left s).right dd ddInS)
    
    let withoutGe: sup.val ⊑ supWithoutD := sup.property.right supWithoutD isUB
    let eq: sup.val = supWithoutD :=
      PartialOrder.antisymm sup.val supWithoutD withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.right rfl)
  
  def ord.approximation.ninChain.ninSup.posMem
    (ch: Chain (approximation D))
    (s: ↑ch.val)
    (d: D)
    (dNin: d ∉ s.val.posMem)
  :
    d ∉ (ch.sup (approximation D) cc).val.posMem
  :=
    let sup := ch.sup (approximation D) cc
    let supGeS := sup.property.left s
    
    contra (supGeS.right d) dNin
  
end Set3
