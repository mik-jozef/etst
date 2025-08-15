/-
  Contains stuff related to `Set3`.
-/

import old.WFC.Ch0_Set3


namespace Set3
  def pos_eq
    {s0 s1: Set3 D}
    (eq: s0 = s1)
  :
    s0.posMem = s1.posMem
  :=
    congr rfl eq
  
  def def_eq
    {s0 s1: Set3 D}
    (eq: s0 = s1)
  :
    s0.defMem = s1.defMem
  :=
    congr rfl eq
  
  
  def just.inDefToEq
    {a b: D}
    (aIn: a ∈ (just b).defMem)
  :
    a = b
  :=
    aIn
  
  def just.inDefToEqBin
    {a b: D}
    (d: D)
    (aIn: a ∈ (just d).defMem)
    (bIn: b ∈ (just d).defMem)
  :
    a = b
  :=
    aIn.trans bIn.symm
  
  def just.inPosToEq
    {a b: D}
    (aIn: a ∈ (just b).posMem)
  :
    a = b
  :=
    aIn
  
  def just.inPosToEqBin
    {a b: D}
    (d: D)
    (aIn: a ∈ (just d).posMem)
    (bIn: b ∈ (just d).posMem)
  :
    a = b
  :=
    aIn.trans bIn.symm
  
  
  def empty.nin.def (d: D): d ∉ Set3.empty.defMem := False.elim
  def empty.nin.pos (d: D): d ∉ Set3.empty.posMem := False.elim
  
  -- :( def empty.fromNoPos (noPos (d: D): d ∉ s.posMem): ...
  def empty.fromNoPos (noPos: ∀ d: D, d ∉ s.posMem): s = Set3.empty :=
    Set3.eq
      (funext fun d =>
        propext
          (Iff.intro
            (fun dInSDef => noPos d dInSDef.toPos)
            (fun nope => False.elim nope)))
      (funext fun d =>
        propext
          (Iff.intro
            (fun dInSPos => noPos d dInSPos)
            (fun nope => False.elim nope)))
  
  def union (s0 s1: Set3 D): Set3 D := ⟨
    s0.defMem ∪ s1.defMem,
    s0.posMem ∪ s1.posMem,
    fun _d dIn =>
      dIn.elim
        (fun dIn0 => Or.inl dIn0.toPos)
        (fun dIn1 => Or.inr dIn1.toPos)
  ⟩
  
  def memUnion (s0 s1: Set3 D) (d: D):
    d ∈ (union s0 s1).defMem ↔ d ∈ s0.defMem ∨ d ∈ s1.defMem
  :=
    Iff.intro id id
  
  def union.monoLeft (s0 s1: Set3 D):
    s0 ≤ union s0 s1
  :=
    LeStd.intro
      Set.subset_union_left
      Set.subset_union_left
  
  def union.monoRite (s0 s1: Set3 D):
    s1 ≤ union s0 s1
  :=
    LeStd.intro
      Set.subset_union_right
      Set.subset_union_right
  
  
  def inter (s0 s1: Set3 D): Set3 D := ⟨
    s0.defMem ∩ s1.defMem,
    s0.posMem ∩ s1.posMem,
    fun _d dIn => And.intro dIn.left.toPos dIn.right.toPos
  ⟩
  
  def memInter (s0 s1: Set3 D) (d: D):
    d ∈ (inter s0 s1).defMem ↔ d ∈ s0.defMem ∧ d ∈ s1.defMem
  :=
    Iff.intro id id
  
  def inter.monoLeft (s0 s1: Set3 D):
    inter s0 s1 ≤ s0
  :=
    LeStd.intro
      Set.inter_subset_left
      Set.inter_subset_left
  
  def inter.monoRite (s0 s1: Set3 D):
    inter s0 s1 ≤ s1
  :=
    LeStd.intro
      Set.inter_subset_right
      Set.inter_subset_right
  
  def condSome (s: Set3 D): Set3 D := {
    defMem := fun _ => ∃ d: D, d ∈ s.defMem
    posMem := fun _ => ∃ d: D, d ∈ s.posMem
    defLePos := fun _ ⟨d, dIn⟩ => ⟨d, dIn.toPos⟩
  }
  
  def condFull (s: Set3 D): Set3 D := {
    defMem := fun _ => ∀ d: D, d ∈ s.defMem
    posMem := fun _ => ∀ d: D, d ∈ s.posMem
    defLePos := fun _ dIn d => (dIn d).toPos
  }
  
  def cpl (s: Set3 D): Set3 D := {
    defMem := fun d => d ∉ s.posMem
    posMem := fun d => d ∉ s.defMem
    defLePos := fun _ => notDefOfNotPos
  }
  
  def arbUn (f: D → Set3 D): Set3 D := {
    defMem := fun d => ∃ dd: D, d ∈ (f dd).defMem
    posMem := fun d => ∃ dd: D, d ∈ (f dd).posMem
    defLePos := fun _d ⟨dd, ddIn⟩ => ⟨dd, ddIn.toPos⟩
  }
  
  def arbIr (f: D → Set3 D): Set3 D := {
    defMem := fun d => ∀ dd: D, d ∈ (f dd).defMem
    posMem := fun d => ∀ dd: D, d ∈ (f dd).posMem
    defLePos := fun _d ddIn dd => (ddIn dd).toPos
  }
  
  instance unionInst (D: Type u): Union (Set3 D) where
    union := union
  
  instance interInst (D: Type u): Inter (Set3 D) where
    inter := inter
  
  
  def ninPos.ninDef {s: Set3 D} (dNin: d ∉ s.posMem): d ∉ s.defMem :=
    fun dIn => dNin dIn.toPos
  
  structure without.DefMem
    (s: Set3 D)
    (dWithout d: D)
  : Prop where
  intro ::
    dIn: d ∈ s.defMem
    neq: d ≠ dWithout
  
  structure without.PosMem
    (s: Set3 D)
    (dWithout d: D)
  : Prop where
  intro ::
    dIn: d ∈ s.posMem
    neq: d ≠ dWithout
  
  def without (s: Set3 D) (d: D): Set3 D := {
    defMem := without.DefMem s d
    posMem := without.PosMem s d
    defLePos :=
      fun _dd ddDef => {
        dIn := ddDef.dIn.toPos
        neq := ddDef.neq
      }
  }
  
  def without.ninPos (s: Set3 D) (d: D): d ∉ (s.without d).posMem :=
    fun dIn => dIn.neq rfl
  
  def without.ninDef (s: Set3 D) (d: D): d ∉ (s.without d).defMem :=
    fun dIn => dIn.neq rfl
  
  def without.ltStd {s: Set3 D} (dInS: d ∈ s.posMem):
    (s.without d) < s
  :=
    LtStd.intro
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn.dIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.without d).posMem := Set3.without.ninPos _ _
        let dNinS: d ∉ s.posMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  def without.leStd (s: Set3 D):
    (s.without d) ≤ s
  :=
    LeStd.intro
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos.dIn)
  
  
  def withoutDef (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => without.DefMem s d dd
    posMem := fun dd => dd ∈ s.posMem
    defLePos := fun _d dDef => dDef.dIn.toPos
  }
  
  def withoutDef.ninDef (s: Set3 D) (d: D): d ∉ (s.withoutDef d).defMem :=
    fun dIn => dIn.neq rfl
  
  def withoutDef.preservesPos
    (s: Set3 D)
    {d: D}
    (dInPos: d ∈ s.posMem)
  :
    d ∈ (s.withoutDef d).posMem
  :=
    dInPos
  
  def withoutDef.ltStd {s: Set3 D} (dInS: d ∈ s.defMem):
    s.withoutDef d < s
  :=
    LtStd.intro
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem :=
          Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  def withoutDef.ltApx {s: Set3 D} {d: D} (dInS: d ∈ s.defMem):
    s.withoutDef d ⊏ s
  :=
    LtApx.intro
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem :=
          Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  def withoutDef.leStd (s: Set3 D):
    s.withoutDef d ≤ s
  :=
    LeStd.intro
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos)
  
  def withoutDef.leApx (s: Set3 D):
    s.withoutDef d ⊑ s
  :=
    LeApx.intro
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos)
  
  
  def _root_.Set3.with (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => dd ∈ s.defMem ∨ dd = d
    posMem := fun dd => dd ∈ s.posMem ∨ dd = d
    defLePos :=
      fun _dd ddDef =>
        ddDef.elim
          (fun ddInS => Or.inl ddInS.toPos)
          (fun eq => Or.inr eq)
  }
  
  def with.inPos (s: Set3 D) (d: D): d ∈ (s.with d).posMem :=
    Or.inr rfl
  
  def with.inDef (s: Set3 D) (d: D): d ∈ (s.with d).defMem :=
    Or.inr rfl
  
  def with.gtStd (s: Set3 D) (d: D) (dNinS: d ∉ s.posMem):
    s < s.with d
  :=
    LtStd.intro
        (fun _dd ddIn => Or.inl ddIn)
        (fun _dd ddIn => Or.inl ddIn)
      (fun eq =>
        let dInSWith: d ∈ (s.with d).posMem :=
          Set3.with.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  
  def withPos (s: Set3 D) (d: D): Set3 D := {
    defMem := fun dd => dd ∈ s.defMem
    posMem := fun dd => dd ∈ s.posMem ∨ dd = d
    defLePos := fun _dd ddDef => Or.inl ddDef.toPos
  }
  
  def withPos.defMemEq (s: Set3 D) (d: D):
    s.defMem = (s.withPos d).defMem
  :=
    funext (fun _ => (propext (Iff.intro id id)))
  
  def withPos.inPos (s: Set3 D) (d: D): d ∈ (s.withPos d).posMem :=
    Or.inr rfl
  
  def withPos.gtStd {s: Set3 D} (dNinS: d ∉ s.posMem):
    s < s.withPos d
  :=
    LtStd.intro
      (fun _dd ddIn => ddIn)
      (fun _dd ddIn => Or.inl ddIn)
      (fun eq =>
        let dInSWith: d ∈ (s.withPos d).posMem := Set3.withPos.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  def withPos.ltApx {s: Set3 D} (dNinS: d ∉ s.posMem):
     s.withPos d ⊏ s
  :=
    LtApx.intro
        (fun _dd ddIn => ddIn)
        (fun _dd ddIn => Or.inl ddIn)
      (fun eq =>
        let dInSWith: d ∈ (s.withPos d).posMem := Set3.withPos.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  
  def ord.standard.inSet.inSup.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    (s3: ↑set)
    {d: D}
    (dInSDef: d ∈ s3.val.defMem)
  :
    d ∈ sup.val.defMem
  :=
    let supGeS := sup.property.isMember s3
    
    supGeS.defLe dInSDef
  
  def ord.standard.inSet.inSup.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {s3: ↑set}
    {d: D}
    (dInSDef: d ∈ s3.val.posMem)
  :
    d ∈ sup.val.posMem
  :=
    let supGeS := sup.property.isMember s3
    
    supGeS.posLe dInSDef
  
  
  def ord.standard.allNinSet.ninSup.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {d: D}
    (allNin: ∀ (s: ↑set), d ∉ s.val.defMem)
  :
    d ∉ sup.val.defMem
  :=
    let supWithoutD := sup.val.withoutDef d;
    
    let withoutLe: supWithoutD ≤ sup.val :=
      if h: d ∈ sup.val.defMem then
        (Set3.withoutDef.ltStd h).toLe
      else
        let eq: sup.val = supWithoutD :=
          Set3.eq
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => {
                dIn := ddIn,
                neq := (fun eq => h (eq ▸ ddIn)),
              })
              (fun ddIn => ddIn.dIn)))))
            rfl
        eq ▸ ((standard D).le_refl sup.val)
    
    let isUB: IsUpperBound (standard D) set supWithoutD :=
      fun s =>
        LeStd.intro
          (fun _dd ddInS =>
            let dInSup := (sup.property.isMember s).defLe ddInS
            let dNinS := allNin s
            without.DefMem.intro dInSup (fun eq => dNinS (eq ▸ ddInS)))
          (fun _dd ddInS => (sup.property.isMember s).posLe ddInS)
    
    let withoutGe: sup.val ≤ supWithoutD :=
      sup.property.isLeMember isUB
    let eq: sup.val = supWithoutD :=
      ord.standard.le_antisymm sup.val supWithoutD withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.neq rfl)
  
  def ord.standard.allNinSet.ninSup.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {d: D}
    (allNin: ∀ (s: ↑set), d ∉ s.val.posMem)
  :
    d ∉ sup.val.posMem
  :=
    let supWithoutD := sup.val.without d;
    
    let withoutLe: supWithoutD ≤ sup.val :=
      if h: d ∈ sup.val.posMem then
        (Set3.without.ltStd h).toLe
      else
        let eq: sup.val = supWithoutD :=
          Set3.eq
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => without.DefMem.intro
                ddIn (fun eq => h (eq ▸ ddIn.toPos)))
              (fun ddIn => ddIn.dIn)))))
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => without.PosMem.intro
                ddIn (fun eq => h (eq ▸ ddIn)))
              (fun ddIn => ddIn.dIn)))))
        eq ▸ ((standard D).le_refl sup.val)
    
    let isUB: IsUpperBound (standard D) set supWithoutD :=
      fun s =>
        LeStd.intro
          (fun _dd ddInS =>
            let dInSup := (sup.property.isMember s).defLe ddInS
            let dNinS := allNin s
            without.DefMem.intro
              dInSup
              (fun eq => dNinS (eq ▸ ddInS.toPos)))
          (fun _dd ddInS =>
            let ddInSup := (sup.property.isMember s).posLe ddInS
            let dNinS := allNin s
            without.PosMem.intro
              ddInSup
              (fun eq => dNinS (eq ▸ ddInS)))
    
    let withoutGe: sup.val ≤ supWithoutD :=
      sup.property.isLeMember isUB
    
    let eq: sup.val = supWithoutD :=
      (standard D).le_antisymm sup.val supWithoutD withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.neq rfl)
  
  
  def ord.standard.inSup.inSomeSet.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {d: D}
    (dIn: d ∈ sup.val.defMem)
  :
    ∃ s: ↑set, d ∈ s.val.defMem
  :=
    byContradiction fun notEx =>
      let allNin: ∀ s: ↑set, d ∉ s.val.defMem :=
        fun s =>
          if h: d ∈ s.val.defMem then
            False.elim (notEx ⟨s, h⟩)
          else
            h
      
      ord.standard.allNinSet.ninSup.defMem sup allNin dIn

  def ord.standard.inSup.inSomeSet.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {d: D}
    (dIn: d ∈ sup.val.posMem)
  :
    ∃ s: ↑set, d ∈ s.val.posMem
  :=
    byContradiction fun notEx =>
      let allNin: ∀ s: ↑set, d ∉ s.val.posMem :=
        fun s =>
          if h: d ∈ s.val.posMem then
            False.elim (notEx ⟨s, h⟩)
          else
            h
      
      ord.standard.allNinSet.ninSup.posMem sup allNin dIn
  
  
  def ord.standard.ninSup.allNinSet.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {d: D}
    (dNin: d ∉ sup.val.defMem)
  :
    ∀ s: ↑set, d ∉ s.val.defMem
  :=
    fun s dIn =>
      dNin (ord.standard.inSet.inSup.defMem sup s dIn)
  
  def ord.standard.ninSup.allNinSet.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (standard D) set)
    {d: D}
    (dNin: d ∉ sup.val.posMem)
  :
    ∀ s: ↑set, d ∉ s.val.posMem
  :=
    fun _ dIn =>
      dNin (ord.standard.inSet.inSup.posMem sup dIn)
  
  
  def ord.approximation.inSet.inSup.defMem
    {set: Set (Set3 D)}
    (s: ↑set)
    {d: D}
    (dInSDef: d ∈ s.val.defMem)
    (sup: Supremum (approximation D) set)
  :
    d ∈ sup.val.defMem
  :=
    let supGeS := sup.property.isMember s
    
    supGeS.defLe dInSDef
  
  def ord.approximation.allInSet.inSup.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (approximation D) set)
    {d: D}
    (allIn: ∀ s: ↑set, d ∈ s.val.posMem)
  :
    d ∈ sup.val.posMem
  :=
    let supWithPosD := sup.val.withPos d;
    
    let withoutLe: supWithPosD ⊑ sup.val :=
      if h: d ∈ sup.val.posMem then
        let eq: sup.val = supWithPosD :=
          Set3.eq
            (Set3.withPos.defMemEq sup.val d)
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => Or.inl ddIn)
              (fun ddIn => ddIn.elim id (fun eq => eq ▸ h))))))
        eq ▸ ((approximation D).le_refl sup.val)
      else
        (Set3.withPos.ltApx h).toLe
    
    let isUB: IsUpperBound (approximation D) set supWithPosD :=
      fun s =>
        LeApx.intro
          (fun _dd ddInS => (sup.property.isMember s).defLe ddInS)
          (fun _dd ddInSupPos => ddInSupPos.elim
            (fun ddInSup => (sup.property.isMember s).posLe ddInSup)
            (fun eq => eq ▸ allIn s))
    
    let withoutGe: sup.val ⊑ supWithPosD :=
      sup.property.isLeMember isUB
    
    let eq: sup.val = supWithPosD :=
      (approximation D).le_antisymm sup.val supWithPosD withoutGe withoutLe
    
    eq ▸ (Or.inr rfl)
  
  
  def ord.approximation.allNinSet.ninSup.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (approximation D) set)
    {d: D}
    (allNin: ∀ (s: ↑set), d ∉ s.val.defMem)
  :
    d ∉ sup.val.defMem
  :=
    let supWithoutD := sup.val.withoutDef d;
    
    let withoutLe: supWithoutD ⊑ sup.val :=
      if h: d ∈ sup.val.defMem then
        (Set3.withoutDef.ltApx h).toLe
      else
        let eq: sup.val = supWithoutD :=
          Set3.eq
            (funext (fun _dd => (propext (Iff.intro
              (fun ddIn => without.DefMem.intro
                ddIn
                (fun eq => h (eq ▸ ddIn)))
              (fun ddIn => ddIn.dIn)))))
            rfl
        eq ▸ ((approximation D).le_refl sup.val)
    
    let isUB: IsUpperBound (approximation D) set supWithoutD :=
      fun s =>
        LeApx.intro
          (fun _dd ddInS =>
            let dInSup := (sup.property.isMember s).defLe ddInS
            let dNinS := allNin s
            without.DefMem.intro dInSup (fun eq => dNinS (eq ▸ ddInS)))
          (fun _dd ddInS => (sup.property.isMember s).posLe ddInS)
    
    let withoutGe: sup.val ⊑ supWithoutD :=
      sup.property.isLeMember isUB
    
    let eq: sup.val = supWithoutD :=
      @PartialOrder.le_antisymm _ (ord.approximation D)
        _ _ withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.neq rfl)
  
  def ord.approximation.ninSet.ninSup.posMem
    {set: Set (Set3 D)}
    (s: ↑set)
    {d: D}
    (dNin: d ∉ s.val.posMem)
    (sup: Supremum (approximation D) set)
  :
    d ∉ sup.val.posMem
  :=
    let supGeS := sup.property.isMember s
    
    let dSupS: (d: D) → d ∈ sup.val.posMem → d ∈ s.val.posMem := supGeS.posLe
    
    Function.contra (dSupS d) dNin
  
  
  def ord.approximation.inSup.inSomeSet.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (approximation D) set)
    {d: D}
    (dIn: d ∈ sup.val.defMem)
  :
    ∃ s: ↑set, d ∈ s.val.defMem
  :=
    byContradiction fun notEx =>
      let allNin: ∀ s: ↑set, d ∉ s.val.defMem :=
        fun s =>
          if h: d ∈ s.val.defMem then
            False.elim (notEx ⟨s, h⟩)
          else
            h
      
      ord.approximation.allNinSet.ninSup.defMem sup allNin dIn
  
  def ord.approximation.inSup.allInSet.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (approximation D) set)
    {d: D}
    (dIn: d ∈ sup.val.posMem)
  :
    ∀ s: ↑set, d ∈ s.val.posMem
  :=
    fun s =>
      let supGeS := sup.property.isMember s
      
      supGeS.posLe dIn
  
  def ord.approximation.ninSup.allNinSet.defMem
    {set: Set (Set3 D)}
    (sup: Supremum (approximation D) set)
    {d: D}
    (dNin: d ∉ sup.val.defMem)
  :
    ∀ s: ↑set, d ∉ s.val.defMem
  :=
    fun s dIn =>
      dNin (ord.approximation.inSet.inSup.defMem s dIn sup)
  
  def ord.approximation.ninSup.ninSomeSet.posMem
    {set: Set (Set3 D)}
    (sup: Supremum (approximation D) set)
    {d: D}
    (dNin: d ∉ sup.val.posMem)
  :
    ∃ s: ↑set, d ∉ s.val.posMem
  :=
    byContradiction fun notEx =>
      let allIn: ∀ s: ↑set, d ∈ s.val.posMem :=
        fun s =>
          if h: d ∈ s.val.posMem then
            h
          else
            False.elim (notEx ⟨s, h⟩)
      
      dNin (ord.approximation.allInSet.inSup.posMem sup allIn)
  
  def eqJust
    {d: D}
    (allEq: ∀ dPos ∈ s.posMem, dPos = d)
    (nonEmpty: dEx ∈ s.defMem)
  :
    s = just d
  :=
    let dEq := allEq _ nonEmpty.toPos
    
    Set3.eq
      (funext fun _ =>
        propext
          (Iff.intro
            (fun isDef => allEq _ isDef.toPos)
            (fun eq => dEq.trans eq.symm ▸ nonEmpty)))
      (funext fun _ =>
        propext
          (Iff.intro
            (allEq _)
            (fun eq => dEq.trans eq.symm ▸ nonEmpty.toPos)))
  
end Set3
