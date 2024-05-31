import Utils.BasicUtils
import Lfp


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
  
  structure eq2
    (s3: Set3 D)
    (s2: Set D): Prop
  where
    allDefIn: ∀ d: s3.defMem, d.val ∈ s2
    allNinNpos: ∀ d: ↑s2ᶜ, d.val ∉ s3.posMem
  
  
  def empty {D: Type}: Set3 D :=
    ⟨Set.empty, Set.empty, Preorder.le_refl _⟩
  
  def undetermined {D: Type}: Set3 D :=
    ⟨Set.empty, Set.full, fun _ => False.elim⟩
  
  def full {D: Type}: Set3 D :=
    ⟨Set.full, Set.full, Preorder.le_refl _⟩
  
  def just {D: Type} (d: D): Set3 D :=
    ⟨Set.just d, Set.just d, Preorder.le_refl _⟩
  
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
            (fun dInSDef =>
              let dInSPos := s.defLePos dInSDef
              noPos d dInSPos)
            (fun nope => False.elim nope)))
      (funext fun d =>
        propext
          (Iff.intro
            (fun dInSPos => noPos d dInSPos)
            (fun nope => False.elim nope)))
  
  
  structure LeStd (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
  
  structure LtStd (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
    neq: a ≠ b
  
  structure LeApx (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: b.posMem ≤ a.posMem
  
  structure LtApx (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: b.posMem ≤ a.posMem
    neq: a ≠ b
  
  def LtStd.toLe (lt: LtStd a b): LeStd a b := {
    defLe := lt.defLe
    posLe := lt.posLe
  }
  
  def LtApx.toLe (lt: LtApx a b): LeApx a b := {
    defLe := lt.defLe
    posLe := lt.posLe
  }
  
  instance leInst: LE (Set3 D) where
    le := LeStd
  
  instance sqleInst: SqLE (Set3 D) where
    le := LeApx
  
  instance sqltInst: SqLT (Set3 D) where
    lt := LtApx
  
  
  def ord.approximation.le_antisymm
    (a b: Set3 D)
    (ab: a ⊑ b)
    (ba: b ⊑ a)
  :=
      let defEq: a.defMem = b.defMem :=
        PartialOrder.le_antisymm a.defMem b.defMem ab.defLe ba.defLe;
      let posEq: a.posMem = b.posMem :=
        PartialOrder.le_antisymm a.posMem b.posMem ba.posLe ab.posLe;
      Set3.eq defEq posEq
  
  -- Latter instances override former instances in priority.
  -- How may I set the prio manually? `@[default_instance] x`
  -- does not work
  instance ord.approximation (D: Type u): PartialOrder (Set3 D) where
    le := LeApx
    lt := LtApx
    
    le_refl (a: Set3 D) :=
      LeApx.intro
        (Preorder.le_refl (a.defMem))
        (Preorder.le_refl (a.posMem))
    
    le_antisymm := approximation.le_antisymm
    
    le_trans (a b c: Set3 D) (ab: a ⊑ b) (bc: b ⊑ c) :=
      LeApx.intro
        (Preorder.le_trans _ _ _ ab.defLe bc.defLe)
        (Preorder.le_trans _ _ _ bc.posLe ab.posLe)
    
    lt_iff_le_not_le a b: a ⊏ b ↔ a ⊑ b ∧ ¬b ⊑ a :=
      Iff.intro
        (fun ab => And.intro
          ab.toLe
          fun ba =>
            let abEq: a = b :=
              approximation.le_antisymm _ _ ab.toLe ba
            ab.neq abEq)
        fun ⟨ab, nba⟩ =>
          if h: a = b then
            False.elim (nba (h ▸ ab))
          else
            ⟨ab.defLe, ab.posLe, h⟩
  
  
  def ord.standard.le_antisymm (a b: Set3 D) (ab: a ≤ b) (ba: b ≤ a) :=
    let defEq: a.defMem = b.defMem :=
      PartialOrder.le_antisymm a.defMem b.defMem ab.defLe ba.defLe;
    let posEq: a.posMem = b.posMem :=
      PartialOrder.le_antisymm a.posMem b.posMem ab.posLe ba.posLe;
    Set3.eq defEq posEq
  
  instance ord.standard (D: Type u): PartialOrder (Set3 D) where
    le := LeStd
    lt := LtStd
    
    le_refl (a: Set3 D) :=
      LeStd.intro
        (Preorder.le_refl (a.defMem))
        (Preorder.le_refl (a.posMem))
    
    le_antisymm := standard.le_antisymm
    
    le_trans (a b c: Set3 D) (ab: a ≤ b) (bc: b ≤ c) :=
      LeStd.intro
        (Preorder.le_trans a.defMem b.defMem c.defMem ab.defLe bc.defLe)
        (Preorder.le_trans a.posMem b.posMem c.posMem ab.posLe bc.posLe)
    
    lt_iff_le_not_le a b :=
      Iff.intro
        (fun ab => ⟨ab.toLe, fun ba =>
          let eq := standard.le_antisymm _ _ ab.toLe ba
          ab.neq eq⟩)
        fun ⟨ab, nba⟩ =>
          if h: a = b then
            False.elim (nba (h ▸ ab))
          else
            ⟨ab.defLe, ab.posLe, h⟩
  
  def ord.standard.sup (s: Set (Set3 D)): Supremum (standard D) s :=
    let sup := {
      defMem := fun d => ∃s: ↑s, d ∈ s.val.defMem
      posMem := fun d => ∃s: ↑s, d ∈ s.val.posMem
      defLePos :=
        fun d dDef =>
          let s := dDef.unwrap
          ⟨s, s.val.val.defLePos s.property⟩
    }
    ⟨
      sup,
      {
        isMember :=
          (fun s =>
            LeStd.intro
              -- Why tf is this unfolding required???
              (fun d dMem => by unfold defMem; exact ⟨s, dMem⟩)
              (fun d dMem => by unfold posMem; exact ⟨s, dMem⟩))
        isLeMember :=
          fun ub ubIsUB =>
            LeStd.intro
              (fun d dMemSupWtf =>
                -- WHAT THE ACTUAL FLYING why is `by exact` necessary here???
                let dMemSup: ∃s: ↑s, d ∈ s.val.defMem := by exact dMemSupWtf;
                let s := dMemSup.unwrap
                let sLeUb: s.val.val ≤ ub := ubIsUB s
                let dInS: d ∈ s.val.val.defMem := s.property
                sLeUb.defLe dInS)
              (fun d dMemSupWtf =>
                let dMemSup: ∃s: ↑s, d ∈ s.val.posMem := by exact dMemSupWtf;
                let s := dMemSup.unwrap
                let sLeUb: s.val.val ≤ ub := ubIsUB s
                let dInS: d ∈ s.val.val.posMem := s.property
                sLeUb.posLe dInS)
      }
    ⟩
  
  def ord.approximation.sup (ch: Chain (approximation D)):
    Supremum (approximation D) ch
  :=
    let sup: Set3 D := {
      defMem := fun d => ∃s: ↑ch, d ∈ s.val.defMem
      posMem := fun d => ∀s: ↑ch, d ∈ s.val.posMem
      defLePos :=
        fun d dDef s =>
          let sOfD := dDef.unwrap
          let sSOfDComparable := ch.isChain s.property sOfD.val.property
          
          if h: s.val = sOfD then
            let dPos := sOfD.val.val.defLePos sOfD.property
            h ▸ dPos
          else
            (sSOfDComparable h).elim
              (fun sLe =>
                let dSOfDPos: d ∈ sOfD.val.val.posMem :=
                  sOfD.val.val.defLePos sOfD.property
                sLe.posLe dSOfDPos)
              (fun sGe =>
                let dSDef: d ∈ s.val.defMem :=
                  sGe.defLe sOfD.property
                s.val.defLePos dSDef)
    }
    ⟨
      sup,
      {
        isMember :=
          (fun s =>
            LeApx.intro
              (fun _ dMem => ⟨s, dMem⟩)
              (fun _ dMemSup => dMemSup s)),
        isLeMember :=
          fun ub ubIsUB =>
            LeApx.intro
              (fun d dMemSup =>
                let s := dMemSup.unwrap
                let sLeUb: s.val.val ⊑ ub := ubIsUB s
                let dInS: d ∈ s.val.val.defMem := s.property
                sLeUb.defLe dInS)
              (fun _d dMemUB s =>
                let sLeUb: s.val ⊑ ub := ubIsUB s
                sLeUb.posLe dMemUB),
      }
    ⟩
  
  
  def ord.standard.isChainComplete (D: Type u):
    IsChainComplete (ord.standard D)
  := {
    supExists :=
      fun ch => ⟨(sup ch.set).val, (sup ch.set).property⟩
  }
  
  def ord.approximation.isChainComplete (D: Type u):
    IsChainComplete (ord.approximation D)
  := {
    supExists :=
      fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  
  def ninPos.ninDef {s: Set3 D} (dNin: d ∉ s.posMem): d ∉ s.defMem :=
    fun dIn => dNin (s.defLePos dIn)
  
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
        dIn := (s.defLePos ddDef.dIn)
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
    defLePos := fun _d dDef => (s.defLePos dDef.dIn)
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
          (fun ddInS => Or.inl (s.defLePos ddInS))
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
    defLePos := fun _dd ddDef => Or.inl (s.defLePos ddDef)
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
  
  
  def ord.standard.ninSet.ninSup.defMem
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
      PartialOrder.le_antisymm sup.val supWithoutD withoutGe withoutLe
    
    eq ▸ (fun dIn => dIn.neq rfl)
  

  def ord.standard.ninSet.ninSup.posMem
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
                ddIn (fun eq => h (eq ▸ (sup.val.defLePos ddIn))))
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
              (fun eq => dNinS (eq ▸ (s.val.defLePos ddInS))))
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
      
      ord.standard.ninSet.ninSup.defMem sup allNin dIn

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
      
      ord.standard.ninSet.ninSup.posMem sup allNin dIn
  
  
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
  
  def ord.approximation.inSet.inSup.posMem
    {set: Set (Set3 D)}
    {d: D}
    (allIn: ∀ s: ↑set, d ∈ s.val.posMem)
    (sup: Supremum (approximation D) set)
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
  
  
  def ord.approximation.ninSet.ninSup.defMem
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
  
  
  def union (s0 s1: Set3 D): Set3 D := ⟨
    s0.defMem ∪ s1.defMem,
    s0.posMem ∪ s1.posMem,
    fun _d dIn =>
      dIn.elim
        (fun dIn0 => Or.inl (s0.defLePos dIn0))
        (fun dIn1 => Or.inr (s1.defLePos dIn1))
  ⟩
  
  def memUnion (s0 s1: Set3 D) (d: D):
    d ∈ (union s0 s1).defMem ↔ d ∈ s0.defMem ∨ d ∈ s1.defMem
  :=
    Iff.intro id id
  
  def union.monoLeft (s0 s1: Set3 D):
    s0 ≤ union s0 s1
  :=
    LeStd.intro
      (Set.subset_union_left _ _)
      (Set.subset_union_left _ _)
  
  def union.monoRite (s0 s1: Set3 D):
    s1 ≤ union s0 s1
  :=
    LeStd.intro
      (Set.subset_union_right _ _)
      (Set.subset_union_right _ _)
  
  
  def inter (s0 s1: Set3 D): Set3 D := ⟨
    s0.defMem ∩ s1.defMem,
    s0.posMem ∩ s1.posMem,
    fun _d dIn =>
      And.intro
        (s0.defLePos dIn.left)
        (s1.defLePos dIn.right)
  ⟩
  
  def memInter (s0 s1: Set3 D) (d: D):
    d ∈ (inter s0 s1).defMem ↔ d ∈ s0.defMem ∧ d ∈ s1.defMem
  :=
    Iff.intro id id
  
  def inter.monoLeft (s0 s1: Set3 D):
    inter s0 s1 ≤ s0
  :=
    LeStd.intro
      (Set.inter_subset_left _ _)
      (Set.inter_subset_left _ _)
  
  def inter.monoRite (s0 s1: Set3 D):
    inter s0 s1 ≤ s1
  :=
    LeStd.intro
      (Set.inter_subset_right _ _)
      (Set.inter_subset_right _ _)
  
  
  instance unionInst (D: Type u): Union (Set3 D) where
    union := union
  
  instance interInst (D: Type u): Inter (Set3 D) where
    inter := inter
  
end Set3
