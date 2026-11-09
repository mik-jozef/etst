module
public import Etst.WFC.Utils.General.PointwiseOrder
public import Etst.WFC.Ch0_Set3

import Mathlib.Order.CompleteLattice.Defs


public section
namespace Etst

universe u


namespace Set3
  theorem pos_eq
    {D} {s0 s1: Set3 D}
    (eq: s0 = s1)
  :
    s0.posMem = s1.posMem
  :=
    congr rfl eq
  
  theorem def_eq
    {D} {s0 s1: Set3 D}
    (eq: s0 = s1)
  :
    s0.defMem = s1.defMem
  :=
    congr rfl eq
  
  theorem eq4
    {D} {a b: Set3 D}
    (abDef: ∀ d ∈ a.defMem, d ∈ b.defMem)
    (baDef: ∀ d ∈ b.defMem, d ∈ a.defMem)
    (abPos: ∀ d ∈ a.posMem, d ∈ b.posMem)
    (baPos: ∀ d ∈ b.posMem, d ∈ a.posMem)
  :
    a = b
  :=
    Set3.eq
      (Set.ext fun x => Iff.intro (abDef x) (baDef x))
      (Set.ext fun x => Iff.intro (abPos x) (baPos x))
  
  
  theorem just.inDefToEq
    {D} {a b: D}
    (aIn: a ∈ (just b).defMem)
  :
    a = b
  :=
    aIn
  
  theorem just.inDefToEqBin
    {D} {a b: D}
    (d: D)
    (aIn: a ∈ (just d).defMem)
    (bIn: b ∈ (just d).defMem)
  :
    a = b
  :=
    aIn.trans bIn.symm
  
  theorem just.inPosToEq
    {D} {a b: D}
    (aIn: a ∈ (just b).posMem)
  :
    a = b
  :=
    aIn
  
  theorem just.inPosToEqBin
    {D} {a b: D}
    (d: D)
    (aIn: a ∈ (just d).posMem)
    (bIn: b ∈ (just d).posMem)
  :
    a = b
  :=
    aIn.trans bIn.symm
  
  
  exposed def IsClassical {D} (s3: Set3 D): Prop :=
    ∀ d, d ∈ s3.posMem → d ∈ s3.defMem
  
  
  theorem empty.nin.def {D} (d: D): d ∉ (Set3.empty (D := D)).defMem := False.elim
  theorem empty.nin.pos {D} (d: D): d ∉ (Set3.empty (D := D)).posMem := False.elim
  
  -- :( def empty.fromNoPos (noPos (d: D): d ∉ s.posMem): ...
  theorem empty.fromNoPos {D}
    {s: Set3 D}
    (noPos: ∀ d: D, d ∉ s.posMem)
  :
    s = Set3.empty
  :=
    Set3.eq
      (Set.ext fun d =>
        (Iff.intro
          (fun dInSDef => noPos d (defToPos dInSDef))
          (fun nope => False.elim nope)))
      (Set.ext fun d =>
        (Iff.intro
          (fun dInSPos => noPos d dInSPos)
          (fun nope => False.elim nope)))
  
  exposed def union {D} (s0 s1: Set3 D): Set3 D := ⟨
    s0.defMem ∪ s1.defMem,
    s0.posMem ∪ s1.posMem,
    fun _ => (Or.elim · (Or.inl ∘ defToPos) (Or.inr ∘ defToPos))
  ⟩
  
  theorem memUnion {D} (s0 s1: Set3 D) (d: D):
    d ∈ (union s0 s1).defMem ↔ d ∈ s0.defMem ∨ d ∈ s1.defMem
  :=
    Iff.intro id id
  
  theorem union.monoLeft {D} (s0 s1: Set3 D):
    s0 ≤ union s0 s1
  :=
    LeStd.mk
      Set.subset_union_left
      Set.subset_union_left
  
  theorem union.monoRite {D} (s0 s1: Set3 D):
    s1 ≤ union s0 s1
  :=
    LeStd.mk
      Set.subset_union_right
      Set.subset_union_right
  
  theorem union.union_le
    {D} {s0 s1 s: Set3 D}
    (le0: s0 ≤ s)
    (le1: s1 ≤ s)
  :
    union s0 s1 ≤ s
  := {
    defLe _ dLe :=
      dLe.elim (fun dIn => le0.defLe dIn) (fun dIn => le1.defLe dIn)
    posLe _ dLe :=
      dLe.elim (fun dIn => le0.posLe dIn) (fun dIn => le1.posLe dIn)
  }
  
  
  exposed def inter {D} (s0 s1: Set3 D): Set3 D := ⟨
    s0.defMem ∩ s1.defMem,
    s0.posMem ∩ s1.posMem,
    fun _d dIn => ⟨defToPos dIn.left, defToPos dIn.right⟩
  ⟩
  
  theorem memInter {D} (s0 s1: Set3 D) (d: D):
    d ∈ (inter s0 s1).defMem ↔ d ∈ s0.defMem ∧ d ∈ s1.defMem
  :=
    Iff.intro id id
  
  theorem inter.monoLeft {D} (s0 s1: Set3 D):
    inter s0 s1 ≤ s0
  :=
    LeStd.mk
      Set.inter_subset_left
      Set.inter_subset_left
  
  theorem inter.monoRite {D} (s0 s1: Set3 D):
    inter s0 s1 ≤ s1
  :=
    LeStd.mk
      Set.inter_subset_right
      Set.inter_subset_right
  
  theorem inter.le_inter
    {D} {s0 s1 s: Set3 D}
    (le0: s ≤ s0)
    (le1: s ≤ s1)
  :
    s ≤ inter s0 s1
  := {
    defLe _ dLe := And.intro (le0.defLe dLe) (le1.defLe dLe)
    posLe _ dLe := And.intro (le0.posLe dLe) (le1.posLe dLe)
  }
  
  
  exposed def some {D} (s: Set3 D): Set3 D := {
    defMem := { _any | ∃ d: D, d ∈ s.defMem }
    posMem := { _any | ∃ d: D, d ∈ s.posMem }
    defLePos := fun _ ⟨d, dIn⟩ => ⟨d, defToPos dIn⟩
  }
  
  exposed def full {D} (s: Set3 D): Set3 D := {
    defMem := { _any | ∀ d: D, d ∈ s.defMem }
    posMem := { _any | ∀ d: D, d ∈ s.posMem }
    defLePos _ dIn d := defToPos (dIn d)
  }
  
  exposed def compl {D} (s: Set3 D): Set3 D := {
    defMem := s.posMemᶜ
    posMem := s.defMemᶜ
    defLePos _ := not_def_of_not_pos
  }
  
  exposed def arbUn {D} (f: D → Set3 D): Set3 D := {
    defMem := { d | ∃ dd: D, d ∈ (f dd).defMem }
    posMem := { d | ∃ dd: D, d ∈ (f dd).posMem }
    defLePos := fun _d ⟨dd, ddIn⟩ => ⟨dd, defToPos ddIn⟩
  }
  
  exposed def arbIr {D} (f: D → Set3 D): Set3 D := {
    defMem := { d | ∀ dd: D, d ∈ (f dd).defMem }
    posMem := { d | ∀ dd: D, d ∈ (f dd).posMem }
    defLePos _d ddIn dd := defToPos (ddIn dd)
  }
  
  /- The pointwise image of a triset under a function. -/
  exposed def image {D} (f: D → D) (s: Set3 D): Set3 D where
    defMem := f '' s.defMem
    posMem := f '' s.posMem
    defLePos := fun _ ⟨x, hx, eq⟩ => ⟨x, defToPos hx, eq⟩
  
  
  instance unionInst (D: Type u): Union (Set3 D) where
    union := union
  
  instance interInst (D: Type u): Inter (Set3 D) where
    inter := inter
  
  theorem compl_inj_eq
    {D} {s0 s1: Set3 D}
    (eq: compl s0 = compl s1)
  :
    s0 = s1
  :=
    let defEq: s0.compl.defMem = s1.compl.defMem := congr rfl eq
    let posEq: s0.compl.posMem = s1.compl.posMem := congr rfl eq
    Set3.eq (compl_inj_iff.mp posEq) (compl_inj_iff.mp defEq)
  
  theorem compl_inj_neq {D} {s0 s1: Set3 D} (neq: s0 ≠ s1): compl s0 ≠ compl s1 :=
    compl_inj_eq.mt neq
  
  
  theorem ninPos.ninDef {D d}
    {s: Set3 D}
    (dNin: d ∉ s.posMem)
  :
    d ∉ s.defMem
  :=
    dNin ∘ defToPos
  
  structure without.DefMem
    {D} (s: Set3 D)
    (dWithout d: D)
  : Prop where
  intro ::
    dIn: d ∈ s.defMem
    neq: d ≠ dWithout
  
  structure without.PosMem
    {D} (s: Set3 D)
    (dWithout d: D)
  : Prop where
  intro ::
    dIn: d ∈ s.posMem
    neq: d ≠ dWithout
  
  def without {D} (s: Set3 D) (d: D): Set3 D := {
    defMem := .ofPred (without.DefMem s d)
    posMem := .ofPred (without.PosMem s d)
    defLePos :=
      fun _dd ddDef => {
        dIn := (defToPos ddDef.dIn)
        neq := ddDef.neq
      }
  }
  
  theorem without.ninPos {D}
    (s: Set3 D)
    (d: D)
  :
    d ∉ (s.without d).posMem
  :=
    fun dIn => dIn.neq rfl
  
  theorem without.ninDef {D}
    (s: Set3 D)
    (d: D)
  :
    d ∉ (s.without d).defMem
  :=
    fun dIn => dIn.neq rfl
  
  theorem without.ltStd {D d}
    {s: Set3 D}
    (dInS: d ∈ s.posMem)
  :
    (s.without d) < s
  :=
    LtStd.mk
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn.dIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.without d).posMem := Set3.without.ninPos _ _
        let dNinS: d ∉ s.posMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  theorem without.leStd {D} (s: Set3 D) (d: D):
    (s.without d) ≤ s
  :=
    LeStd.mk
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos.dIn)
  
  
  def withoutDef {D} (s: Set3 D) (d: D): Set3 D := {
    defMem := .ofPred (without.DefMem s d)
    posMem := s.posMem
    defLePos _d dDef := defToPos dDef.dIn
  }
  
  theorem withoutDef.ninDef {D}
    (s: Set3 D)
    (d: D)
  :
    d ∉ (s.withoutDef d).defMem
  :=
    fun dIn => dIn.neq rfl
  
  theorem withoutDef.preservesPos {D}
    (s: Set3 D)
    {d: D}
    (dInPos: d ∈ s.posMem)
  :
    d ∈ (s.withoutDef d).posMem
  :=
    dInPos
  
  theorem withoutDef.ltStd {D} {s: Set3 D} {d} (dInS: d ∈ s.defMem):
    s.withoutDef d < s
  :=
    LtStd.mk
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem :=
          Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  theorem withoutDef.ltApx {D} {s: Set3 D} {d: D} (dInS: d ∈ s.defMem):
    s.withoutDef d ⊏ s
  :=
    LtApx.mk
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem :=
          Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  theorem withoutDef.leStd {D} (s: Set3 D) (d: D):
    s.withoutDef d ≤ s
  :=
    LeStd.mk
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos)
  
  theorem withoutDef.leApx {D} (s: Set3 D) (d: D):
    s.withoutDef d ⊑ s
  :=
    LeApx.mk
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos)
  
  
  exposed def _root_.Etst.Set3.with {D} (s: Set3 D) (d: D): Set3 D := {
    defMem := s.defMem ∪ {d}
    posMem := s.posMem ∪ {d}
    defLePos _ := (Or.elim · (Or.inl ∘ defToPos) Or.inr)
  }
  
  theorem with.inPos {D} (s: Set3 D) (d: D): d ∈ (s.with d).posMem :=
    Or.inr rfl
  
  theorem with.inDef {D} (s: Set3 D) (d: D): d ∈ (s.with d).defMem :=
    Or.inr rfl
  
  theorem with.gtStd {D} (s: Set3 D) (d: D) (dNinS: d ∉ s.posMem):
    s < s.with d
  :=
    LtStd.mk
        (fun _dd ddIn => Or.inl ddIn)
        (fun _dd ddIn => Or.inl ddIn)
      (fun eq =>
        let dInSWith: d ∈ (s.with d).posMem :=
          Set3.with.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  
  exposed def withPos {D} (s: Set3 D) (d: D): Set3 D := {
    defMem := s.defMem
    posMem := s.posMem ∪ {d}
    defLePos _ := Or.inl ∘ defToPos
  }
  
  theorem withPos_defMemEq {D} (s: Set3 D) (d: D):
    s.defMem = (s.withPos d).defMem
  :=
    rfl
  
  theorem withPos_inPos {D}
    (s: Set3 D)
    (d: D)
  :
    d ∈ (s.withPos d).posMem
  :=
    Or.inr rfl
  
  theorem withPos_gtStd {D} {s: Set3 D} {d} (dNinS: d ∉ s.posMem):
    s < s.withPos d
  :=
    LtStd.mk
      (fun _dd ddIn => ddIn)
      (fun _dd ddIn => Or.inl ddIn)
      (fun eq => dNinS (eq ▸ (s.withPos_inPos d)))
  
  theorem withPos.ltApx {D} {s: Set3 D} {d} (dNinS: d ∉ s.posMem):
     s.withPos d ⊏ s
  :=
    LtApx.mk
      (fun _ => id)
      (fun _ => Or.inl)
      (fun eq => dNinS (eq ▸ s.withPos_inPos d))
  
  
  -- The approximation relation is antisymmetric.
  theorem ordApx.le_antisymm
    {D} (a b: Set3 D)
    (ab: a ⊑ b)
    (ba: b ⊑ a)
  :
    a = b
  :=
    let defEq: a.defMem = b.defMem :=
      PartialOrder.le_antisymm a.defMem b.defMem ab.defLe ba.defLe;
    let posEq: a.posMem = b.posMem :=
      PartialOrder.le_antisymm a.posMem b.posMem ba.posLe ab.posLe;
    Set3.eq defEq posEq
  
  -- The definition of the approximation order.
  @[expose, reducible]
  def ordApx (D: Type u): PartialOrder (Set3 D) where
    le := LeApx
    lt := LtApx
    
    -- The reflexivity of the approximation order.
    le_refl _ := { defLe := le_rfl, posLe := le_rfl }
    
    -- The antisymmetry of the approximation order.
    le_antisymm := ordApx.le_antisymm
    
    -- The transitivity of the approximation order.
    le_trans (a b c: Set3 D) (ab: a ⊑ b) (bc: b ⊑ c) := {
      defLe := Preorder.le_trans _ _ _ ab.defLe bc.defLe
      posLe := Preorder.le_trans _ _ _ bc.posLe ab.posLe
    }
    
    -- The compatibility of the `le` and `lt` relations. 
    lt_iff_le_not_ge a b: a ⊏ b ↔ a ⊑ b ∧ ¬b ⊑ a :=
      Iff.intro
        (fun ab => And.intro
          ab.toLe
          fun ba =>
            let abEq: a = b :=
              ordApx.le_antisymm _ _ ab.toLe ba
            ab.neq abEq)
        fun ⟨ab, nba⟩ =>
          if h: a = b then
            False.elim (nba (h ▸ ab))
          else
            ⟨ab.defLe, ab.posLe, h⟩
  
  theorem LeApx.notDefLe
    {D} {a b: Set3 D}
    (ab: LeApx a b)
  :
    b.defMemᶜ ≤ a.defMemᶜ
  :=
    compl_le_compl (defLe ab)
  
  theorem LeApx.notPosLe
    {D} {a b: Set3 D}
    (ab: LeApx a b)
  :
    a.posMemᶜ ≤ b.posMemᶜ
  :=
    compl_le_compl (posLe ab)
  
  theorem LeStd.notDefLe
    {D} {a b: Set3 D}
    (ab: LeStd a b)
  :
    b.defMemᶜ ≤ a.defMemᶜ
  :=
    compl_le_compl (defLe ab)
  
  theorem LeStd.notPosLe
    {D} {a b: Set3 D}
    (ab: LeStd a b)
  :
    b.posMemᶜ ≤ a.posMemᶜ
  :=
    compl_le_compl (posLe ab)
  
  theorem LeStd.compl_le_compl {D}
    {a b: Set3 D}
    (ab: LeStd a b)
  :
    b.compl ≤ a.compl
  :=
    LeStd.mk (LeStd.notPosLe ab) (LeStd.notDefLe ab)
  
  theorem LtStd.compl_lt_compl {D}
    {a b: Set3 D}
    (ab: LtStd a b)
  :
    b.compl < a.compl
  :=
    LtStd.mk
      ab.toLe.notPosLe
      ab.toLe.notDefLe
      (compl_inj_neq ab.neq.symm)
  
  theorem LeStd.memLe
    {D} {a b: Set3 D} {lane}
    (ab: LeStd a b)
  :
    a.getLane lane ≤ b.getLane lane
  :=
    match lane with
    | .defLane => ab.defLe
    | .posLane => ab.posLe
  
  
  -- The standard order is antisymmetric.
  theorem ordStd.le_antisymm {D}
    (a b: Set3 D)
    (ab: a ≤ b)
    (ba: b ≤ a)
  :
    a = b
  :=
    Set3.eq
      (PartialOrder.le_antisymm _ _ ab.defLe ba.defLe)
      (PartialOrder.le_antisymm _ _ ab.posLe ba.posLe)
  
  -- The definition of the standard order.
  @[expose, reducible]
  def ordStd (D: Type u): PartialOrder (Set3 D) where
    le := LeStd
    lt := LtStd
    
    -- The reflexivity of the standard order.
    le_refl _ := { defLe := le_rfl, posLe := le_rfl }
    
    -- The antisymmetry of the standard order.
    le_antisymm := ordStd.le_antisymm
    
    -- The transitivity of the standard order.
    le_trans (a b c: Set3 D) (ab: a ≤ b) (bc: b ≤ c) := {
      defLe := Preorder.le_trans _ _ _ ab.defLe bc.defLe
      posLe := Preorder.le_trans _ _ _ ab.posLe bc.posLe
    }
    
    -- The compatibility of the `le` and `lt` relations.
    lt_iff_le_not_ge a b :=
      Iff.intro
        (fun ab => ⟨ab.toLe, fun ba =>
          let eq := ordStd.le_antisymm _ _ ab.toLe ba
          ab.neq eq⟩)
        fun ⟨ab, nba⟩ =>
          if h: a = b then
            False.elim (nba (h ▸ ab))
          else
            ⟨ab.defLe, ab.posLe, h⟩
  
  /-
    The supremum of a set of trisets wrt. the standard order.
    
    Its definitive members are the union of the definitive
    members of the trisets in the set, and its possible members
    are the union of the possible members.
  -/
  exposed def ordStd.sSup {D} (s: Set (Set3 D)): Set3 D := {
    defMem := { d | ∃ s3 ∈ s, d ∈ s3.defMem }
    posMem := { d | ∃ s3 ∈ s, d ∈ s3.posMem }
    defLePos :=
      fun _ dDef =>
        let ⟨s, ⟨inS, isDef⟩⟩ := dDef
        ⟨s, ⟨inS, defToPos isDef⟩⟩
  }
  
  abbrev ordStd.IsLUB {D} :=
    @_root_.IsLUB (Set3 D) (ordStd D).toLE
  
  theorem ordStd.sSup_isLUB {D}
    (s: Set (Set3 D))
  :
    IsLUB s (sSup s)
  :=
    And.intro
      (fun s3 s3In => {
        defLe _d dMem := ⟨s3, s3In, dMem⟩
        posLe _d dMem := ⟨s3, s3In, dMem⟩
      })
      fun _ub ubIsUB => {
        defLe _ := fun ⟨_, inS3, dMem⟩ => (ubIsUB inS3).defLe dMem
        posLe _ := fun ⟨_, inS3, dMem⟩ => (ubIsUB inS3).posLe dMem
      }
  
  /-
    The supremum of a chain of trisets wrt. the approximation order.
    
    Its definitive members are the union of the definitive members
    of the trisets in the chain, and its possible members are the
    intersection of the possible members.
  -/
  def ordApx.sup
    {D} (s: Set (Set3 D))
    (defLePos:
      ∀ (a: s) (d: a.val.defMem) (b: s), d.val ∈ b.val.posMem)
  :
    Set3 D
  := {
    defMem := { d | ∃ s3: s, d ∈ s3.val.defMem }
    posMem := { d | ∀ s3: s, d ∈ s3.val.posMem }
    defLePos := fun d ⟨a, dIn⟩ => defLePos a ⟨d, dIn⟩
  }
  
  theorem ordApx.sup_defLePos_of_chain
    {D} {ch: Set (Set3 D)}
    (isChain: IsChain (ordApx D).le ch)
    (a: ch)
    (d: a.val.defMem)
    (b: ch)
  :
    d.val ∈ b.val.posMem
  :=
    match isChain.total a.property b.property with
    | Or.inl ab => defToPos (ab.defLe d.property)
    | Or.inr ba => ba.posLe (defToPos d.property)
  
  def ordApx.supOfChain {D} {ch} (isChain: IsChain (ordApx D).le ch):
    Set3 D
  :=
    sup ch (sup_defLePos_of_chain isChain)
  
  abbrev ordApx.IsLUB {D} :=
    @_root_.IsLUB (Set3 D) (ordApx D).toLE
  
  theorem ordApx.sup_isLUB
    {D} (s: Set (Set3 D))
    (defLePos:
      ∀ (a: s) (d: a.val.defMem) (b: s), d.val ∈ b.val.posMem)
  :
    IsLUB s (sup s defLePos)
  :=
    And.intro
      (fun s3 s3In => {
        defLe _ dMem := ⟨⟨s3, s3In⟩, dMem⟩
        posLe _ dMemSup := dMemSup ⟨s3, s3In⟩
      })
      fun _ ubIsUB => {
        defLe :=
          fun _ ⟨s3, dMemSup⟩ => (ubIsUB s3.property).defLe dMemSup
        posLe :=
          fun _ dMemUB s3 => (ubIsUB s3.property).posLe dMemUB
      }
  
  theorem ordApx.lub_is_sup
    {D} {s: Set (Set3 D)} {lub}
    (isLub: IsLUB s lub)
  :
    ∃ defLePos, lub = sup s defLePos
  :=
    let _ := ordApx
    let defLePos := fun a ⟨_d, dDef⟩ b =>
      (isLub.left b.property).posLe
        (defToPos ((isLub.left a.property).defLe dDef))
    ⟨
      defLePos,
      IsLeast.unique isLub (sup_isLUB s defLePos),
    ⟩
  
  theorem ordApx.supOfChain_isLUB
    {D} {ch}
    (isChain: IsChain (ordApx D).le ch)
  :
    IsLUB ch (supOfChain isChain)
  :=
    sup_isLUB ch (sup_defLePos_of_chain isChain)
  
  
  -- The standard order is chain-complete.
  theorem ordStd.isChainComplete (D: Type u):
    IsChainComplete (ordStd D)
  :=
    fun ch _ => ⟨sSup ch, sSup_isLUB ch⟩
  
  -- The approximation order is chain-complete.
  theorem ordApx.isChainComplete (D: Type u):
    IsChainComplete (ordApx D)
  :=
    fun _ isChain => ⟨
      supOfChain isChain,
      supOfChain_isLUB isChain
    ⟩
  
  
  def ordStd.sInf {D} (s: Set (Set3 D)): Set3 D := {
    defMem := { d | ∀ s3: s, d ∈ s3.val.defMem }
    posMem := { d | ∀ s3: s, d ∈ s3.val.posMem }
    defLePos _d dDef s3 := defToPos (dDef s3)
  }
  
  abbrev ordStd.IsGLB {D} :=
    @_root_.IsGLB (Set3 D) (ordStd D).toLE
  
  theorem ordStd.sInf_isGLB {D}
    (s: Set (Set3 D))
  :
    IsGLB s (sInf s)
  :=
    And.intro
      (fun s3 s3In => {
        defLe _d dMem := dMem ⟨s3, s3In⟩
        posLe _d dMem := dMem ⟨s3, s3In⟩
      })
      fun _lb lbIsGLB => {
        defLe _d dMem s3 := (lbIsGLB s3.property).defLe dMem
        posLe _d dMem s3 := (lbIsGLB s3.property).posLe dMem
      }
  
  @[expose, reducible]
  def ordStdLattice (D: Type u): CompleteLattice (Set3 D) := {
    __ := ordStd D
    
    top := Set3.univ
    bot := Set3.empty
    
    le_top _ := LeStd.mk (fun _ _ => trivial) (fun _ _ => trivial)
    bot_le _ := LeStd.mk nofun nofun
    
    sup := union
    le_sup_left := union.monoLeft
    le_sup_right := union.monoRite
    sup_le _ _ _ := union.union_le
    
    sSup := ordStd.sSup
    isLUB_sSup s := ordStd.sSup_isLUB s
    
    inf := inter
    inf_le_left := inter.monoLeft
    inf_le_right := inter.monoRite
    le_inf _ _ _ := inter.le_inter

    sInf := ordStd.sInf
    isGLB_sInf s := ordStd.sInf_isGLB s
  }
  
  
  theorem ordStd.in_set_in_sup_defMem
    {D} {set: Set (Set3 D)} {lub} {d}
    (isLub: IsLUB set lub)
  :
    (∃ s3 ∈ set, d ∈ s3.defMem) ↔ d ∈ lub.defMem
  :=
    let _ := Set3.ordStd D
    Iff.intro
      (fun ⟨_s3, inSet, dIn⟩ =>
        (isLub.left inSet).defLe dIn)
      (fun inLub =>
        let sSup_isLub := Set3.ordStd.sSup_isLUB set
        let ⟨s3, inSet, dIn⟩ :=
          IsLUB.unique isLub sSup_isLub ▸ inLub
        ⟨s3, inSet, dIn⟩)
  
  theorem ordStd.in_set_in_sup_posMem
    {D} {set: Set (Set3 D)} {lub} {d}
    (isLub: IsLUB set lub)
  :
    (∃ s3 ∈ set, d ∈ s3.posMem) ↔ d ∈ lub.posMem
  :=
    let _ := Set3.ordStd D
    Iff.intro
      (fun ⟨_s3, inSet, dIn⟩ =>
        (isLub.left inSet).posLe dIn)
      (fun inLub =>
        let sSup_isLub := Set3.ordStd.sSup_isLUB set
        let ⟨s3, inSet, dIn⟩ :=
          IsLUB.unique isLub sSup_isLub ▸ inLub
        ⟨s3, inSet, dIn⟩)
  
  
  theorem ordApx.in_set_in_sup_defMem
    {D} {set: Set (Set3 D)} {lub} {d}
    (isLub: IsLUB set lub)
  :
    (∃ s3 ∈ set, d ∈ s3.defMem) ↔ d ∈ lub.defMem
  :=
    let _ := Set3.ordApx D
    Iff.intro
      (fun ⟨_s3, inSet, dIn⟩ =>
        (isLub.left inSet).defLe dIn)
      (fun inLub =>
        let ⟨_, eq⟩ := Set3.ordApx.lub_is_sup isLub
        let ⟨⟨s3, inSet⟩, dIn⟩ := eq ▸ inLub
        ⟨s3, inSet, dIn⟩)
  
  theorem ordApx.in_set_in_sup_posMem
    {D} {set: Set (Set3 D)} {lub} {d}
    (isLub: IsLUB set lub)
  :
    (∀ s3 ∈ set, d ∈ s3.posMem) ↔ d ∈ lub.posMem
  :=
    let _ := Set3.ordApx D
    let ⟨_, eq⟩ := Set3.ordApx.lub_is_sup isLub
    eq ▸ Iff.intro
      (fun inAllSets =>
        byContradiction fun ninPosSup =>
          let ⟨s3, ninPos⟩ := ninPosSup.toEx fun _ => id
          ninPos (inAllSets s3 s3.property))
      (fun inLub s3 s3In => inLub ⟨s3, s3In⟩)
  
  
  -- A definite member is a possible member, but not vice versa.
  exposed def Lane.Le: Lane → Lane → Prop
  | .posLane, .defLane => False
  | _, _ => True

  instance (a b: Lane): Decidable (Lane.Le a b) :=
    match a, b with
    | .posLane, .defLane => isFalse id
    | .defLane, _ => isTrue True.intro
    | .posLane, .posLane => isTrue True.intro
  
  theorem Lane.Le.liftMem
    {D} {laneA laneB: Lane} {d: D}
    (le: Lane.Le laneA laneB)
    ⦃s: Set3 D⦄
    (inA: d ∈ s.getLane laneA)
  :
    d ∈ s.getLane laneB
  :=
    match laneA, laneB with
    | .defLane, .defLane => inA
    | .defLane, .posLane => defToPos inA
    | .posLane, .posLane => inA
  
  theorem defMem_toLane {D d lane} {s: Set3 D}
    (isDef: d ∈ s.defMem)
  :
    d ∈ s.getLane lane
  :=
    match lane with
    | .defLane => isDef
    | .posLane => defToPos isDef
  
  theorem getLane_toPos {D d lane} {s: Set3 D}
    (inLane: d ∈ s.getLane lane)
  :
    d ∈ s.posMem
  :=
    match lane with
    | .defLane => defToPos inLane
    | .posLane => inLane
  
  theorem Lane.toggle_toggle:
    (lane: Set3.Lane) → lane.toggle.toggle = lane
  | .posLane => rfl
  | .defLane => rfl
  
  theorem Lane.toggle_eq_iff {lane other: Set3.Lane}:
    lane.toggle = other ↔ lane ≠ other
  := by
    cases lane <;> cases other <;> decide
  
  theorem Lane.toggle_ne_iff {lane other: Set3.Lane}:
    lane.toggle ≠ other ↔ lane = other
  := by
    cases lane <;> cases other <;> decide

end Set3
