import Mathlib.Order.CompleteLattice.Defs

import Etst.WFC.Ch0_Set3

namespace Etst


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
  
  def eq4
    {a b: Set3 D}
    (abDef: ∀ d ∈ a.defMem, b.defMem d)
    (baDef: ∀ d ∈ b.defMem, a.defMem d)
    (abPos: ∀ d ∈ a.posMem, b.posMem d)
    (baPos: ∀ d ∈ b.posMem, a.posMem d)
  :
    a = b
  :=
    Set3.eq
      (Set.ext fun x => Iff.intro (abDef x) (baDef x))
      (Set.ext fun x => Iff.intro (abPos x) (baPos x))
  
  
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
    LeStd.mk
      Set.subset_union_left
      Set.subset_union_left
  
  def union.monoRite (s0 s1: Set3 D):
    s1 ≤ union s0 s1
  :=
    LeStd.mk
      Set.subset_union_right
      Set.subset_union_right
  
  def union.union_le
    {s0 s1 s: Set3 D}
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
    LeStd.mk
      Set.inter_subset_left
      Set.inter_subset_left
  
  def inter.monoRite (s0 s1: Set3 D):
    inter s0 s1 ≤ s1
  :=
    LeStd.mk
      Set.inter_subset_right
      Set.inter_subset_right
  
  def inter.le_inter
    {s0 s1 s: Set3 D}
    (le0: s ≤ s0)
    (le1: s ≤ s1)
  :
    s ≤ inter s0 s1
  := {
    defLe _ dLe := And.intro (le0.defLe dLe) (le1.defLe dLe)
    posLe _ dLe := And.intro (le0.posLe dLe) (le1.posLe dLe)
  }
  
  
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
  
  def compl (s: Set3 D): Set3 D := {
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
  
  def compl_inj_eq
    (eq: compl s0 = compl s1)
  :
    s0 = s1
  :=
    let defEq: s0.compl.defMem = s1.compl.defMem := congr rfl eq
    let posEq: s0.compl.posMem = s1.compl.posMem := congr rfl eq
    Set3.eq (compl_inj_iff.mp posEq) (compl_inj_iff.mp defEq)
  
  def compl_inj_neq (neq: s0 ≠ s1): compl s0 ≠ compl s1 :=
    compl_inj_eq.mt neq
  
  
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
    LtStd.mk
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn.dIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.without d).posMem := Set3.without.ninPos _ _
        let dNinS: d ∉ s.posMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  def without.leStd (s: Set3 D) (d: D):
    (s.without d) ≤ s
  :=
    LeStd.mk
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
    LtStd.mk
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
    LtApx.mk
      (fun _dd ddIn => ddIn.dIn)
      (fun _dd ddIn => ddIn)
      (fun eq =>
        let dNinSWithout: d ∉ (s.withoutDef d).defMem :=
          Set3.withoutDef.ninDef _ _
        let dNinS: d ∉ s.defMem := eq ▸ dNinSWithout
        dNinS dInS)
  
  def withoutDef.leStd (s: Set3 D) (d: D):
    s.withoutDef d ≤ s
  :=
    LeStd.mk
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos)
  
  def withoutDef.leApx (s: Set3 D) (d: D):
    s.withoutDef d ⊑ s
  :=
    LeApx.mk
      (fun _dd ddInDef => ddInDef.dIn)
      (fun _dd ddInPos => ddInPos)
  
  
  def _root_.Etst.Set3.with (s: Set3 D) (d: D): Set3 D := {
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
    LtStd.mk
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
    LtStd.mk
      (fun _dd ddIn => ddIn)
      (fun _dd ddIn => Or.inl ddIn)
      (fun eq =>
        let dInSWith: d ∈ (s.withPos d).posMem := Set3.withPos.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  def withPos.ltApx {s: Set3 D} (dNinS: d ∉ s.posMem):
     s.withPos d ⊏ s
  :=
    LtApx.mk
        (fun _dd ddIn => ddIn)
        (fun _dd ddIn => Or.inl ddIn)
      (fun eq =>
        let dInSWith: d ∈ (s.withPos d).posMem := Set3.withPos.inPos _ _
        let dInS: d ∈ s.posMem := eq ▸ dInSWith
        dNinS dInS)
  
  
  -- The approximation relation is antisymmetric.
  def ordApx.le_antisymm
    (a b: Set3 D)
    (ab: a ⊑ b)
    (ba: b ⊑ a)
  :=
    let defEq: a.defMem = b.defMem :=
      PartialOrder.le_antisymm a.defMem b.defMem ab.defLe ba.defLe;
    let posEq: a.posMem = b.posMem :=
      PartialOrder.le_antisymm a.posMem b.posMem ba.posLe ab.posLe;
    Set3.eq defEq posEq
  
  -- The definition of the approximation order.
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
  
  def LeApx.notDefLe
    (ab: LeApx a b)
  :
    b.defMemᶜ ≤ a.defMemᶜ
  :=
    compl_le_compl (defLe ab)
  
  def LeApx.notPosLe
    (ab: LeApx a b)
  :
    a.posMemᶜ ≤ b.posMemᶜ
  :=
    compl_le_compl (posLe ab)
  
  def LeStd.notDefLe
    (ab: LeStd a b)
  :
    b.defMemᶜ ≤ a.defMemᶜ
  :=
    compl_le_compl (defLe ab)
  
  def LeStd.notPosLe
    (ab: LeStd a b)
  :
    b.posMemᶜ ≤ a.posMemᶜ
  :=
    compl_le_compl (posLe ab)
  
  def LeStd.compl_le_compl (ab: LeStd a b): b.compl ≤ a.compl :=
    LeStd.mk (LeStd.notPosLe ab) (LeStd.notDefLe ab)
  
  def LtStd.compl_lt_compl (ab: LtStd a b): b.compl < a.compl :=
    LtStd.mk ab.toLe.notPosLe ab.toLe.notDefLe (compl_inj_neq ab.neq.symm)
  
  
  -- The standard order is antisymmetric.
  def ordStd.le_antisymm (a b: Set3 D) (ab: a ≤ b) (ba: b ≤ a) :=
    Set3.eq
      (PartialOrder.le_antisymm _ _ ab.defLe ba.defLe)
      (PartialOrder.le_antisymm _ _ ab.posLe ba.posLe)
  
  -- The definition of the standard order.
  def ordStd (D: Type u): PartialOrder (Set3 D) where
    le := LeStd
    lt := LtStd
    
    -- The reflexivity of the standard order.
    le_refl _ := { defLe := le_rfl, posLe := le_rfl }
    
    -- The antisymmetry of the standard order.
    le_antisymm := ordStd.le_antisymm
    
    -- The transitivity of the standard order.
    le_trans (a b c: Set3 D) (ab: a ≤ b) (bc: b ≤ c) := {
      defLe := Preorder.le_trans a.defMem b.defMem c.defMem ab.defLe bc.defLe
      posLe := Preorder.le_trans a.posMem b.posMem c.posMem ab.posLe bc.posLe
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
  def ordStd.sSup (s: Set (Set3 D)): Set3 D := {
    defMem := fun d => ∃s3: ↑s, d ∈ s3.val.defMem
    posMem := fun d => ∃s3: ↑s, d ∈ s3.val.posMem
    defLePos :=
      fun _ dDef =>
        let ⟨s, isDef⟩ := dDef
        ⟨s, isDef.toPos⟩
  }
  
  def ordStd.IsLUB {D} := @_root_.IsLUB (Set3 D) (ordStd D).toLE
  
  def ordStd.sSup_isLUB (s: Set (Set3 D)): IsLUB s (sSup s) :=
    And.intro
      (fun s3 s3In => {
        defLe := fun _d dMem => ⟨⟨s3, s3In⟩, dMem⟩
        posLe := fun _d dMem => ⟨⟨s3, s3In⟩, dMem⟩
      })
      fun _ub ubIsUB => {
        defLe := fun _d ⟨s3, dMem⟩ => (ubIsUB s3.property).defLe dMem
        posLe := fun _d ⟨s3, dMem⟩ => (ubIsUB s3.property).posLe dMem
      }
  
  /-
    The supremum of a chain of trisets wrt. the approximation order.
    
    Its definitive members are the union of the definitive members
    of the trisets in the chain, and its possible members are the
    intersection of the possible members.
  -/
  def ordApx.sup
    (s: Set (Set3 D))
    (defLePos:
      ∀ (a: ↑s) (d: a.val.defMem) (b: ↑s), b.val.posMem d)
  :
    Set3 D
  := {
    defMem := fun d => ∃ s3: s, d ∈ s3.val.defMem
    posMem := fun d => ∀ s3: s, d ∈ s3.val.posMem
    defLePos := fun d ⟨a, dIn⟩ => defLePos a ⟨d, dIn⟩
  }
  
  def ordApx.sup_defLePos_of_chain
    (isChain: IsChain (ordApx D).le ch)
    (a: ↑ch)
    (d: a.val.defMem)
    (b: ↑ch)
  :
    b.val.posMem d
  :=
    match isChain.total a.property b.property with
    | Or.inl ab => (ab.defLe d.property).toPos
    | Or.inr ba => ba.posLe d.property.toPos
  
  def ordApx.supOfChain (isChain: IsChain (ordApx D).le ch):
    Set3 D
  :=
    sup ch (sup_defLePos_of_chain isChain)
  
  def ordApx.IsLUB {D} := @_root_.IsLUB (Set3 D) (ordApx D).toLE
  
  def ordApx.sup_isLUB
    (s: Set (Set3 D))
    (defLePos:
      ∀ (a: ↑s) (d: a.val.defMem) (b: ↑s), b.val.posMem d)
  :
    IsLUB s (sup s defLePos)
  :=
    And.intro
      (fun s3 s3In => {
        defLe := fun _ dMem => ⟨⟨s3, s3In⟩, dMem⟩
        posLe := fun _ dMemSup => dMemSup ⟨s3, s3In⟩
      })
      fun _ ubIsUB => {
        defLe :=
          fun _ ⟨s3, dMemSup⟩ => (ubIsUB s3.property).defLe dMemSup
        posLe :=
          fun _ dMemUB s3 => (ubIsUB s3.property).posLe dMemUB
      }
  
  def ordApx.lub_is_sup
    (isLub: IsLUB s lub)
  :
    ∃ defLePos, lub = sup s defLePos
  :=
    let _ := ordApx
    let defLePos := fun a ⟨_d, dDef⟩ b =>
      (isLub.left b.property).posLe
        ((isLub.left a.property).defLe dDef).toPos
    ⟨
      defLePos,
      IsLeast.unique isLub (sup_isLUB s defLePos),
    ⟩
  
  def ordApx.supOfChain_isLUB
    (isChain: IsChain (ordApx D).le ch)
  :
    IsLUB ch (supOfChain isChain)
  :=
    sup_isLUB ch (sup_defLePos_of_chain isChain)
  
  
  -- The standard order is chain-complete.
  def ordStd.isChainComplete (D: Type u):
    IsChainComplete (ordStd D)
  :=
    fun ch _ => ⟨sSup ch, sSup_isLUB ch⟩
  
  -- The approximation order is chain-complete.
  def ordApx.isChainComplete (D: Type u):
    IsChainComplete (ordApx D)
  :=
    fun _ isChain => ⟨
      supOfChain isChain,
      supOfChain_isLUB isChain
    ⟩
  
  
  def ordStd.sInf (s: Set (Set3 D)): Set3 D := {
    defMem := fun d => ∀ s3: ↑s, d ∈ s3.val.defMem
    posMem := fun d => ∀ s3: ↑s, d ∈ s3.val.posMem
    defLePos := fun _d dDef s3 => (dDef s3).toPos
  }
  
  def ordStd.IsGLB {D} := @_root_.IsGLB (Set3 D) (ordStd D).toLE
  
  def ordStd.sInf_isGLB (s: Set (Set3 D)): IsGLB s (sInf s) :=
    And.intro
      (fun s3 s3In => {
        defLe := fun _d dMem => dMem ⟨s3, s3In⟩
        posLe := fun _d dMem => dMem ⟨s3, s3In⟩
      })
      fun _lb lbIsGLB => {
        defLe := fun _d dMem s3 => (lbIsGLB s3.property).defLe dMem
        posLe := fun _d dMem s3 => (lbIsGLB s3.property).posLe dMem
      }
  
  def ordStdLattice D: CompleteLattice (Set3 D) := {
    __ := ordStd D
    
    top := Set3.full
    bot := Set3.empty
    
    le_top := fun _ => LeStd.mk (fun _ _ => trivial) (fun _ _ => trivial)
    bot_le := fun _ => LeStd.mk nofun nofun
    
    sup := union
    le_sup_left := union.monoLeft
    le_sup_right := union.monoRite
    sup_le := fun _ _ _ => union.union_le
    
    sSup := ordStd.sSup
    le_sSup := fun s _s3 s3In => (ordStd.sSup_isLUB s).left s3In
    sSup_le := fun s _s3 sLe => (ordStd.sSup_isLUB s).right sLe
    
    inf := inter
    inf_le_left := inter.monoLeft
    inf_le_right := inter.monoRite
    le_inf := fun _ _ _ => inter.le_inter

    sInf := ordStd.sInf
    sInf_le := fun s _s3 s3In => (ordStd.sInf_isGLB s).left s3In
    le_sInf := fun s _s3 sLe => (ordStd.sInf_isGLB s).right sLe
  }
  
  
  def ordStd.in_set_in_sup_defMem
    {set: Set (Set3 D)}
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
        let ⟨⟨s3, inSet⟩, dIn⟩ :=
          IsLUB.unique isLub sSup_isLub ▸ inLub
        ⟨s3, inSet, dIn⟩)
  
  def ordStd.in_set_in_sup_posMem
    {set: Set (Set3 D)}
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
        let ⟨⟨s3, inSet⟩, dIn⟩ :=
          IsLUB.unique isLub sSup_isLub ▸ inLub
        ⟨s3, inSet, dIn⟩)
  
  
  def ordApx.in_set_in_sup_defMem
    {set: Set (Set3 D)}
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
  
  def ordApx.in_set_in_sup_posMem
    {set: Set (Set3 D)}
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
  
end Set3
