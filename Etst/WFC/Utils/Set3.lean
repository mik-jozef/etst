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
  
  
  def ordStd.nin_sup_of_nin_any_set_defMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (ninAnySet: ∀ s3 ∈ set, d ∉ s3.defMem)
  :
    d ∉ lub.defMem
  :=
    let _ := ordStd D
    let lubWithout := lub.withoutDef d
    let isLubWithout: IsLUB set lubWithout :=
      And.intro
        (fun s3 s3In => {
          defLe := fun s3D s3DMem =>
            let neq (eq: s3D = d) := ninAnySet s3 s3In (eq ▸ s3DMem)
            ⟨(isLub.left s3In).defLe s3DMem, neq⟩
          posLe := fun _s3D s3DMem => (isLub.left s3In).posLe s3DMem
        })
        (fun _f fIn =>
          (withoutDef.leStd lub d).trans (isLub.right fIn))
    
    isLub.unique isLubWithout ▸
    fun ia => ia.neq rfl
  
  def ordStd.in_sup_of_in_some_set_defMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (inSomeSet: ∃ s3 ∈ set, d ∈ s3.defMem)
  :
    d ∈ lub.defMem
  :=
    let ⟨_s3, inSet, dIn⟩ := inSomeSet
    (isLub.left inSet).defLe dIn

  def ordStd.in_no_set_of_nin_sup_defMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (dNinSup: d ∉ lub.defMem)
  :
    ∀ s3 ∈ set, d ∉ s3.defMem
  :=
    fun s3 s3In dNinS3 =>
      dNinSup <| in_sup_of_in_some_set_defMem isLub ⟨s3, s3In, dNinS3⟩

  def ordStd.in_some_set_of_in_sup_defMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (dInSup: d ∈ lub.defMem)
  :
    ∃ s3 ∈ set, d ∈ s3.defMem
  :=
    by_contradiction fun nex =>
      let ninAnySet := by push_neg at nex; exact nex
      nin_sup_of_nin_any_set_defMem isLub ninAnySet dInSup


  def ordStd.nin_sup_of_nin_any_set_posMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (ninAnySet: ∀ s3 ∈ set, d ∉ s3.posMem)
  :
    d ∉ lub.posMem
  :=
    let _ := ordStd D
    let lubWithout := lub.without d
    let isLubWithout: IsLUB set lubWithout :=
      And.intro
        (fun s3 s3In => {
          defLe := fun s3D s3DMem =>
            let neq (eq: s3D = d) := ninAnySet s3 s3In (eq ▸ s3DMem.toPos)
            ⟨(isLub.left s3In).defLe s3DMem, neq⟩
          posLe := fun s3D s3DMem =>
            let neq (eq: s3D = d) := ninAnySet s3 s3In (eq ▸ s3DMem)
            ⟨(isLub.left s3In).posLe s3DMem, neq⟩
        })
        (fun _f fIn =>
          (without.leStd lub d).trans (isLub.right fIn))
    
    isLub.unique isLubWithout ▸
    fun ia => ia.neq rfl

  def ordStd.in_sup_of_in_some_set_posMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (inSomeSet: ∃ s3 ∈ set, d ∈ s3.posMem)
  :
    d ∈ lub.posMem
  :=
    let ⟨_s3, inSet, dIn⟩ := inSomeSet
    (isLub.left inSet).posLe dIn

  def ordStd.in_no_set_of_nin_sup_posMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (dNinSup: d ∉ lub.posMem)
  :
    ∀ s3 ∈ set, d ∉ s3.posMem
  :=
    fun s3 s3In dNinS3 =>
      dNinSup <| in_sup_of_in_some_set_posMem isLub ⟨s3, s3In, dNinS3⟩

  def ordStd.in_some_set_of_in_sup_posMem
    {set: Set (Set3 D)}
    (isLub: IsLUB set lub)
    (dInSup: d ∈ lub.posMem)
  :
    ∃ s3 ∈ set, d ∈ s3.posMem
  :=
    by_contradiction fun nex =>
      let ninAnySet := by push_neg at nex; exact nex
      nin_sup_of_nin_any_set_posMem isLub ninAnySet dInSup
  
end Set3
