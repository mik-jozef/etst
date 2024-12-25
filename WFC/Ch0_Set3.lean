/-
  Volume 0: Well-founded Collections
  # Chapter 0: Three-valued Sets
  
  This file defines a type `Set3 (D: Type)` that represents
  a set whose membership relation is three-valued -- every
  element is either a definitive member, a definitive
  non-member, or its membership is *undetermined*.
  Elements of `Set3 D` are called trisets of `D`.
  
  Elements that are either definitive members or undetermined
  members are called possible members. Trisets with no undetermined
  elements are called *classical* (or two-valued).
  
  Formally, a `Set3 D` is a pair `(defMem, posMem)` of sets of
  `D` such that `defMem ⊆ posMem` (`defMem` and `posMem` contain
  the definitive and possible members, respectively).
  
  Two orders are defined on `Set3 D`, the standard order and the
  approximation order.
  
  (Informally,) a triset `a` is less than or equal to `b` in the
  standard order if it contains fewer definitive members and fewer
  possible members than `b`. Formally, `a ≤ b` if
  
      a.defMem ⊆ b.defMem ∧ a.posMem ⊆ b.posMem  \,.
  
  A triset `a` is less than or equal to `b` in the approximation
  order if it has more undetermined members (ie. both fewer
  definitive members and fewer definitive nonmembers), but agrees
  with `b` on its determined members. Formally, `a ⊑ b` if
  
      a.defMem ⊆ b.defMem ∧ b.posMem ⊆ a.posMem  \,.
  
  The least element of the standard order is the empty triset,
  while the least element of the approximation order is the wholly
  undetermined triset.
  
  Both orders are proven chain-complete.
-/

import Utils.BasicUtils
import Utils.Lfp


-- The definition of Set3.
structure Set3 (D: Type u) where
  defMem: Set D -- The definitive members
  posMem: Set D -- The possible members
  defLePos: defMem ≤ posMem

namespace Set3
  -- A convenience function allowing us to use `isDef.toPos` on
  -- instances of `Set3.defMem s d`.
  def defMem.toPos (isDef: Set3.defMem s d) : s.posMem d :=
    s.defLePos isDef
  
  -- If two trisets have the same definitive and possible members,
  -- they are equal.
  protected def eq:
    {a b: Set3 D} →
    a.defMem = b.defMem →
    a.posMem = b.posMem
  →
    a = b
  -- Thanks to answerers of https://proofassistants.stackexchange.com/q/1747
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl
  
  /-
    An element which is not a possible member is also not a
    definitive member.
  -/
  def notDefOfNotPos
    {s3: Set3 D}
    (notPos: ¬ s3.posMem d)
  :
    ¬ s3.defMem d
  :=
    fun isDef => notPos isDef.toPos
  
  
  -- The empty triset contains no elements.
  def empty: Set3 D :=
    ⟨Set.empty, Set.empty, Preorder.le_refl _⟩
  
  /-
    The wholly undetermined triset possibly contains all
    elements of `D`, but has no definitive members.
  -/
  def undetermined: Set3 D :=
    ⟨Set.empty, Set.full, fun _ => False.elim⟩
  
  -- The full triset contains all elements of `D`.
  def full: Set3 D :=
    ⟨Set.full, Set.full, Preorder.le_refl _⟩
  
  -- A triset containing a single element.
  def just (d: D): Set3 D :=
    ⟨Set.just d, Set.just d, Preorder.le_refl _⟩
  
  def ofSet (s: Set D): Set3 D :=
    ⟨s, s, Preorder.le_refl _⟩
  
  
  /-
    The definition of the "less than or equal to" relation for
    the standard order.
  -/
  structure LeStd (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
  
  /-
    The definition of the "less than" relation for the standard
    order.
  -/
  structure LtStd (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
    neq: a ≠ b
  
  
  /-
    The definition of the "less than or equal to" relation for
    the approximation order.
  -/
  structure LeApx (a b: Set3 D): Prop where
    intro ::
    defLe: a.defMem ≤ b.defMem
    posLe: b.posMem ≤ a.posMem
  
  /-
    The definition of the "less than" relation for the approximation
    order.
  -/
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
  
  -- Support for the `≤` symbol (standard `le`).
  instance leInst: LE (Set3 D) where
    le := LeStd
  
  -- Support for the `<` symbol (standard `lt`).
  instance ltInst: LT (Set3 D) where
    lt := LtStd
  
  -- Support for the `⊑` symbol (approximation `le`).
  instance sqleInst: SqLE (Set3 D) where
    le := LeApx
  
  -- Support for the `⊏` symbol (approximation `lt`).
  instance sqltInst: SqLT (Set3 D) where
    lt := LtApx
  
  
  -- The approximation relation is antisymmetric.
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
  
  -- The definition of the approximation order.
  def ord.approximation (D: Type u): PartialOrder (Set3 D) where
    le := LeApx
    lt := LtApx
    
    -- The reflexivity of the approximation order.
    le_refl (a: Set3 D) :=
      LeApx.intro
        (Preorder.le_refl (a.defMem))
        (Preorder.le_refl (a.posMem))
    
    -- The antisymmetry of the approximation order.
    le_antisymm := approximation.le_antisymm
    
    -- The transitivity of the approximation order.
    le_trans (a b c: Set3 D) (ab: a ⊑ b) (bc: b ⊑ c) :=
      LeApx.intro
        (Preorder.le_trans _ _ _ ab.defLe bc.defLe)
        (Preorder.le_trans _ _ _ bc.posLe ab.posLe)
    
    -- The compatibility of the `le` and `lt` relations. 
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
  
  
  -- The standard order is antisymmetric.
  def ord.standard.le_antisymm (a b: Set3 D) (ab: a ≤ b) (ba: b ≤ a) :=
    let defEq: a.defMem = b.defMem :=
      PartialOrder.le_antisymm a.defMem b.defMem ab.defLe ba.defLe;
    let posEq: a.posMem = b.posMem :=
      PartialOrder.le_antisymm a.posMem b.posMem ab.posLe ba.posLe;
    Set3.eq defEq posEq
  
  -- The definition of the standard order.
  def ord.standard (D: Type u): PartialOrder (Set3 D) where
    le := LeStd
    lt := LtStd
    
    -- The reflexivity of the standard order.
    le_refl (a: Set3 D) :=
      LeStd.intro
        (Preorder.le_refl (a.defMem))
        (Preorder.le_refl (a.posMem))
    
    -- The antisymmetry of the standard order.
    le_antisymm := standard.le_antisymm
    
    -- The transitivity of the standard order.
    le_trans (a b c: Set3 D) (ab: a ≤ b) (bc: b ≤ c) :=
      LeStd.intro
        (Preorder.le_trans a.defMem b.defMem c.defMem ab.defLe bc.defLe)
        (Preorder.le_trans a.posMem b.posMem c.posMem ab.posLe bc.posLe)
    
    -- The compatibility of the `le` and `lt` relations.
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
  
  /-
    The supremum of a set of trisets wrt. the standard order.
    
    Its definitive members are the union of the definitive
    members of the trisets in the set, and its possible members
    are the union of the possible members.
  -/
  def ord.standard.sup (s: Set (Set3 D)): Supremum (standard D) s :=
    let sup: Set3 D := {
      defMem := fun d => ∃s: ↑s, d ∈ s.val.defMem
      posMem := fun d => ∃s: ↑s, d ∈ s.val.posMem
      defLePos :=
        fun _ dDef =>
          let ⟨s, isDef⟩ := dDef
          ⟨s, isDef.toPos⟩
    }
    ⟨
      sup,
      {
        isMember :=
          (fun s =>
            LeStd.intro
              (fun _ dMem => ⟨s, dMem⟩)
              (fun _ dMem => ⟨s, dMem⟩))
        isLeMember :=
          fun ub ubIsUB =>
            LeStd.intro
              (fun d dMemSupWtf =>
                let dMemSup: ∃s: ↑s, d ∈ s.val.defMem := dMemSupWtf;
                let s := dMemSup.unwrap
                let sLeUb: s.val.val ≤ ub := ubIsUB s
                let dInS: d ∈ s.val.val.defMem := s.property
                sLeUb.defLe dInS)
              (fun d dMemSupWtf =>
                let dMemSup: ∃s: ↑s, d ∈ s.val.posMem := dMemSupWtf;
                let s := dMemSup.unwrap
                let sLeUb: s.val.val ≤ ub := ubIsUB s
                let dInS: d ∈ s.val.val.posMem := s.property
                sLeUb.posLe dInS)
      }
    ⟩
  
  /-
    The supremum of a chain of trisets wrt. the approximation order.
    
    Its definitive members are the union of the definitive members
    of the trisets in the chain, and its possible members are the
    intersection of the possible members.
  -/
  def ord.approximation.sup (ch: Chain (approximation D)):
    Supremum (approximation D) ch
  :=
    let sup: Set3 D := {
      defMem := fun d => ∃ s: ↑ch, d ∈ s.val.defMem
      posMem := fun d => ∀ s: ↑ch, d ∈ s.val.posMem
      defLePos :=
        fun _d dDef s =>
          let sOfD := dDef.unwrap
          let sSOfDComparable := ch.isChain s.property sOfD.val.property
          
          if h: s.val = sOfD then
            h ▸ sOfD.property.toPos
          else
            (sSOfDComparable h).elim
              (fun sLe => sLe.posLe sOfD.property.toPos)
              (fun sGe => (sGe.defLe sOfD.property).toPos)
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
  
  
  -- The standard order is chain-complete.
  def ord.standard.isChainComplete (D: Type u):
    IsChainComplete (ord.standard D)
  := {
    supExists :=
      fun ch => ⟨(sup ch.set).val, (sup ch.set).property⟩
  }
  
  -- The approximation order is chain-complete.
  def ord.approximation.isChainComplete (D: Type u):
    IsChainComplete (ord.approximation D)
  := {
    supExists :=
      fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
end Set3
