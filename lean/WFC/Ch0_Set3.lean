/-
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
  
  The least element of the standard ordering is the empty triset,
  while the least element of the approximation ordering is the
  wholly undetermined triset.
  
  Both orders are proven chain-complete.
-/

import Utils.BasicUtils
import Utils.Lfp


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
  
  
  /-
    An element which is not a possible member is also not a
    definitive member.
  -/
  def notDefOfNotPos
    (s3: Set3 D)
    (notPos: ¬ s3.posMem d)
  :
    ¬ s3.defMem d
  :=
    fun isDef => notPos (s3.defLePos isDef)
  
  
  -- The empty triset contains no elements.
  def empty {D: Type}: Set3 D :=
    ⟨Set.empty, Set.empty, Preorder.le_refl _⟩
  
  /-
    The wholly undetermined triset possibly contains all
    elements of `D`, but has no definitive members.
  -/
  def undetermined {D: Type}: Set3 D :=
    ⟨Set.empty, Set.full, fun _ => False.elim⟩
  
  -- The full triset contains all elements of `D`.
  def full {D: Type}: Set3 D :=
    ⟨Set.full, Set.full, Preorder.le_refl _⟩
  
  -- A triset containing a single element.
  def just {D: Type} (d: D): Set3 D :=
    ⟨Set.just d, Set.just d, Preorder.le_refl _⟩
  
  def ofSet (s: Set D): Set3 D :=
    ⟨s, s, Preorder.le_refl _⟩
  
  
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
  
  instance ltInst: LT (Set3 D) where
    lt := LtStd
  
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
  
  def ord.approximation (D: Type u): PartialOrder (Set3 D) where
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
  
  def ord.standard (D: Type u): PartialOrder (Set3 D) where
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
              -- Why tf is `by exact` required???
              (fun d dMem => by exact ⟨s, dMem⟩)
              (fun d dMem => by exact ⟨s, dMem⟩))
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
  
end Set3
