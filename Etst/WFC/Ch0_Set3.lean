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
  undetermined triset. Both orders are chain-complete.
-/

import Mathlib.Data.Set.Basic

import Etst.WFC.Utils.General.PointwiseOrder
import Etst.BasicUtils

namespace Etst


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
  def empty: Set3 D := ⟨{}, {}, le_rfl⟩
  
  /-
    The wholly undetermined triset possibly contains all
    elements of `D`, but has no definitive members.
  -/
  def undetermined: Set3 D := ⟨{}, Set.univ, nofun⟩
  
  -- The full triset contains all elements of `D`.
  def full: Set3 D := ⟨Set.univ, Set.univ, le_rfl⟩
  
  -- A triset containing a single element.
  def just (d: D): Set3 D := ⟨{d}, {d}, le_rfl⟩
  
  def ofSet2 (s: Set D): Set3 D := ⟨s, s, le_rfl⟩
  
  
  /-
    The definition of the "less than or equal to" relation for
    the standard order.
  -/
  structure LeStd (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
  
  /-
    The definition of the "less than" relation for the standard
    order.
  -/
  structure LtStd (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
    neq: a ≠ b
  
  
  /-
    The definition of the "less than or equal to" relation for
    the approximation order.
  -/
  structure LeApx (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: b.posMem ≤ a.posMem
  
  /-
    The definition of the "less than" relation for the approximation
    order.
  -/
  structure LtApx (a b: Set3 D): Prop where
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
  
end Set3
