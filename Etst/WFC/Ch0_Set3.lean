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


-- The definition of trisets / three-valued sets.
structure Set3 (D: Type*) where
  defMem: Set D -- The definitive members
  posMem: Set D -- The possible members
  defLePos: defMem ≤ posMem

namespace Set3
  -- A convenience function allowing us to use `isDef.toPos` on
  -- instances of `Set3.defMem s d`.
  def defMem.toPos {D} {s: Set3 D} {d} (isDef: Set3.defMem s d) : s.posMem d :=
    s.defLePos isDef
  
  -- If two trisets have the same definitive and possible members,
  -- they are equal.
  protected def eq {D}:
    {a b: Set3 D} →
    a.defMem = b.defMem →
    a.posMem = b.posMem
  →
    a = b
  -- Thanks to answerers of https://proofassistants.stackexchange.com/q/1747
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl
  
  def eq_def {D} {s0 s1: Set3 D} (eq: s0 = s1): s0.defMem = s1.defMem :=
    congrArg Set3.defMem eq
  
  def eq_pos {D} {s0 s1: Set3 D} (eq: s0 = s1): s0.posMem = s1.posMem :=
    congrArg Set3.posMem eq
  
  /-
    An element which is not a possible member is also not a
    definitive member.
  -/
  def notDefOfNotPos
    {D} {s3: Set3 D} {d}
    (notPos: ¬ s3.posMem d)
  :
    ¬ s3.defMem d
  :=
    fun isDef => notPos isDef.toPos
  
  -- The empty triset contains no elements.
  def empty {D}: Set3 D := ⟨{}, {}, le_rfl⟩
  
  /-
    The wholly undetermined triset possibly contains all
    elements of `D`, but has no definitive members.
  -/
  def undetermined {D}: Set3 D := ⟨{}, Set.univ, nofun⟩
  
  -- The universal triset contains all elements of `D`.
  def univ {D}: Set3 D := ⟨Set.univ, Set.univ, le_rfl⟩
  
  -- A triset containing a single element.
  def just {D} (d: D): Set3 D := ⟨{d}, {d}, le_rfl⟩
  
  def ofSet2 {D} (s: Set D): Set3 D := ⟨s, s, le_rfl⟩
  
  
  /-
    The definition of the "less than or equal to" relation for
    the standard order.
  -/
  structure LeStd {D} (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
  
  /-
    The definition of the "less than" relation for the standard
    order.
  -/
  structure LtStd {D} (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: a.posMem ≤ b.posMem
    neq: a ≠ b
  
  
  /-
    The definition of the "less than or equal to" relation for
    the approximation order.
  -/
  structure LeApx {D} (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: b.posMem ≤ a.posMem
  
  /-
    The definition of the "less than" relation for the approximation
    order.
  -/
  structure LtApx {D} (a b: Set3 D): Prop where
    defLe: a.defMem ≤ b.defMem
    posLe: b.posMem ≤ a.posMem
    neq: a ≠ b
  
  
  def LtStd.toLe {D} {a b: Set3 D} (lt: LtStd a b): LeStd a b := {
    defLe := lt.defLe
    posLe := lt.posLe
  }
  
  def LtApx.toLe {D} {a b: Set3 D} (lt: LtApx a b): LeApx a b := {
    defLe := lt.defLe
    posLe := lt.posLe
  }
  
  -- Support for the `≤` symbol (standard `le`).
  instance leInst {D}: LE (Set3 D) where
    le := LeStd
  
  -- Support for the `<` symbol (standard `lt`).
  instance ltInst {D}: LT (Set3 D) where
    lt := LtStd
  
  -- Support for the `⊑` symbol (approximation `le`).
  instance sqleInst {D}: SqLE (Set3 D) where
    le := LeApx
  
  -- Support for the `⊏` symbol (approximation `lt`).
  instance sqltInst {D}: SqLT (Set3 D) where
    lt := LtApx
  
  
  inductive Lane
  | posLane
  | defLane
  deriving DecidableEq
  
  def Lane.toggle: Lane → Lane
  | .posLane => .defLane
  | .defLane => .posLane
  
  def getLane
    {D} (s3: Set3 D)
    (lane: Lane)
  :
    Set D
  :=
    match lane with
    | .posLane => s3.posMem
    | .defLane => s3.defMem
  
end Set3
