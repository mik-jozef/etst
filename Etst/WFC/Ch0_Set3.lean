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
module
public import Mathlib.Data.Set.Basic
public import Etst.BasicUtils

import Etst.WFC.Utils.General.PointwiseOrder

namespace Etst

public inductive Set3.Lane
| posLane
| defLane
deriving DecidableEq, Repr

-- The definition of trisets / three-valued sets.
public structure Set3 (D: Type*) where
  getLane: Set3.Lane → Set D
  defLePos: getLane .defLane ≤ getLane .posLane

namespace Set3
  exposed def defMem {D} (s: Set3 D): Set D := s.getLane .defLane
  exposed def posMem {D} (s: Set3 D): Set D := s.getLane .posLane
  
  exposed def Lane.toggle: Lane → Lane
  | .posLane => .defLane
  | .defLane => .posLane
  
  -- A convenience function allowing us to use `isDef.toPos` on
  -- instances of `Set3.defMem s d`.
  public theorem defToPos {D d}
    {s: Set3 D}
    (isDef: d ∈ s.defMem)
  :
    d ∈ s.posMem
  :=
    s.defLePos isDef
  
  -- If two trisets have the same definitive and possible members,
  -- they are equal.
  public protected theorem eq {D}
    {a b: Set3 D}
    (defEq: a.defMem = b.defMem)
    (posEq: a.posMem = b.posMem)
  :
    a = b
  :=
    let getDefEq: a.getLane = b.getLane :=
      funext fun | .defLane => defEq | .posLane => posEq
    -- Thanks to answerers of
    -- https://proofassistants.stackexchange.com/q/1747
    match a, b, getDefEq with
    | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
  
  exposed def ofLanes {D}
    (defLane posLane: Set D)
    (defLePos: defLane ≤ posLane)
  :
    Set3 D
  := ⟨
    fun | .defLane => defLane | .posLane => posLane,
    defLePos,
  ⟩
  
  /-
    An element which is not a possible member is also not a
    definitive member.
  -/
  public theorem not_def_of_not_pos
    {D} {s3: Set3 D} {d}
    (notPos: ¬ d ∈ s3.posMem)
  :
    ¬ d ∈ s3.defMem
  :=
    notPos ∘ defToPos
  
  exposed def ofSet2 {D} (s: Set D): Set3 D := ⟨fun _ => s, le_rfl⟩
  
  -- The empty triset contains no elements.
  exposed def empty {D}: Set3 D := ofSet2 {}
  
  /-
    The wholly undetermined triset possibly contains all
    elements of `D`, but has no definitive members.
  -/
  exposed def undetermined {D}: Set3 D := ofLanes {} Set.univ nofun
  
  -- The universal triset contains all elements of `D`.
  exposed def univ {D}: Set3 D := ofSet2 Set.univ
  
  -- A triset containing a single element.
  exposed def just {D} (d: D): Set3 D := ofSet2 {d}
  
  /-
    The definition of the "less than or equal to" relation for
    the standard order.
  -/
  public structure LeStd {D} (a b: Set3 D): Prop where
    defLe: a.getLane .defLane ≤ b.getLane .defLane
    posLe: a.getLane .posLane ≤ b.getLane .posLane
  
  /-
    The definition of the "less than" relation for the standard
    order.
  -/
  public structure LtStd {D} (a b: Set3 D): Prop where
    defLe: a.getLane .defLane ≤ b.getLane .defLane
    posLe: a.getLane .posLane ≤ b.getLane .posLane
    neq: a ≠ b
  
  
  /-
    The definition of the "less than or equal to" relation for
    the approximation order.
  -/
  public structure LeApx {D} (a b: Set3 D): Prop where
    defLe: a.getLane .defLane ≤ b.getLane .defLane
    posLe: b.getLane .posLane ≤ a.getLane .posLane
  
  /-
    The definition of the "less than" relation for the approximation
    order.
  -/
  public structure LtApx {D} (a b: Set3 D): Prop where
    defLe: a.getLane .defLane ≤ b.getLane .defLane
    posLe: b.getLane .posLane ≤ a.getLane .posLane
    neq: a ≠ b
  
  
  public theorem LtStd.toLe {D}
    {a b: Set3 D}
    (lt: LtStd a b)
  :
    LeStd a b
  := {
    defLe := lt.defLe
    posLe := lt.posLe
  }
  
  public theorem LtApx.toLe {D}
    {a b: Set3 D}
    (lt: LtApx a b)
  :
    LeApx a b
  := {
    defLe := lt.defLe
    posLe := lt.posLe
  }
  
  -- Support for the `≤` symbol (standard `le`).
  public instance leInst {D}: LE (Set3 D) where
    le := LeStd
  
  -- Support for the `<` symbol (standard `lt`).
  public instance ltInst {D}: LT (Set3 D) where
    lt := LtStd
  
  -- Support for the `⊑` symbol (approximation `le`).
  public instance sqleInst {D}: SqLE (Set3 D) where
    le := LeApx
  
  -- Support for the `⊏` symbol (approximation `lt`).
  public instance sqltInst {D}: SqLT (Set3 D) where
    lt := LtApx
  
end Set3
