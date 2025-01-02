-- # Chapter 2: Valuations

import Utils.Set3
import Utils.Pointwise


/-
  A valuation is a function from variables to trisets of values.
-/
def Valuation Var D := Var → Set3 D

namespace Valuation
  /-
    In the empty valuation, every variable represents the empty
    triset.
  -/
  def empty: Valuation Var D := fun _ => Set3.empty
  
  /-
    In the undetermined valuation, every variable represents
    the undetermined triset.
  -/
  def undetermined: Valuation Var D := fun _ => Set3.undetermined
  
  /-
    In the full valuation, every variable represents the full
    triset.
  -/
  def full: Valuation Var D := fun _ => Set3.full
  
  -- The approximation order on valuations is defined pointwise.
  def ord.approximation (Var D: Type*):
    PartialOrder (Valuation Var D)
  :=
    PartialOrder.pointwise Var (Set3.ord.approximation D)
  
  -- The standard order on valuations is defined pointwise.
  def ord.standard (Var D: Type*)
  :
    PartialOrder (Valuation Var D)
  :=
    PartialOrder.pointwise Var (Set3.ord.standard D)
  
  
  -- The lte relation of the approximation order is denoted using ⊑.
  instance instSqle (Var D: Type*): SqLE (Valuation Var D) where
    le := (ord.approximation Var D).le
  
  -- The lt relation of the approximation order is denoted using ⊏.
  instance instSqlt (Var D: Type*): SqLT (Valuation Var D) where
    lt := (ord.approximation Var D).lt
  
  -- The lte relation of the standard order is denoted using ≤.
  instance instLe (Var D: Type*): LE (Valuation Var D) where
    le := (ord.standard Var D).le
  
  -- The lt relation of the standard order is denoted using <.
  instance instLt (Var D: Type*): LT (Valuation Var D) where
    lt := (ord.standard Var D).lt
  
  
  /-
    The empty valuation is the least element of the standard
    order.
  -/
  def empty.isLeast:
    iIsLeast (ord.standard Var D).le Set.full empty
  := {
    isMember := trivial
    isLeMember := fun _ _ _ => Set3.LeStd.intro nofun nofun
  }
  
  /-
    The undetermined valuation is the least element of the
    approximation order.
  -/
  def undetermined.isLeast:
    iIsLeast (ord.approximation Var D).le Set.full undetermined
  := {
    isMember := trivial
    isLeMember :=
      (fun _val _valInFull _x => Set3.LeApx.intro
        (fun _t tInUndet => False.elim tInUndet)
        (fun _t _tInUndet => trivial))
  }
  
  /-
    Returns the supremum of a chain of valuations under the
    approximation order.
  -/
  noncomputable def ord.standard.sup
    {D: Type*}
    (ch: Chain (standard Var D))
  :
    Supremum (standard Var D) ch
  :=
    ch.pointwiseSup (Set3.ord.standard.isChainComplete D)
  
  /-
    Returns the supremum of a chain of valuations under the
    standard order.
  -/
  noncomputable def ord.approximation.sup
    (ch: Chain (approximation Var D))
  :
    Supremum (approximation Var D) ch
  :=
    ch.pointwiseSup (Set3.ord.approximation.isChainComplete D)
  
  
  -- The standard order is chain complete.
  def ord.standard.isChainComplete (D: Type*)
  :
    IsChainComplete (Valuation.ord.standard Var D)
  := {
    supExists := fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  -- The approximation order is chain complete.
  def ord.approximation.isChainComplete (D: Type*)
  :
    IsChainComplete (Valuation.ord.approximation Var D)
  := {
    supExists := fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  
  /-
    With respect to the standard order, the supremum of the empty
    chain (ie. the least element of the order) is the empty
    valuation.
  -/
  def ord.standard.sup.emptyChain
    (ch: Chain (standard Var D))
    (chEmpty: ch.IsEmpty)
    (chSup: Supremum (standard Var D) ch)
  :
    chSup.val = Valuation.empty
  :=
    iIsLeast.isUnique
      (standard Var D)
      (Chain.sup.empty.isLeast ch chEmpty chSup)
      empty.isLeast
  
  /-
    With respect to the approximation order, the supremum of the
    empty chain (ie. the least element of the order) is the
    undetermined valuation.
  -/
  def ord.approximation.sup.emptyChain
    (ch: Chain (approximation Var D))
    (chEmpty: ch.IsEmpty)
    (chSup: Supremum (approximation Var D) ch)
  :
    chSup.val = Valuation.undetermined
  :=
    iIsLeast.isUnique
      (approximation Var D)
      (Chain.sup.empty.isLeast ch chEmpty chSup)
      undetermined.isLeast
  
  /-
    `val.update x d` is the valuation that is equal to `val` on
    all variables except `x`, whose value is `d`.
  -/
  def update
    [DecidableEq Var]
    (val: Valuation Var D)
    (x: Var)
    (d: D)
  :
    Valuation Var D
  :=
    fun v =>
      if v = x then
        Set3.just d
      else
        val v
  
  def remove
    [DecidableEq Var]
    (val: Valuation Var D)
    (x: Var)
    (d: D)
  :
    Valuation Var D
  :=
    fun v =>
      if v = x then
        (val v).without d
      else
        val v
  
  
  /-
    `ValVar` encodes some (usage-specific) relation between a variable
    and an element. For example, it may be used to represent the
    assertion that a certain variable contains a certain element in
    some valuation. (which may be denoted as `d ∈ x`).
  -/
  structure _root_.ValVar (Var D: Type*) where
    d: D
    x: Var

  def withBoundVars
    [DecidableEq Var]
    (val: Valuation Var D)
  :
    (boundVars: List (ValVar Var D)) →
    Valuation Var D
  |
    [] => val
  | ⟨d, x⟩ :: tail => (val.withBoundVars tail).update x d
  
end Valuation
