/-
  # Chapter 2: Valuations
-/

import Utils.Set3
import Utils.Pointwise


/-
  A valuation is a function from variables to trisets of values.
-/
def Valuation D := Nat → Set3 D

namespace Valuation
  /-
    In the empty valuation, every variable represents the empty
    triset.
  -/
  def empty: Valuation D := fun _ => Set3.empty
  
  /-
    In the undetermined valuation, every variable represents
    the undetermined triset.
  -/
  def undetermined: Valuation D := fun _ => Set3.undetermined
  
  -- The approximation order on valuations is defined pointwise.
  def ord.approximation (D: Type u):
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ord.approximation D)
  
  -- The standard order on valuations is defined pointwise.
  def ord.standard (D: Type u)
  :
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ord.standard D)
  
  
  -- The lte relation of the approximation order is denoted using ⊑.
  instance instSqle (D: Type u): SqLE (Valuation D) where
    le := (ord.approximation D).le
  
  -- The lt relation of the approximation order is denoted using ⊏.
  instance instSqlt (D: Type u): SqLT (Valuation D) where
    lt := (ord.approximation D).lt
  
  -- The lte relation of the standard order is denoted using ≤.
  instance instLe (D: Type u): LE (Valuation D) where
    le := (ord.standard D).le
  
  -- The lt relation of the standard order is denoted using <.
  instance instLt (D: Type u): LT (Valuation D) where
    lt := (ord.standard D).lt
  
  
  /-
    The empty valuation is the least element of the standard
    order.
  -/
  def empty.isLeast: iIsLeast (ord.standard D).le Set.full empty := {
    isMember := trivial
    isLeMember :=
      (fun _val _valInFull _x => Set3.LeStd.intro
        (fun _t tInEmpty => False.elim tInEmpty)
        (fun _t tInEmpty => False.elim tInEmpty))
  }
  
  /-
    The undetermined valuation is the least element of the
    approximation order.
  -/
  def undetermined.isLeast:
    iIsLeast (ord.approximation D).le Set.full undetermined
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
    {D: Type u}
    (ch: Chain (standard D))
  :
    Supremum (standard D) ch
  :=
    ch.pointwiseSup (Set3.ord.standard.isChainComplete D)
  
  /-
    Returns the supremum of a chain of valuations under the
    standard order.
  -/
  noncomputable def ord.approximation.sup
    (ch: Chain (approximation D))
  :
    Supremum (approximation D) ch
  :=
    ch.pointwiseSup (Set3.ord.approximation.isChainComplete D)
  
  
  -- The standard order is chain complete.
  def ord.standard.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ord.standard D)
  := {
    supExists := fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  -- The approximation order is chain complete.
  def ord.approximation.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ord.approximation D)
  := {
    supExists := fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  
  /-
    With respect to the standard order, the supremum of the empty
    chain (ie. the least element of the order) is the empty
    valuation.
  -/
  def ord.standard.sup.emptyChain
    (ch: Chain (standard D))
    (chEmpty: ch.IsEmpty)
    (chSup: Supremum (standard D) ch)
  :
    chSup.val = Valuation.empty
  :=
    iIsLeast.isUnique
      (standard D)
      (Chain.sup.empty.isLeast ch chEmpty chSup)
      empty.isLeast
  
  /-
    With respect to the approximation order, the supremum of the
    empty chain (ie. the least element of the order) is the
    undetermined valuation.
  -/
  def ord.approximation.sup.emptyChain
    (ch: Chain (approximation D))
    (chEmpty: ch.IsEmpty)
    (chSup: Supremum (approximation D) ch)
  :
    chSup.val = Valuation.undetermined
  :=
    iIsLeast.isUnique
      (approximation D)
      (Chain.sup.empty.isLeast ch chEmpty chSup)
      undetermined.isLeast
  
  /-
    `val.update x d` is the valuation that is equal to `val` on
    all variables except `x`, whose value is `d`.
  -/
  def update
    (val: Valuation D)
    (x: Nat)
    (d: D)
  :
    Valuation D
  :=
    fun v =>
      if v = x then
        Set3.just d
      else
        val v
  
end Valuation
