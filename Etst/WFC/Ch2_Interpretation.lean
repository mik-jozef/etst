-- # Chapter 2: Interpretation of Expressions

import Etst.WFC.Ch1_Expr_DefList

namespace Etst


-- ## Section 0: Valuations

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
  
  /-
    In the full valuation, every variable represents the full
    triset.
  -/
  def full: Valuation D := fun _ => Set3.full
  
  -- The approximation order on valuations is defined pointwise.
  def ordApx (D: Type u):
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ordApx D)
  
  -- The standard order on valuations is defined pointwise.
  def ordStd (D: Type u)
  :
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ordStd D)
  
  
  -- The lte relation of the approximation order is denoted using ⊑.
  instance instSqle (D: Type u): SqLE (Valuation D) where
    le := (ordApx D).le
  
  -- The lt relation of the approximation order is denoted using ⊏.
  instance instSqlt (D: Type u): SqLT (Valuation D) where
    lt := (ordApx D).lt
  
  -- The lte relation of the standard order is denoted using ≤.
  instance instLe (D: Type u): LE (Valuation D) where
    le := (ordStd D).le
  
  -- The lt relation of the standard order is denoted using <.
  instance instLt (D: Type u): LT (Valuation D) where
    lt := (ordStd D).lt
  
  
  def ordStd.IsLeast (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLeast _ (ordStd D).toLE s a
  
  def ordApx.IsLeast (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLeast _ (ordApx D).toLE s a
  
  def ordStd.IsLUB (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLUB _ (ordStd D).toLE s a
  
  def ordApx.IsLUB (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLUB _ (ordApx D).toLE s a
  
  
  /-
    The empty valuation is the least element of the standard
    order.
  -/
  def ordStd.empty_least {D}: IsLeast (D := D) Set.univ empty := ⟨
    trivial,
    fun _val _valInFull _x => {
      defLe := nofun
      posLe := nofun
    }
  ⟩
  
  /-
    The undetermined valuation is the least element of the
    approximation order.
  -/
  def ordApx.undetermined_least {D}: IsLeast (D := D) Set.univ undetermined := ⟨
    trivial,
    fun _val _valInFull _x => {
      defLe := nofun
      posLe := fun _ _ => trivial
    }
  ⟩

  /-
    Returns the supremum of a chain of valuations under the
    standard order.
  -/
  noncomputable def ordStd.sup
    (isChain: IsChain (ordStd D).le ch)
  :
    Valuation D
  :=
    isChain.pointwiseSup (Set3.ordStd.isChainComplete D)
  
  def ordStd.sup_isLUB
    (isChain: IsChain (ordStd D).le ch)
  :
    IsLUB ch (ordStd.sup isChain)
  :=
    isChain.pointwiseSup_isLUB (Set3.ordStd.isChainComplete D)
  
  
  /-
    Returns the supremum of a chain of valuations under the
    approximation order.
  -/
  noncomputable def ordApx.sup
    (isChain: IsChain (ordApx D).le ch)
  :
    Valuation D
  :=
    isChain.pointwiseSup (Set3.ordApx.isChainComplete D)
  
  def ordApx.sup_isLUB
    (isChain: IsChain (ordApx D).le ch)
  :
    IsLUB ch (ordApx.sup isChain)
  :=
    isChain.pointwiseSup_isLUB (Set3.ordApx.isChainComplete D)
  
  
  -- The standard order is chain complete.
  def ordStd.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ordStd D)
  :=
    fun _ isChain => ⟨sup isChain, sup_isLUB isChain⟩
  
  -- The approximation order is chain complete.
  def ordApx.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ordApx D)
  :=
    fun _ isChain => ⟨sup isChain, sup_isLUB isChain⟩
  
  
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

/-
  `ValVar` encodes some (usage-specific) relation between a variable
  and an element. For example, it may be used to represent the
  assertion that a certain variable contains a certain element in
  some valuation.
  
  That the variable `x` contains the element `d` may be denoted
  as `d ∈ x`.
-/
structure ValVar (D: Type*) where
  d: D
  x: Nat

def Valuation.withBoundVars
  (val: Valuation D)
:
  (boundVars: List (ValVar D)) →
  Valuation D
|
  [] => val
| ⟨d, x⟩ :: tail => (val.withBoundVars tail).update x d


-- ## Section 3: The Interpretation Function


def Signature.Args
  (sig: Signature)
  (op: sig.Op)
  (D: Type u)
:=
  sig.Params op → Set D

/-
  A salgebra on T is an algebra on sets of T whose operations are
  monotonic.
  
  A salgebra with a signature `sig` provides an interpretation of
  each operation in the signature.
  
  The reason for using salgebras rather than algebras and defining
  the operations on sets in the standard manner (which would get
  us monotonicity for free) is that some operations, for example
  the dual of string concatenation, are not definable in this way.
  Take
      { '' } ⊙ {}      = { '' }.
      { 'a' } ⊙ {}     = {}.
      { '', 'a' } ⊙ {} = { '', 'a' }.
-/
structure Salgebra (sig: Signature) where
  D: Type u
  I: (op: sig.Op) → sig.Args op D → Set D
  isMonotonic
    (op: sig.Op)
    (args0 args1: sig.Args op D)
    (le: ∀ param: sig.Params op, args0 param ≤ args1 param)
  :
    I op args0 ≤ I op args1


/-
  The interpretation of an expression is defined using two valuations
  we will call "background" and "context". Context is the "main"
  valuation that is normally used to interpret the variables in the
  expression. Background is used to interpret complements and their
  subexpressions. In particular,
  
      (Expr.cpl expr).interpretation b c
  
  is defined in terms of
  
      expr.interpretation b b \,.
  
  When background and context are the same valuation, this
  definition reduces to the usual one with a single valuation.
  
  The three-valuedness is handled in an intuitive fashion -- the
  definite members of an expression are defined in terms of the
  definite members of its subexpressions, and the same applies to
  the possible members.
  
  An interesting exception is the complement, where `d` is a
  definite member of the complement of `expr` iff `d` is not
  a *possible* member of `expr`, and vice versa.
-/
def Expr.interpretation
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
:
  (Expr sig) → Set3 salg.D

| var a => c a
| op opr exprs =>
    let defArgs arg := (interpretation salg b c (exprs arg)).defMem
    let posArgs arg := (interpretation salg b c (exprs arg)).posMem
    ⟨
      salg.I opr defArgs,
      salg.I opr posArgs,
      
      salg.isMonotonic
        opr
        defArgs
        posArgs
        fun arg => (interpretation salg b c (exprs arg)).defLePos
    ⟩
| cpl e =>
    let ie := (interpretation salg b b e)
    ⟨
      ie.posMemᶜ,
      ie.defMemᶜ,
      
      fun _d dInNPos => fun dInDef => dInNPos dInDef.toPos
    ⟩
| arbUn x body =>
    let body.I (dX: salg.D): Set3 salg.D :=
      interpretation salg (b.update x dX) (c.update x dX) body
    
    ⟨
      fun d => ∃ dX, d ∈ (body.I dX).defMem,
      fun d => ∃ dX, d ∈ (body.I dX).posMem,
      
      fun _d dDef => dDef.elim fun dX iXDef => ⟨dX, iXDef.toPos⟩
    ⟩
| arbIr x body =>
    let body.I (dX: salg.D): Set3 salg.D :=
      (interpretation salg (b.update x dX) (c.update x dX) body)
    
    ⟨
      fun d => ∀ dX, d ∈ (body.I dX).defMem,
      fun d => ∀ dX, d ∈ (body.I dX).posMem,
      
      fun _d dDefBody xDDef => (dDefBody xDDef).toPos
    ⟩
