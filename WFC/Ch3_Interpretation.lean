-- # Chapter 3: The Interpretation Function

import Utils.Valuation
import Utils.ExprIsFreeVar


def Signature.Args
  (sig: Signature)
  (op: sig.Op)
  (D: Type u)
:=
  sig.Params op → Set D

/-
  Salgebras act not on elements themselves (like algebras do), but
  on sets of elements, monotonically.
  
  (Equivalently, a salgebra on T is an algebra on sets of T whose
  operations are monotonic.)
  
  A salgebra on a signature `sig` provides an interpretation of
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
noncomputable def Expr.interpretation
  (salg: Salgebra sig)
  (b c: Valuation Var salg.D)
:
  (Expr Var sig) → Set3 salg.D

| var a => c a
| op opr exprs =>
    let defArgs := fun arg =>
      (interpretation salg b c (exprs arg)).defMem
    let posArgs := fun arg =>
      (interpretation salg b c (exprs arg)).posMem
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


def DefList.GetDef
  (Var: Type*)
  (sig: Signature)
:=
  Var → Expr Var sig

/-
  A definition list is a map from natural numbers to expressions.
  It is used to allow recursive definitions -- the free variables
  in a definition refer to other definitions of the definition list.
-/
structure DefList
  (Var: Type*)
  (sig: Signature)
where
  getDef: DefList.GetDef Var sig

/-
  The definition x depends on y if x = y or x contains y, possibly
  transitively.
-/
inductive DefList.DependsOn
  (getDef: GetDef Var sig)
:
  Var → Var → Prop
where
| Refl x: DependsOn getDef x x
| Uses
  (aUsesB: (getDef a).IsFreeVar Set.empty b)
  (bUsesC: DependsOn getDef b c)
  :
    DependsOn getDef a c

/-
  If `a` depends on `b`, and `b` has a free variable `c`, then `a`
  also depends on `c`.
-/
def DefList.DependsOn.push
  {getDef: GetDef Var sig}
  (dependsOn: DependsOn getDef a b)
  (isFree: (getDef b).IsFreeVar Set.empty c)
:
  DependsOn getDef a c
:=
  -- Lean cannot verify termination here :/
  -- match dependsOn with
  -- | Refl _ => Uses isFree (Refl c)
  -- | Uses head tail =>
  --   let ih := push tail isFree
  --   ...
  let thePrincipleTM:
    (getDef b).IsFreeVar Set.empty c → DependsOn getDef a c
  :=
    dependsOn.rec
      (fun _ isFree => Uses isFree (Refl c))
      (fun isFree _ ih ihh =>
        Uses isFree (ih ihh))
  
  thePrincipleTM isFree

/-
  A definition list is finitely bounded iff every definition only
  depends on finitely many other definitions (transitively). This
  excludes definition lists like
  
  ```
    let def0 := def1
    let def1 := def3
    let def3 := def4
    ...
  ```
-/
def DefList.IsFinBounded (getDef: GetDef Var sig): Prop :=
  ∀ (name: Var)
    (vars: Set Var)
    (_: ∀ var ∈ vars, DependsOn getDef name var)
  ,
    vars.Finite

-- A version of `IsFinBounded` for natural number variables.
def DefList.IsFinBoundedNat (getDef: GetDef Nat sig): Prop :=
  ∀ name,
  ∃ upperBound,
  ∀ {dep}
    (_: DependsOn getDef name dep)
  ,
    dep < upperBound

-- A proof that `IsFinBoundedNat` implies `IsFinBounded`.
def DefList.isFinBoundedOfNat
  {getDef: GetDef Nat sig}
  (isFinBoundedNat: DefList.IsFinBoundedNat getDef)
:
  DefList.IsFinBounded getDef
:=
  fun x _usedVars usedVarsAreUsed =>
    let ⟨bound, leBoundOfDepends⟩ := isFinBoundedNat x
    (Set.finite_lt_nat bound).subset
      fun usedVar usedVarIsUsed =>
        let xDependsOnUsedVar :=
          usedVarsAreUsed usedVar usedVarIsUsed
        leBoundOfDepends xDependsOnUsedVar

-- Interpretation on definition lists is defined pointwise.
noncomputable def DefList.interpretation
  (salg: Salgebra sig)
  (b c: Valuation Var salg.D)
  (dl: DefList Var sig)
:
  Valuation Var salg.D
:=
  fun x => Expr.interpretation salg b c (dl.getDef x)


-- A finitely bounded definition list. See IsFinBounded above.
structure FinBoundedDL
  (Var: Type*)
  (sig: Signature)
extends
  DefList Var sig
where
  isFinBounded: DefList.IsFinBounded getDef
