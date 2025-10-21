-- # Chapter 1: Expressions and Definition Lists

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

import Etst.WFC.Ch0_Set3

namespace Etst


/-
  ArityZero, ArityOne, and ArityTwo are types that have exactly
  zero, one, and two elements, respectively. They are useful for
  defining particular signatures (see below).
-/
inductive ArityZero
inductive ArityOne | zth
inductive ArityTwo | zth | fst

def ArityZero.elim (az: ArityZero): T := nomatch az

/-
  A signature is a set of operators, each with a fixed number of
  parameters.
  
  `Op` is the type (or "set") of operators of the signature.
  
  `Params` is a function that maps each operator to a type whose
  elements represent the individual parameters of the operator.
  For example, for a nullary operator (a constant) `op`, `Params op`
  would be the empty type, and for a binary operator, `Params op`
  would be a type having exactly two elements.
  
  Thanks to answerers of https://proofassistants.stackexchange.com/q/1740
-/
structure Signature where
  Op: Type u
  Params: Op → Type v


/-
  An expression is an inductive structure defined over a signature
  `sig`. It can be a variable, the application of an operator to its
  parameters, the complement of an expression, or an arbitrary union
  or intersection.
  
  Variables are natural numbers. The arguments of an operator `op`
  are indexed by the type `sig.Params op`.
  
  `E` (extra info) is for storing arbitrary extra information in each
  variable.
-/
inductive Expr (E: Type*) (sig: Signature) where
| var (e: E) (x: Nat)
| bvar (x: Nat) -- Uses de Bruijn indices
| op (op: sig.Op) (args: sig.Params op → Expr E sig)
| compl (body: Expr E sig)
| arbUn (body: Expr E sig)
| arbIr (body: Expr E sig)


abbrev BasicExpr := Expr Unit
def BasicExpr.var (x: Nat): BasicExpr sig := Expr.var () x
def BasicExpr.bvar (x: Nat): BasicExpr sig := Expr.bvar x
def BasicExpr.op
  (op: sig.Op)
  (args: sig.Params op → BasicExpr sig)
:
  BasicExpr sig
:=
  Expr.op op args
def BasicExpr.compl (body: BasicExpr sig): BasicExpr sig :=
  Expr.compl body
def BasicExpr.arbUn (body: BasicExpr sig): BasicExpr sig :=
  Expr.arbUn body
def BasicExpr.arbIr (body: BasicExpr sig): BasicExpr sig :=
  Expr.arbIr body

namespace Expr
  def UsesVar (expr: Expr E sig): Set Nat :=
    fun x =>
      match expr with
        | var _ v => x = v
        | bvar _ => False
        | op _ args => ∃ param, (args param).UsesVar x
        | compl body => body.UsesVar x
        | arbUn body => body.UsesVar x
        | arbIr body => body.UsesVar x


  /-
    A positive expression is an expression that does not contain
    complements of expressions, with the exception of complements
    of bound variables.
    
    Complementing a bound variable is allowed because it is guaranteed
    to be two-valued, so it cannot result in a contradictory definition.
  -/
  def IsPositive: Expr E sig → Prop
  | var _ _ => True
  | bvar _ => True
  | op _ args => ∀ param, (args param).IsPositive
  | compl (bvar _) => True
  | compl _ => False
  | arbUn body => body.IsPositive
  | arbIr body => body.IsPositive

  /-
    A helper function that we can use to show termination of
    functions defined recursively over expressions.
    
    This is a proper version of the sizeOf function defined natively
    by Lean.
  -/
  noncomputable def sizeOf: Expr E sig → Ordinal.{0}
  | var _ _ => 0
  | bvar _ => 0
  | op _ args =>
      iSup (fun arg => (args arg).sizeOf) + 1
  | compl body => body.sizeOf + 1
  | arbUn body => body.sizeOf + 1
  | arbIr body => body.sizeOf + 1
end Expr


def DefList.GetDef (sig: Signature) := Nat → BasicExpr sig

/-
  A definition list is a map from natural numbers to expressions.
  It is used to allow recursive definitions -- the free variables
  in a definition refer to other definitions of the definition list.
-/
structure DefList (sig: Signature) where
  getDef: DefList.GetDef sig

-- The definition x depends on y x contains y, possibly transitively.
inductive DefList.DependsOn
  (getDef: GetDef sig)
:
  Nat → Nat → Prop
where
| Base
  (aUsesB: (getDef a).UsesVar b)
  :
    DependsOn getDef a b
| Rec
  (aUsesB: (getDef a).UsesVar b)
  (bUsesC: DependsOn getDef b c)
  :
    DependsOn getDef a c

/-
  If `a` depends on `b`, and `b` has a free variable `c`, then `a`
  also depends on `c`.
-/
def DefList.DependsOn.push
  {getDef: GetDef sig}
  (dependsOn: DependsOn getDef a b)
  (isFree: (getDef b).UsesVar c)
:
  DependsOn getDef a c
:=
  -- Lean cannot verify termination here :/
  -- match dependsOn with
  -- | Base b => Rec b (Base isFree)
  -- | Rec head tail =>
  --   let ih := push tail isFree
  --   sorry
  let thePrincipleTM:
    (getDef b).UsesVar c → DependsOn getDef a c
  :=
    dependsOn.rec
      (fun isFreeAB isFreeBC => Rec isFreeAB (Base isFreeBC))
      (fun isFree _ ih ihh =>
        Rec isFree (ih ihh))
  
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
def DefList.IsFinBounded (getDef: GetDef sig): Prop :=
  ∀ name,
  ∃ upperBound,
  ∀ {dep}
    (_: DependsOn getDef name dep)
  ,
    dep < upperBound

-- A finitely bounded definition list. See IsFinBounded above.
structure FinBoundedDL (sig: Signature) extends DefList sig where
  isFinBounded: DefList.IsFinBounded getDef
