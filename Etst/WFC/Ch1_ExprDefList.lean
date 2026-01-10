-- # Chapter 1: Expressions and Definition Lists

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

import Etst.WFC.Ch0_Set3

namespace Etst


/-
  An expression is an inductive structure that (as we later define)
  can be evaluated to a triset.
  
  `E` (extra info) is for storing arbitrary extra information in each
  variable.
-/
inductive Expr (E: Type*) where
-- TODO perhaps rename to "const", and bvar to var?
| var (e: E) (x: Nat)
| bvar (x: Nat) -- Uses de Bruijn indices
| null
| pair (left rite: Expr E)
| ir (left rite: Expr E)
| condFull (body: Expr E)
| compl (body: Expr E)
| arbIr (body: Expr E)
deriving DecidableEq

def Expr.un (left rite: Expr E): Expr E :=
  compl (ir (compl left) (compl rite))
def Expr.condSome (body: Expr E): Expr E :=
  compl (condFull (compl body))
def Expr.arbUn (body: Expr E): Expr E :=
  compl (arbIr (compl body))


abbrev BasicExpr := Expr Unit

-- Convenience definitions for preserving the `BasicExpr` type in arguments.
def BasicExpr.var (x: Nat): BasicExpr := Expr.var () x
def BasicExpr.bvar (x: Nat): BasicExpr := Expr.bvar x
def BasicExpr.null: BasicExpr := Expr.null
def BasicExpr.pair (left rite: BasicExpr): BasicExpr :=
  Expr.pair left rite
def BasicExpr.un (left rite: BasicExpr): BasicExpr :=
  Expr.un left rite
def BasicExpr.ir (left rite: BasicExpr): BasicExpr :=
  Expr.ir left rite
def BasicExpr.condSome (body: BasicExpr): BasicExpr :=
  Expr.condSome body
def BasicExpr.condFull (body: BasicExpr): BasicExpr :=
  Expr.condFull body
def BasicExpr.compl (body: BasicExpr): BasicExpr :=
  Expr.compl body
def BasicExpr.arbUn (body: BasicExpr): BasicExpr :=
  Expr.arbUn body
def BasicExpr.arbIr (body: BasicExpr): BasicExpr :=
  Expr.arbIr body

namespace Expr
  def UsesVar (expr: Expr E): Set Nat :=
    fun x =>
      match expr with
        | var _ v => x = v
        | bvar _ => False
        | null => False
        | pair left rite => left.UsesVar x ∨ rite.UsesVar x
        | ir left rite => left.UsesVar x ∨ rite.UsesVar x
        | condFull body => body.UsesVar x
        | compl body => body.UsesVar x
        | arbIr body => body.UsesVar x
  
  
  /-
    A positive expression only refers to variables under an even
    number of complements.
  -/
  def IsPositive (expr: Expr E) (isEvenD := true): Prop :=
    match expr with
    | var _ _ => isEvenD
    | bvar _ => True
    | null => True
    | pair left rite =>
        left.IsPositive isEvenD ∧ rite.IsPositive isEvenD
    | ir left rite =>
        left.IsPositive isEvenD ∧ rite.IsPositive isEvenD
    | condFull body => body.IsPositive isEvenD
    | compl body => body.IsPositive (!isEvenD)
    | arbIr body => body.IsPositive isEvenD

  
  -- `any` contains all elements, under any valuation.
  def any: Expr E := .arbUn (.bvar 0)
  -- `none` contains no elements, under any valuation.
  def none: Expr E := .compl any
  
  -- Removes all bound variables with index >= ub.
  def clearBvars (ub := 0): Expr E → Expr E
    | .var info x => .var info x
    | .bvar x => if x < ub then .bvar x else .none
    | .null => .null
    | .pair left rite =>
        .pair (left.clearBvars ub) (rite.clearBvars ub)
    | .ir left rite =>
        .ir (left.clearBvars ub) (rite.clearBvars ub)
    | .condFull body =>
        .condFull (body.clearBvars ub)
    | .compl e => .compl (e.clearBvars ub)
    | .arbIr body => .arbIr (body.clearBvars (ub + 1))
  
  def IsClean (expr: Expr E): Prop :=
    expr = expr.clearBvars
  
end Expr


def DefList.GetDef := Nat → BasicExpr

/-
  A definition list is a map from natural numbers to expressions.
  It is used to allow recursive definitions -- the variables
  in a definition refer to other definitions of the definition list.
-/
structure DefList where
  getDef: DefList.GetDef
  isClean: ∀ name, (getDef name).IsClean

-- The definition x depends on y x contains y, possibly transitively.
inductive DefList.DependsOn
  (getDef: GetDef)
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
  {getDef: GetDef}
  (dependsOn: DependsOn getDef a b)
  (isFree: (getDef b).UsesVar c)
:
  DependsOn getDef a c
:=
  match dependsOn with
  | Base b => Rec b (Base isFree)
  | Rec head tail => Rec head (push tail isFree)

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
def DefList.IsFinBounded (getDef: GetDef): Prop :=
  ∀ name,
  ∃ upperBound,
  ∀ {dep}
    (_: DependsOn getDef name dep)
  ,
    dep < upperBound

-- A finitely bounded definition list. See IsFinBounded above.
structure FinBoundedDL extends DefList where
  isFinBounded: DefList.IsFinBounded getDef
