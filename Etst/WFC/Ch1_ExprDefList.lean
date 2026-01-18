-- # Chapter 1: Expressions and Definition Lists

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

import Etst.WFC.Ch0_Set3

namespace Etst


/-
  An expression is an inductive structure that (as we later define)
  can be evaluated to a triset.
  
  `E` (extra info) is for storing arbitrary extra information in each
  constant.
-/
inductive Expr (E: Type*) where
| const (e: E) (x: Nat)
| var (x: Nat) -- Uses de Bruijn indices
| null
| pair (left rite: Expr E)
| ir (left rite: Expr E)
| full (body: Expr E)
| compl (body: Expr E)
| arbIr (body: Expr E)
deriving DecidableEq

def Expr.un (left rite: Expr E): Expr E :=
  compl (ir (compl left) (compl rite))
def Expr.some (body: Expr E): Expr E :=
  compl (full (compl body))
def Expr.arbUn (body: Expr E): Expr E :=
  compl (arbIr (compl body))


abbrev BasicExpr := Expr Unit

-- Convenience definitions for preserving the `BasicExpr` type in arguments.
def BasicExpr.const (x: Nat): BasicExpr := Expr.const () x
def BasicExpr.var (x: Nat): BasicExpr := Expr.var x
def BasicExpr.null: BasicExpr := Expr.null
def BasicExpr.pair (left rite: BasicExpr): BasicExpr :=
  Expr.pair left rite
def BasicExpr.un (left rite: BasicExpr): BasicExpr :=
  Expr.un left rite
def BasicExpr.ir (left rite: BasicExpr): BasicExpr :=
  Expr.ir left rite
def BasicExpr.some (body: BasicExpr): BasicExpr :=
  Expr.some body
def BasicExpr.full (body: BasicExpr): BasicExpr :=
  Expr.full body
def BasicExpr.compl (body: BasicExpr): BasicExpr :=
  Expr.compl body
def BasicExpr.arbUn (body: BasicExpr): BasicExpr :=
  Expr.arbUn body
def BasicExpr.arbIr (body: BasicExpr): BasicExpr :=
  Expr.arbIr body

namespace Expr
  def UsesConst (expr: Expr E): Set Nat :=
    fun x =>
      match expr with
        | const _ v => x = v
        | var _ => False
        | null => False
        | pair left rite => left.UsesConst x ∨ rite.UsesConst x
        | ir left rite => left.UsesConst x ∨ rite.UsesConst x
        | full body => body.UsesConst x
        | compl body => body.UsesConst x
        | arbIr body => body.UsesConst x
  
  
  /-
    A positive expression only refers to constants under an even
    number of complements.
  -/
  def IsPositive (expr: Expr E) (isEvenD := true): Prop :=
    match expr with
    | const _ _ => isEvenD
    | var _ => True
    | null => True
    | pair left rite =>
        left.IsPositive isEvenD ∧ rite.IsPositive isEvenD
    | ir left rite =>
        left.IsPositive isEvenD ∧ rite.IsPositive isEvenD
    | full body => body.IsPositive isEvenD
    | compl body => body.IsPositive (!isEvenD)
    | arbIr body => body.IsPositive isEvenD

  
  -- `any` contains all elements, under any valuation.
  def any: Expr E := .arbUn (.var 0)
  -- `none` contains no elements, under any valuation.
  def none: Expr E := .compl any
  
  -- Removes all variables with index >= ub.
  def clearVars (ub := 0): Expr E → Expr E
    | .const info x => .const info x
    | .var x => if x < ub then .var x else .none
    | .null => .null
    | .pair left rite =>
        .pair (left.clearVars ub) (rite.clearVars ub)
    | .ir left rite =>
        .ir (left.clearVars ub) (rite.clearVars ub)
    | .full body =>
        .full (body.clearVars ub)
    | .compl e => .compl (e.clearVars ub)
    | .arbIr body => .arbIr (body.clearVars (ub + 1))
  
  def IsClean (expr: Expr E): Prop :=
    expr = expr.clearVars
  
end Expr


def DefList.GetDef := Nat → BasicExpr

/-
  A definition list is a map from natural numbers to expressions.
  It is used to allow recursive definitions -- the constants
  in a definition refer to other definitions of the definition list.
-/
structure DefList where
  getDef: DefList.GetDef
  isClean: ∀ name, (getDef name).IsClean

-- The definition x depends on y iff x contains y, possibly transitively.
inductive DefList.DependsOn
  (getDef: GetDef)
:
  Nat → Nat → Prop
where
| Base
  (aUsesB: (getDef a).UsesConst b)
  :
    DependsOn getDef a b
| Rec
  (aUsesB: (getDef a).UsesConst b)
  (bUsesC: DependsOn getDef b c)
  :
    DependsOn getDef a c

/-
  If `a` depends on `b`, and `b` has a free constant `c`, then `a`
  also depends on `c`.
-/
def DefList.DependsOn.push
  {getDef: GetDef}
  (dependsOn: DependsOn getDef a b)
  (isFree: (getDef b).UsesConst c)
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
