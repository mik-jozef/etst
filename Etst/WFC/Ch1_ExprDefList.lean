-- # Chapter 1: Expressions and Definition Lists
module
public import Etst.WFC.Ch0_Set3
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

public section
namespace Etst


inductive ExprKind
| basic
| lane
deriving DecidableEq

abbrev ExprKind.ConstTag: ExprKind → Type
| basic => Unit
| lane => Set3.Lane

instance: (kind: ExprKind) → DecidableEq kind.ConstTag
| .basic => inferInstance
| .lane  => inferInstance

/-
  An expression is an inductive structure that (as we later define)
  can be evaluated to a triset.
  
  The variables use de Bruijn indices, ie. `var 0` refers to the
  innermost quantifier, `var 1` to the next outer one, and so on.
-/
public inductive Expr (kind: ExprKind) where
| const (tag: kind.ConstTag) (x: Nat)
| var (x: Nat)
| null
| prod (left rite: Expr kind)
| ir (left rite: Expr kind)
| full (body: Expr kind)
| compl (body: Expr kind)
| arbIr (body: Expr kind)
deriving DecidableEq

exposed section
def Expr.un {kind} (left rite: Expr kind): Expr kind :=
  compl (ir (compl left) (compl rite))
def Expr.some {kind} (body: Expr kind): Expr kind :=
  compl (full (compl body))
def Expr.arbUn {kind} (body: Expr kind): Expr kind :=
  compl (arbIr (compl body))
end


namespace Expr
  exposed def UsesConst {kind} (expr: Expr kind) (x: Nat): Prop :=
    match expr with
      | const _ v => x = v
      | var _ => False
      | null => False
      | prod left rite => left.UsesConst x ∨ rite.UsesConst x
      | ir left rite => left.UsesConst x ∨ rite.UsesConst x
      | full body => body.UsesConst x
      | compl body => body.UsesConst x
      | arbIr body => body.UsesConst x
  
  exposed def UsesFreeVar {kind} (expr: Expr kind) (x: Nat): Prop :=
    match expr with
      | const _ _ => False
      | var v => x = v
      | null => False
      | prod left rite => left.UsesFreeVar x ∨ rite.UsesFreeVar x
      | ir left rite => left.UsesFreeVar x ∨ rite.UsesFreeVar x
      | full body => body.UsesFreeVar x
      | compl body => body.UsesFreeVar x
      | arbIr body => body.UsesFreeVar (x + 1)
  
  exposed def FreeVarsSat {kind} (expr: Expr kind) (P: Nat → Prop): Prop :=
    ∀ x: Nat, expr.UsesFreeVar x → P x
  
  
  /-
    A positive expression only refers to constants under an even
    number of complements.
  -/
  exposed def IsPositive {kind} (expr: Expr kind) (isEvenD := true): Prop :=
    match expr with
    | const _ _ => isEvenD
    | var _ => True
    | null => True
    | prod left rite =>
        left.IsPositive isEvenD ∧ rite.IsPositive isEvenD
    | ir left rite =>
        left.IsPositive isEvenD ∧ rite.IsPositive isEvenD
    | full body => body.IsPositive isEvenD
    | compl body => body.IsPositive (!isEvenD)
    | arbIr body => body.IsPositive isEvenD

  
  -- `any` contains all elements, under any valuation.
  exposed def any {kind}: Expr kind := arbUn (var 0)
  -- `none` contains no elements, under any valuation.
  exposed def none {kind}: Expr kind := arbIr (compl (var 0))
  
  
  /-
    Increments all free variables by `liftBy`. `depth` represents
    inside how many quantifiers we are.
  -/
  exposed def lift {kind}
    (expr: Expr kind)
    (depth := 0)
    (liftBy := 1)
  :=
    match expr with
    | const info x => const info x
    | var x => var (if x < depth then x else x + liftBy)
    | null => null
    | prod l r => prod (l.lift depth liftBy) (r.lift depth liftBy)
    | ir l r => ir (l.lift depth liftBy) (r.lift depth liftBy)
    | full body => full (body.lift depth liftBy)
    | compl body => compl (body.lift depth liftBy)
    | arbIr body => arbIr (body.lift (depth + 1) liftBy)
  
  /-
    Transforms a map of free variables to one that is equivalent
    inside a single quantifier.
  -/
  exposed def liftFvMap {kind}
    (fvMap: Nat → Expr kind)
  :
    Nat → Expr kind
  | 0 => .var 0
  | n + 1 => (fvMap n).lift
  
  -- Replaces free variables according to a given map.
  exposed def subst {kind}
    (fvMap: Nat → Expr kind)
  :
    Expr kind → Expr kind
  | .const tag x => .const tag x
  | .var x => fvMap x
  | .null => .null
  | .prod left rite =>
    .prod (subst fvMap left) (subst fvMap rite)
  | .ir left rite =>
    .ir (subst fvMap left) (subst fvMap rite)
  | .full body =>
    .full (subst fvMap body)
  | .compl body =>
    .compl (subst fvMap body)
  | .arbIr body =>
    .arbIr (subst (liftFvMap fvMap) body)
  
  public abbrev IsClean {kind} (expr: Expr kind): Prop :=
    expr.FreeVarsSat fun _ => False
  
end Expr


public abbrev DefList.GetDef := Nat → Expr .basic

/-
  A definition list is a map from natural numbers to expressions.
  It is used to allow recursive definitions -- the constants
  in a definition refer to other definitions of the definition list.
-/
public structure DefList where
  getDef: DefList.GetDef
  isClean: ∀ name, (getDef name).IsClean

-- The definition x depends on y iff x contains y, possibly transitively.
public inductive DefList.DependsOn
  (getDef: GetDef)
:
  Nat → Nat → Prop
where
| Base {a b}
    (aUsesB: (getDef a).UsesConst b)
  :
    DependsOn getDef a b
| Rec {a b c}
    (aUsesB: (getDef a).UsesConst b)
    (bUsesC: DependsOn getDef b c)
  :
    DependsOn getDef a c

/-
  If `a` depends on `b`, and `b` has a free constant `c`, then `a`
  also depends on `c`.
-/
public theorem DefList.DependsOn.push
  {getDef: GetDef} {a b c}
  (dependsOn: DependsOn getDef a b)
  (isFree: (getDef b).UsesConst c)
:
  DependsOn getDef a c
:=
  match dependsOn with
  | Base b => Rec b (Base isFree)
  | Rec head tail => Rec head (push tail isFree)

exposed def DefList.IsDefBoundedBy
  (getDef: GetDef)
  (x ub: Nat)
:
  Prop
:=
  ∀ {dep} (_: DependsOn getDef x dep), dep < ub

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
exposed def DefList.IsFinBounded (getDef: GetDef): Prop :=
  ∀ name,
  ∃ upperBound,
  IsDefBoundedBy getDef name upperBound

-- A finitely bounded definition list. See IsFinBounded above.
structure FinBoundedDl extends DefList where
  isFinBounded: DefList.IsFinBounded getDef
