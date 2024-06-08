-- # Chapter 1: Expressions

import Utils.BasicUtils

/-
  ArityZero, ArityOne, and ArityTwo are types that have exactly
  zero, one, and two elements, respectively. They are useful for
  defining particular signatures (see below).
-/
inductive ArityZero
inductive ArityOne | zth
inductive ArityTwo | zth | fst

def ArityZero.noInst: ArityZero → False := ArityZero.rec
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
  An expression is an inductive tree-like structure defined over
  a signature `sig`. It can be a variable, the application of an
  operator to its parameters, a binary union or intersection, the
  complement of an expression, a conditional expression, or an
  arbitrary union or intersection.
  
  Variables are natural numbers. The arguments of an operator `op`
  are indexed by the type `sig.Params op`.
-/
inductive Expr (sig: Signature) where
| var (x: Nat)
| op (op: sig.Op) (args: sig.Params op → Expr sig)
| un (left rite: Expr sig)
| ir (left rite: Expr sig)
| cpl (expr: Expr sig)
| ifThen (cond expr: Expr sig)
| Un (x: Nat) (body: Expr sig)
| Ir (x: Nat) (body: Expr sig)

namespace Expr
  instance coeNat: Coe Nat (Expr s) where
    coe := fun n => Expr.var n
  
  instance exprOfNat (n: Nat): OfNat (Expr s) n where
    ofNat := Expr.var n
  
  def any: Expr s := Expr.un 0 (Expr.cpl 0)
end Expr

/-
  The set of free variables of `expr`, given a set of bound
  variables.
-/
def Expr.IsFreeVar
  (expr: Expr sig)
  (boundVars: Set Nat)
:
  Set Nat
:=
  fun x =>
    match expr with
      | var v => x = v ∧ v ∉ boundVars
      | op _ args => ∃ param, (args param).IsFreeVar boundVars x
      | un left rite =>
          Or
            (left.IsFreeVar boundVars x)
            (rite.IsFreeVar boundVars x)
      | ir left rite =>
          Or
            (left.IsFreeVar boundVars x)
            (rite.IsFreeVar boundVars x)
      | cpl expr => expr.IsFreeVar boundVars x
      | ifThen cond expr =>
          Or
            (cond.IsFreeVar boundVars x)
            (expr.IsFreeVar boundVars x)
      | Un bv body => body.IsFreeVar (fun v => v ∈ boundVars ∨ v = bv) x
      | Ir bv body => body.IsFreeVar (fun v => v ∈ boundVars ∨ v = bv) x


/-
  A positive expression is an expression that does not contain
  complements of expressions, with the exception of complements
  of bound variables.
  
  Complementing a bound variable is allowed because it cannot
  result in a contradictory definition, even with self-reference.
-/
def Expr.IsPositive: Expr sig → (boundVars: Set Nat) → Prop
| Expr.var _, _ => True
| Expr.op _ args, bv => ∀ param, (args param).IsPositive bv
| Expr.un left rite, bv => left.IsPositive bv ∧ rite.IsPositive bv
| Expr.ir left rite, bv => left.IsPositive bv ∧ rite.IsPositive bv
| Expr.cpl (Expr.var v), bv => v ∈ bv
| Expr.cpl _, _ => False
| Expr.ifThen cond expr, bv => cond.IsPositive bv ∧ expr.IsPositive bv
| Expr.Un xUn body, bv => body.IsPositive (fun x => x ∈ bv ∨ x = xUn)
| Expr.Ir xIr body, bv => body.IsPositive (fun x => x ∈ bv ∨ x = xIr)
