-- # Chapter 1: Expressions

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

import Utils.BasicUtils

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
  An expression is an inductive tree-like structure defined over
  a signature `sig`. It can be a variable, the application of an
  operator to its parameters, the complement of an expression, or
  an arbitrary union or intersection.
  
  Variables are natural numbers. The arguments of an operator `op`
  are indexed by the type `sig.Params op`.
-/
inductive Expr (sig: Signature) where
| var (x: Nat)
| op (op: sig.Op) (args: sig.Params op → Expr sig)
| cpl (expr: Expr sig)
| arbUn (x: Nat) (body: Expr sig)
| arbIr (x: Nat) (body: Expr sig)

namespace Expr
  instance coeNat: Coe Nat (Expr s) where
    coe := fun n => Expr.var n
  
  instance exprOfNat (n: Nat): OfNat (Expr s) n where
    ofNat := Expr.var n
  
  /-
    The set of free variables of `expr`, given a set of bound
    variables.
  -/
  def IsFreeVar
    (expr: Expr sig)
    (boundVars: Set Nat := Set.empty)
  :
    Set Nat
  :=
    fun x =>
      match expr with
        | var v => x = v ∧ v ∉ boundVars
        | op _ args => ∃ param, (args param).IsFreeVar boundVars x
        | cpl expr => expr.IsFreeVar boundVars x
        | arbUn bv body => body.IsFreeVar (fun v => v ∈ boundVars ∨ v = bv) x
        | arbIr bv body => body.IsFreeVar (fun v => v ∈ boundVars ∨ v = bv) x
  
  
  /-
    A positive expression is an expression that does not contain
    complements of expressions, with the exception of complements
    of bound variables.
    
    Complementing a bound variable is allowed because it cannot
    result in a contradictory definition, even with self-reference.
  -/
  def IsPositive: Expr sig → (boundVars: Set Nat) → Prop
  | Expr.var _, _ => True
  | Expr.op _ args, bv => ∀ param, (args param).IsPositive bv
  | Expr.cpl (Expr.var v), bv => v ∈ bv
  | Expr.cpl _, _ => False
  | Expr.arbUn xUn body, bv => body.IsPositive (fun x => x ∈ bv ∨ x = xUn)
  | Expr.arbIr xIr body, bv => body.IsPositive (fun x => x ∈ bv ∨ x = xIr)
  
  /-
    A helper function that we can use to show termination of
    functions defined recursively over expressions.
    
    This is a proper version of the sizeOf function defined natively
    by Lean.
  -/
  noncomputable def sizeOf: Expr sig → Ordinal.{0}
  | Expr.var _ => 0
  | Expr.op _ args =>
    iSup (fun arg => (args arg).sizeOf) + 1
  | Expr.cpl expr => expr.sizeOf + 1
  | Expr.arbUn _ body => body.sizeOf + 1
  | Expr.arbIr _ body => body.sizeOf + 1
end Expr
