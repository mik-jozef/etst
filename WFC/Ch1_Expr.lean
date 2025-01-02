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
  
  Variables are of type `Var`. The arguments of an operator `op`
  are indexed by the type `sig.Params op`.
-/
inductive Expr
  (Var: Type*)
  (sig: Signature)
where
| var (x: Var)
| op (op: sig.Op) (args: sig.Params op → Expr Var sig)
| cpl (expr: Expr Var sig)
| arbUn (x: Var) (body: Expr Var sig)
| arbIr (x: Var) (body: Expr Var sig)

namespace Expr
  instance coeVar: Coe Var (Expr Var s) where
    coe := fun n => Expr.var n
  
  instance exprOfNat (n: Nat): OfNat (Expr Nat s) n where
    ofNat := Expr.var n
  
  /-
    The set of free variables of `expr`, given a set of bound
    variables.
  -/
  def IsFreeVar
    (expr: Expr Var sig)
    (boundVars: Set Var)
  :
    Set Var
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
  def IsPositive: Expr Var sig → (boundVars: Set Var) → Prop
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
  noncomputable def sizeOf: Expr Var sig → Ordinal.{0}
  | Expr.var _ => 0
  | Expr.op _ args =>
    iSup (fun arg => (args arg).sizeOf) + 1
  | Expr.cpl expr => expr.sizeOf + 1
  | Expr.arbUn _ body => body.sizeOf + 1
  | Expr.arbIr _ body => body.sizeOf + 1
end Expr
