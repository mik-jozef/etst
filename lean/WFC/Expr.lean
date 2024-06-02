import Utils.BasicUtils


-- Thanks to answerers of https://proofassistants.stackexchange.com/q/1740
structure Signature where
  Op: Type u
  Params: Op → Type v


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
  instance: Coe Nat (Expr s) where
    coe := fun n => Expr.var n
  
  instance (n: Nat): OfNat (Expr s) n where
    ofNat := Expr.var n
  
  def any: Expr s := Expr.un 0 (Expr.cpl 0)
end Expr

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


inductive PosExpr (sig: Signature) where
| var (v: Nat)
| opApp (op: sig.Op) (args: sig.Params op → PosExpr sig)
| un (left: PosExpr sig) (rite: PosExpr sig)
| ir (left: PosExpr sig) (rite: PosExpr sig)
| ifThen (cond expr: PosExpr sig)
  -- Complementing a bound variable is OK.
| Un (x xc: Nat) (body: PosExpr sig)
| Ir (x xc: Nat) (body: PosExpr sig)

def PosExpr.toExpr
  (complements: Nat → Option Nat := fun _ => none)
:
  PosExpr sig → Expr sig

| PosExpr.var v =>
  match complements v with
  | none => Expr.var v
  | some v' => Expr.cpl (Expr.var v')

| PosExpr.opApp op args =>
    Expr.op op (fun p => (args p).toExpr complements)

| PosExpr.un left rite =>
    Expr.un (left.toExpr complements) (rite.toExpr complements)

| PosExpr.ir left rite =>
    Expr.ir (left.toExpr complements) (rite.toExpr complements)

| PosExpr.ifThen cond expr =>
    Expr.ifThen (cond.toExpr complements) (expr.toExpr complements)

| PosExpr.Un x xc body =>
    Expr.Un x (body.toExpr (fun v => if v = xc then x else complements v))

| PosExpr.Ir x xc body =>
    Expr.Ir x (body.toExpr (fun v => if v = xc then x else complements v))
