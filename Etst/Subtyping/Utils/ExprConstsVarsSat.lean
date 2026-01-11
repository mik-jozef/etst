/-
  Defines `constsSat`, a function that checks if all constants
  of an expression satisfy a computable predicate.
-/

import Etst.WFC.Ch1_ExprDefList

namespace Etst

def Expr.UsesVar (expr: Expr E): Set Nat :=
  fun x =>
    match expr with
      | const _ _ => False
      | var v => x = v
      | null => False
      | pair left rite => left.UsesVar x ∨ rite.UsesVar x
      | ir left rite => left.UsesVar x ∨ rite.UsesVar x
      | condFull body => body.UsesVar x
      | compl body => body.UsesVar x
      | arbIr body => body.UsesVar x


abbrev Expr.ConstsSat (expr: Expr E) (P: Nat → Prop): Prop :=
  ∀ x ∈ expr.UsesConst, P x

abbrev Expr.ConstsLt (expr: Expr E) (bound: Nat): Prop :=
  expr.ConstsSat (· < bound)


abbrev Expr.VarsSat (expr: Expr E) (P: Nat → Prop): Prop :=
  ∀ x ∈ expr.UsesVar, P x


namespace Expr
  instance constsSat
    (expr: Expr E)
    (P: Nat → Prop)
    [DecidablePred P]
  :
    Decidable (expr.ConstsSat P)
  :=
    match expr with
    | .const _ xV =>
      if h: P xV then
        .isTrue (fun x (hx: x = xV) => hx.symm ▸ h)
      else
        .isFalse (fun hAll => h (hAll xV rfl))
    | .var _ => .isTrue (fun _ h => h.elim)
    | .null => .isTrue (fun _ h => h.elim)
    | .pair left rite =>
      match constsSat left P, constsSat rite P with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ =>
        .isFalse (fun hAll =>
          hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR =>
        .isFalse (fun hAll =>
          hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .ir left rite =>
      match constsSat left P, constsSat rite P with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll =>
        hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR =>
        .isFalse (fun hAll =>
          hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .condFull body =>
      match constsSat body P with
      | .isTrue h => .isTrue fun x isUsed => h x isUsed
      | .isFalse h => .isFalse fun hFull => h fun x isUsed => hFull x isUsed
    | .compl expr => constsSat expr P
    | .arbIr expr => constsSat expr P
  
  def varsSat
    (expr: Expr E)
    (P: Nat → Prop)
    [DecidablePred P]
  :
    Decidable (expr.VarsSat P)
  :=
    match expr with
    | .const _ _ => .isTrue (fun _ h => h.elim)
    | .var xV =>
      if h: P xV then
        .isTrue (fun x (hx: x = xV) => hx.symm ▸ h)
      else
        .isFalse (fun hAll => h (hAll xV rfl))
    | .null => .isTrue (fun _ h => h.elim)
    | .pair left rite =>
      match varsSat left P, varsSat rite P with
      | .isTrue hL, .isTrue hR =>
      .isTrue fun
        | x, Or.inl isUsed => hL x isUsed
        | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ =>
        .isFalse (fun hAll =>
          hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR =>
        .isFalse (fun hAll =>
          hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .ir left rite =>
      match varsSat left P, varsSat rite P with
      | .isTrue hL, .isTrue hR =>
      .isTrue fun
        | x, Or.inl isUsed => hL x isUsed
        | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ =>
        .isFalse (fun hAll =>
          hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR =>
        .isFalse (fun hAll =>
          hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .condFull body =>
      match varsSat body P with
      | .isTrue h => .isTrue fun x isUsed => h x isUsed
      | .isFalse h => .isFalse fun hFull => h fun x isUsed => hFull x isUsed
    | .compl expr => varsSat expr P
    | .arbIr expr => varsSat expr P
end Expr
