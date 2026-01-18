/-
  Defines `constsSat`, a function that checks if all constants
  of an expression satisfy a computable predicate.
-/

import Etst.WFC.Ch1_ExprDefList

namespace Etst

abbrev Expr.ConstsSat (expr: Expr E) (P: Nat → Prop): Prop :=
  ∀ x ∈ expr.UsesConst, P x

abbrev Expr.ConstsLt (expr: Expr E) (bound: Nat): Prop :=
  expr.ConstsSat (· < bound)

instance Expr.constsSat
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
      .isFalse (fun hSat => h (hSat xV rfl))
  | .var _ => .isTrue (fun _ h => h.elim)
  | .null => .isTrue (fun _ h => h.elim)
  | .pair left rite =>
    match constsSat left P, constsSat rite P with
    | .isTrue hL, .isTrue hR =>
      .isTrue fun
        | x, Or.inl isUsed => hL x isUsed
        | x, Or.inr isUsed => hR x isUsed
    | .isFalse hL, _ =>
      .isFalse (fun hSat =>
        hL (fun x isUsed => hSat x (Or.inl isUsed)))
    | _, .isFalse hR =>
      .isFalse (fun hSat =>
        hR (fun x isUsed => hSat x (Or.inr isUsed)))
  | .ir left rite =>
    match constsSat left P, constsSat rite P with
    | .isTrue hL, .isTrue hR =>
      .isTrue fun
        | x, Or.inl isUsed => hL x isUsed
        | x, Or.inr isUsed => hR x isUsed
    | .isFalse hL, _ => .isFalse (fun hSat =>
      hL (fun x isUsed => hSat x (Or.inl isUsed)))
    | _, .isFalse hR =>
      .isFalse (fun hSat =>
        hR (fun x isUsed => hSat x (Or.inr isUsed)))
  | .full body =>
    match constsSat body P with
    | .isTrue h => .isTrue fun x isUsed => h x isUsed
    | .isFalse h =>
      .isFalse fun hSat => h fun x isUsed => hSat x isUsed
  | .compl expr => constsSat expr P
  | .arbIr expr => constsSat expr P


def Expr.UsesFreeVar (expr: Expr E): Set Nat :=
  fun x =>
    match expr with
      | const _ _ => False
      | var v => x = v
      | null => False
      | pair left rite => left.UsesFreeVar x ∨ rite.UsesFreeVar x
      | ir left rite => left.UsesFreeVar x ∨ rite.UsesFreeVar x
      | full body => body.UsesFreeVar x
      | compl body => body.UsesFreeVar x
      | arbIr body => body.UsesFreeVar (x + 1)

instance Expr.usesFreeVar
  (expr: Expr E)
  (x: Nat)
:
  Decidable (expr.UsesFreeVar x)
:=
  match expr with
  | .const _ _ => .isFalse (fun h => h.elim)
  | .var v =>
    if h: x = v then
      .isTrue h
    else
      .isFalse (fun hVar => h (hVar))
  | .null => .isFalse (fun h => h.elim)
  | .pair left rite =>
    match left.usesFreeVar x, rite.usesFreeVar x with
    | .isTrue hL, _ => .isTrue (Or.inl hL)
    | _, .isTrue hR => .isTrue (Or.inr hR)
    | .isFalse hL, .isFalse hR =>
      .isFalse (fun hVar =>
        match hVar with
        | Or.inl isUsed => hL isUsed
        | Or.inr isUsed => hR isUsed)
  | .ir left rite =>
    match left.usesFreeVar x, rite.usesFreeVar x with
    | .isTrue hL, _ => .isTrue (Or.inl hL)
    | _, .isTrue hR => .isTrue (Or.inr hR)
    | .isFalse hL, .isFalse hR =>
      .isFalse (fun hVar =>
        match hVar with
        | Or.inl isUsed => hL isUsed
        | Or.inr isUsed => hR isUsed)
  | .full body => body.usesFreeVar x
  | .compl expr => expr.usesFreeVar x
  | .arbIr expr => expr.usesFreeVar (x + 1)


abbrev Expr.FreeVarsSat (expr: Expr E) (P: Nat → Prop): Prop :=
  ∀ x ∈ expr.UsesFreeVar, P x

instance Expr.freeVarsSat
  (expr: Expr E)
  (P: Nat → Prop)
  [DecidablePred P]
:
  Decidable (expr.FreeVarsSat P)
:=
  match expr with
  | .const _ _ => .isTrue (fun _ h => h.elim)
  | .var xV =>
    if h: P xV then
      .isTrue (fun x (hx: x = xV) => hx.symm ▸ h)
    else
      .isFalse (fun hSat => h (hSat xV rfl))
  | .null => .isTrue (fun _ h => h.elim)
  | .pair left rite =>
    match freeVarsSat left P, freeVarsSat rite P with
    | .isTrue hL, .isTrue hR =>
    .isTrue fun
      | x, Or.inl isUsed => hL x isUsed
      | x, Or.inr isUsed => hR x isUsed
    | .isFalse hL, _ =>
      .isFalse (fun hSat =>
        hL (fun x isUsed => hSat x (Or.inl isUsed)))
    | _, .isFalse hR =>
      .isFalse (fun hSat =>
        hR (fun x isUsed => hSat x (Or.inr isUsed)))
  | .ir left rite =>
    match freeVarsSat left P, freeVarsSat rite P with
    | .isTrue hL, .isTrue hR =>
    .isTrue fun
      | x, Or.inl isUsed => hL x isUsed
      | x, Or.inr isUsed => hR x isUsed
    | .isFalse hL, _ =>
      .isFalse (fun hSat =>
        hL (fun x isUsed => hSat x (Or.inl isUsed)))
    | _, .isFalse hR =>
      .isFalse (fun hSat =>
        hR (fun x isUsed => hSat x (Or.inr isUsed)))
  | .full body =>
    match freeVarsSat body P with
    | .isTrue h => .isTrue fun x isUsed => h x isUsed
    | .isFalse h =>
      .isFalse fun hSat =>
        h fun x isUsed => hSat x isUsed
  | .compl expr => freeVarsSat expr P
  | .arbIr expr =>
    let P': Nat → Prop := fun
      | 0 => True
      | n + 1 => P n
    have: DecidablePred P' := fun
      | 0 => isTrue True.intro
      | n + 1 => inferInstanceAs (Decidable (P n))
    match freeVarsSat expr P' with
    | .isTrue h => .isTrue (fun x => h (x + 1))
    | .isFalse h =>
      .isFalse fun hSat =>
        h (fun
        | .zero, _ => trivial
        | x+1, isUsed => hSat x isUsed)
