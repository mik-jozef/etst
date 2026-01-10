/-
  Defines `freeDefs`, a function that computes the free definitions
  of an expression.
-/

import Etst.WFC.Ch1_ExprDefList

namespace Etst


abbrev Expr.DefsSat (expr: Expr E) (P: Nat → Prop): Prop :=
  ∀ x ∈ expr.UsesDef, P x

abbrev Expr.DefsLt (expr: Expr E) (bound: Nat): Prop :=
  expr.DefsSat (· < bound)

namespace Expr
  instance defsSat
    (expr: Expr E)
    (P: Nat → Prop)
    [DecidablePred P]
  :
    Decidable (expr.DefsSat P)
  :=
    match expr with
    | .df _ xV =>
      if h: P xV then
        .isTrue (fun x (hx: x = xV) => hx.symm ▸ h)
      else
        .isFalse (fun hAll => h (hAll xV rfl))
    | .var _ => .isTrue (fun _ h => h.elim)
    | .null => .isTrue (fun _ h => h.elim)
    | .pair left rite =>
      match defsSat left P, defsSat rite P with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll => hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR => .isFalse (fun hAll => hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .ir left rite =>
      match defsSat left P, defsSat rite P with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll => hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR => .isFalse (fun hAll => hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .condFull body =>
      match defsSat body P with
      | .isTrue h => .isTrue fun x isUsed => h x isUsed
      | .isFalse h => .isFalse fun hFull => h fun x isUsed => hFull x isUsed
    | .compl expr => defsSat expr P
    | .arbIr expr => defsSat expr P

end Expr
