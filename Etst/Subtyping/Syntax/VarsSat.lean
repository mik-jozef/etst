/-
  Defines `freeVars`, a function that computes the free variables
  of an expression.
-/

import Etst.WFC.Ch1_ExprDefList

namespace Etst


abbrev Expr.VarsSat (expr: Expr E) (P: Nat → Prop): Prop :=
  ∀ x ∈ expr.UsesVar, P x

abbrev Expr.VarsLt (expr: Expr E) (bound: Nat): Prop :=
  expr.VarsSat (· < bound)

namespace Expr
  instance varsSat
    (expr: Expr E)
    (P: Nat → Prop)
    [DecidablePred P]
  :
    Decidable (expr.VarsSat P)
  :=
    match expr with
    | .var _ xV =>
      if h: P xV then
        .isTrue (fun x (hx: x = xV) => hx.symm ▸ h)
      else
        .isFalse (fun hAll => h (hAll xV rfl))
    | .bvar _ => .isTrue (fun _ h => h.elim)
    | .null => .isTrue (fun _ h => h.elim)
    | .pair left rite =>
      match varsSat left P, varsSat rite P with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll => hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR => .isFalse (fun hAll => hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .ir left rite =>
      match varsSat left P, varsSat rite P with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll => hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR => .isFalse (fun hAll => hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .condFull body =>
      match varsSat body P with
      | .isTrue h => .isTrue fun x isUsed => h x isUsed
      | .isFalse h => .isFalse fun hFull => h fun x isUsed => hFull x isUsed
    | .compl expr => varsSat expr P
    | .arbIr expr => varsSat expr P

end Expr
