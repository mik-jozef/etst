/-
  Defines `freeVars`, a function that computes the free variables
  of an expression.
-/

import Etst.WFC.Ch3_WellFoundedModel

namespace Etst


abbrev Expr.VarsLt (expr: Expr E) (bound: Nat): Prop :=
  ∀ x ∈ expr.UsesVar, x < bound

namespace Expr
  instance varsLt
    (expr: Expr E)
    (bound: Nat)
  :
    Decidable (expr.VarsLt bound)
  :=
    match expr with
    | .var _ xV =>
      if h: xV < bound then
        .isTrue (fun x (hx: x = xV) => hx.symm ▸ h)
      else
        .isFalse (fun hAll => h (hAll xV rfl))
    | .bvar _ => .isTrue (fun _ h => h.elim)
    | .null => .isTrue (fun _ h => h.elim)
    | .pair left rite =>
      match varsLt left bound, varsLt rite bound with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll => hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR => .isFalse (fun hAll => hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .ir left rite =>
      match varsLt left bound, varsLt rite bound with
      | .isTrue hL, .isTrue hR =>
        .isTrue fun
          | x, Or.inl isUsed => hL x isUsed
          | x, Or.inr isUsed => hR x isUsed
      | .isFalse hL, _ => .isFalse (fun hAll => hL (fun x isUsed => hAll x (Or.inl isUsed)))
      | _, .isFalse hR => .isFalse (fun hAll => hR (fun x isUsed => hAll x (Or.inr isUsed)))
    | .condFull body =>
      match varsLt body bound with
      | .isTrue h => .isTrue fun x isUsed => h x isUsed
      | .isFalse h => .isFalse fun hFull => h fun x isUsed => hFull x isUsed
    | .compl expr => varsLt expr bound
    | .arbIr expr => varsLt expr bound
  
end Expr
