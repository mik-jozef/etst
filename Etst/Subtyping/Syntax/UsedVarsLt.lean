/-
  Defines `freeVars`, a function that computes the free variables
  of an expression.
-/

import Etst.WFC.Ch3_WellFoundedModel

namespace Etst


inductive Witness (P: Prop) where
| none
| isTrue (val: P)

def Witness.toBool: Witness T → Bool
| none .. => Bool.false
| isTrue .. => Bool.true

instance (T: Prop): ToString (Witness T) where
  toString
    | .none .. => "fols"
    | .isTrue .. => "true"


namespace Pair
  def usedVarsLt
    (expr: Expr E)
    (bound: Nat)
  :
    Witness (∀ x: expr.UsesVar, x.val < bound)
  :=
    match expr with
    | .var _ xV =>
      if hBLe: bound ≤ xV
        then .none
        else .isTrue fun ⟨x, eq⟩ =>
          show x < bound from
          eq ▸ Nat.lt_of_not_le hBLe
    | .bvar _ => .isTrue nofun
    | .null => .isTrue nofun
    | .pair left rite =>
      match usedVarsLt left bound, usedVarsLt rite bound with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, Or.inl isUsed⟩ => freeVarsZth ⟨x, isUsed⟩
          | ⟨x, Or.inr isUsed⟩ => freeVarsFst ⟨x, isUsed⟩
    | .ir left rite =>
      match usedVarsLt left bound, usedVarsLt rite bound with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, Or.inl isUsed⟩ => freeVarsZth ⟨x, isUsed⟩
          | ⟨x, Or.inr isUsed⟩ => freeVarsFst ⟨x, isUsed⟩
    |
      .condFull body =>
      match usedVarsLt body bound with
      | .none => .none
      | .isTrue freeVarsArg =>
        .isTrue fun ⟨x, isUsed⟩ => freeVarsArg ⟨x, isUsed⟩
    |
      .compl expr => usedVarsLt expr bound
    | .arbIr expr => usedVarsLt expr bound
  
end Pair
