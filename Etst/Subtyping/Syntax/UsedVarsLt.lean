/-
  Defines `freeVars`, a function that computes the free variables
  of an expression.
-/

import Etst.WFC.Ch4_PairSalgebra

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
    (expr: Expr E pairSignature)
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
    | .op pairSignature.Op.null _ => .isTrue nofun
    | .op pairSignature.Op.pair args =>
      let freeVarsZth := usedVarsLt (args ArityTwo.zth) bound
      let freeVarsFst := usedVarsLt (args ArityTwo.fst) bound
      match freeVarsZth, freeVarsFst with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, ArityTwo.zth, isUsed⟩ => freeVarsZth ⟨x, isUsed⟩
          | ⟨x, ArityTwo.fst, isUsed⟩ => freeVarsFst ⟨x, isUsed⟩
    |
      .op pairSignature.Op.condSome args =>
      let freeVarsArg := usedVarsLt (args ArityOne.zth) bound
      match freeVarsArg with
      | .none => .none
      | .isTrue freeVarsArg =>
        .isTrue fun
          | ⟨x, ArityOne.zth, isUsed⟩ => freeVarsArg ⟨x, isUsed⟩
    |
      .op pairSignature.Op.condFull args =>
      let freeVarsArg := usedVarsLt (args ArityOne.zth) bound
      match freeVarsArg with
      | .none => .none
      | .isTrue freeVarsArg =>
        .isTrue fun
          | ⟨x, ArityOne.zth, isUsed⟩ => freeVarsArg ⟨x, isUsed⟩
    |
      .op pairSignature.Op.un args =>
      let freeVarsZth := usedVarsLt (args ArityTwo.zth) bound
      let freeVarsFst := usedVarsLt (args ArityTwo.fst) bound
      match freeVarsZth, freeVarsFst with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, ArityTwo.zth, isUsed⟩ => freeVarsZth ⟨x, isUsed⟩
          | ⟨x, ArityTwo.fst, isUsed⟩ => freeVarsFst ⟨x, isUsed⟩
    |
      .op pairSignature.Op.ir args =>
      let freeVarsZth := usedVarsLt (args ArityTwo.zth) bound
      let freeVarsFst := usedVarsLt (args ArityTwo.fst) bound
      match freeVarsZth, freeVarsFst with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, ArityTwo.zth, isUsed⟩ => freeVarsZth ⟨x, isUsed⟩
          | ⟨x, ArityTwo.fst, isUsed⟩ => freeVarsFst ⟨x, isUsed⟩
    |
      .compl expr => usedVarsLt expr bound
    | .arbUn expr => usedVarsLt expr bound
    | .arbIr expr => usedVarsLt expr bound
  
end Pair
