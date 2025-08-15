/-
  Defines `freeVars`, a function that computes the free variables
  of an expression.
-/

import old.Utils.Interpretation
import old.WFC.Ch5_PairSalgebra

inductive PosWitness (P: Prop) where
| none
| isTrue (val: P)

inductive NegWitness (P: Prop) where
| isFols (val: ¬P)
| none

-- Note: one could also want an ExactWitness type, but Mathlib
-- already has `Decidable` which is exactly that.

def PosWitness.toBool: PosWitness T → Bool
| none .. => Bool.false
| isTrue .. => Bool.true

def NegWitness.toBool: NegWitness T → Bool
| isFols .. => Bool.false
| none .. => Bool.true

instance (T: Prop): ToString (PosWitness T) where
  toString
    | .none .. => "fols"
    | .isTrue .. => "true"

instance (T: Prop): ToString (NegWitness T) where
  toString
    | .isFols .. => "fols"
    | .none .. => "true"


namespace Pair
  
  def freeVarsLt
    (expr: Expr pairSignature)
    (boundVars: List Nat := [])
    (bound: Nat)
  :
    PosWitness
      (∀ x: expr.IsFreeVar (fun x => x ∈ boundVars), x.val < bound)
  :=
    match expr with
    | .var xV =>
      if hIsB: xV ∈ boundVars
      then .isTrue fun ⟨_, eq, ninBound⟩ =>
        False.elim (ninBound (eq ▸ hIsB))
      else if hBLe: bound ≤ xV
      then .none
      else .isTrue fun ⟨x, eq, _⟩ => show
        x < bound
      from
        eq ▸ Nat.lt_of_not_le hBLe
    |
      .op pairSignature.Op.zero _ => .isTrue nofun
    |
      .op pairSignature.Op.pair args =>
      let freeVarsZth := freeVarsLt (args ArityTwo.zth) boundVars bound
      let freeVarsFst := freeVarsLt (args ArityTwo.fst) boundVars bound
      match freeVarsZth, freeVarsFst with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, ArityTwo.zth, isFree⟩ => freeVarsZth ⟨x, isFree⟩
          | ⟨x, ArityTwo.fst, isFree⟩ => freeVarsFst ⟨x, isFree⟩
    |
      .op pairSignature.Op.condSome args =>
      let freeVarsArg := freeVarsLt (args ArityOne.zth) boundVars bound
      match freeVarsArg with
      | .none => .none
      | .isTrue freeVarsArg =>
        .isTrue fun
          | ⟨x, ArityOne.zth, isFree⟩ => freeVarsArg ⟨x, isFree⟩
    |
      .op pairSignature.Op.condFull args =>
      let freeVarsArg := freeVarsLt (args ArityOne.zth) boundVars bound
      match freeVarsArg with
      | .none => .none
      | .isTrue freeVarsArg =>
        .isTrue fun
          | ⟨x, ArityOne.zth, isFree⟩ => freeVarsArg ⟨x, isFree⟩
    |
      .op pairSignature.Op.un args =>
      let freeVarsZth := freeVarsLt (args ArityTwo.zth) boundVars bound
      let freeVarsFst := freeVarsLt (args ArityTwo.fst) boundVars bound
      match freeVarsZth, freeVarsFst with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, ArityTwo.zth, isFree⟩ => freeVarsZth ⟨x, isFree⟩
          | ⟨x, ArityTwo.fst, isFree⟩ => freeVarsFst ⟨x, isFree⟩
    |
      .op pairSignature.Op.ir args =>
      let freeVarsZth := freeVarsLt (args ArityTwo.zth) boundVars bound
      let freeVarsFst := freeVarsLt (args ArityTwo.fst) boundVars bound
      match freeVarsZth, freeVarsFst with
      | .none, _ => .none
      | _, .none => .none
      | .isTrue freeVarsZth, .isTrue freeVarsFst =>
        .isTrue fun
          | ⟨x, ArityTwo.zth, isFree⟩ => freeVarsZth ⟨x, isFree⟩
          | ⟨x, ArityTwo.fst, isFree⟩ => freeVarsFst ⟨x, isFree⟩
    |
      .cpl expr =>
        match freeVarsLt expr boundVars bound with
        | .none => .none
        | .isTrue freeVars =>
          .isTrue fun ⟨x, isFree⟩ => freeVars ⟨x, isFree⟩
    |
      .arbUn xB expr =>
        match freeVarsLt expr (xB :: boundVars) bound with
        | .none => .none
        | .isTrue isFreeLt =>
          .isTrue fun ⟨x, isFree⟩ =>
            let isFree := Expr.IsFreeVar.arbUnUnfold isFree
            let ninBound inBound :=
              (List.mem_cons.mp inBound).elim
                (isFree.boundNotFree ∘ Or.inr)
                (isFree.boundNotFree ∘ Or.inl)
            isFreeLt ⟨x, isFree.toBoundsNin ninBound⟩
    |
      .arbIr xB expr =>
        match freeVarsLt expr (xB :: boundVars) bound with
        | .none => .none
        | .isTrue isFreeLt =>
          .isTrue fun ⟨x, isFree⟩ =>
            let isFree := Expr.IsFreeVar.arbIrUnfold isFree
            let ninBound inBound :=
              (List.mem_cons.mp inBound).elim
                (isFree.boundNotFree ∘ Or.inr)
                (isFree.boundNotFree ∘ Or.inl)
            isFreeLt ⟨x, isFree.toBoundsNin ninBound⟩
  
end Pair
