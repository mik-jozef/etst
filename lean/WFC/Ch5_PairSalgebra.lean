/-
  Here we define a particular salgebra of special interest.
  Its carrier type is Pair, which is inductively defined as
  either zero (called the improper pair) or a pair of pairs.
  
  The pair signature consists of two operations, the constant
  `zero` and the binary function `pair`. This simple salgebra
  allows expressing/defining a wide range mathematical objects
  and concepts.
-/

import Mathlib.Order.MinMax

import Utils.BasicUtils
import WFC.Ch3_Interpretation


inductive Pair where
| zero -- Zero is considered an improper pair.
| pair (a b: Pair)

-- Does not work recursively, and the latter also with match
-- expressions :(
--
-- instance Pair.coeEmpty: Coe Unit Pair where
--   coe := fun _ => Pair.zero
-- instance Pair.coePair: Coe (Pair × Pair) Pair where
--   coe := fun ⟨a, b⟩ => Pair.pair a b



namespace Pair
  def fromNat: Nat → Pair
  | Nat.zero => Pair.zero
  | Nat.succ n => Pair.pair (fromNat n) zero
  
  def fromNat.inst: Coe Nat Pair := ⟨fromNat⟩
  
  def depth: Pair → Nat
  | zero => 0
  | pair a b => Nat.succ (max a.depth b.depth)
  
  def IsNatEncoding: Set Pair
  | zero => True
  | pair a b => (IsNatEncoding a) ∧ b = zero
  
  def NatEncoding := { p // IsNatEncoding p }
  
  def arrayLength: Pair → Nat
  | zero => 0
  | pair _ b => Nat.succ b.arrayLength
  
  def arrayAt (p: Pair) (n: Nat): Option Pair :=
    match p, n with
    | zero, _ => none
    | pair head _tail, Nat.zero => head
    | pair _head tail, Nat.succ pred => tail.arrayAt pred
  
  
  def arrayUpToLast (head tail: Pair): Pair :=
    match tail with
    | zero => zero
    | pair tailHead tailTail =>
      pair head (tailHead.arrayUpToLast tailTail)
  
end Pair

inductive pairSignature.Op where
| zero
| pair

def pairSignature.Params: Op → Type
| Op.zero => ArityZero
| Op.pair => ArityTwo

def pairSignature: Signature := {
  Op := pairSignature.Op,
  Params := pairSignature.Params,
}


namespace pairSalgebra
  open pairSignature
  
  /-
    The interpretation function for the pair signature.
    Recall that the interpretation accepts and returns
    sets of elements of the carrier type.
    
    I(Op.zero) = { Pair.zero }
    I(Op.pair, arg0, arg1) = { Pair.pair a b | a ∈ arg0, b ∈ arg1 }
  -/
  def I: (op: Op) → (args: Args pairSignature op Pair) → Set Pair
    | Op.zero => fun _ p => p = Pair.zero
    | Op.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth))
          (b: ↑(args ArityTwo.fst))
        ,
          p = Pair.pair a b
  
  theorem I.isMonotonic
    (op: Op)
    (args0 args1: Args pairSignature op Pair)
    (le: ∀ param: Params op, args0 param ≤ args1 param)
  :
    I op args0 ≤ I op args1
  :=
    match op with
      | Op.zero => Preorder.le_refl _
      | Op.pair =>
          fun _ pInArgs0 =>
            pInArgs0.elim fun a bEx =>
              bEx.elim fun b nab => ⟨
                ⟨a.val, le ArityTwo.zth a.property⟩,
                ⟨⟨b.val, le ArityTwo.fst b.property⟩, nab⟩
              ⟩
end pairSalgebra

def pairSalgebra: Salgebra pairSignature :=
  ⟨Pair, pairSalgebra.I, pairSalgebra.I.isMonotonic⟩
