import Mathlib.Order.MinMax

import Utils.BasicUtils


-- A pair is a full binary tree.
inductive Pair where
| zero -- Zero is considered an improper pair.
| pair (a b: Pair)

-- Does not work recursively, and the latter
-- also with match expressions.
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
