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
import WFC.Ch4_Operators


inductive Pair where
| zero -- Zero is considered an improper pair.
| pair (a b: Pair)


/-
  These instances allow us to denote `Pair.zero` as `()`, and
  `Pair.pair a b` as `(a, b)`.
-/
instance Pair.coeZero: CoeOut Unit Pair where
  coe := fun _ => Pair.zero

instance Pair.coeId: CoeOut Pair Pair where
  coe := id

instance Pair.coePair
  [CoeOut A Pair]
  [CoeOut B Pair]
:
  CoeOut (A × B) Pair
where
  coe := fun ⟨a, b⟩ => Pair.pair a b

/-
  This instance allows chaining other coercions, like one from
  `Nat` to `Pair` below. I feel like I'm breaking some unwritten
  rules of Lean with this one, but it works AFAICT.
-/
instance Pair.coeOutCoe [Coe A Pair]: CoeOut A Pair where
  coe := fun p => p


namespace Pair
  def eq: l0 = l1 → r0 = r1 → pair l0 r0 = pair l1 r1
  | rfl, rfl => rfl
  
  /-
    `Pair.zero` encodes the number zero, while `Pair.pair n zero`
    encodes the successor of `n`.
  -/
  def IsNatEncoding: Set Pair
  | zero => True
  | pair a b => (IsNatEncoding a) ∧ b = zero
  
  def NatEncoding := { p // IsNatEncoding p }
  
  
  def fromNat: Nat → Pair
  | Nat.zero => Pair.zero
  | Nat.succ n => Pair.pair (fromNat n) zero
  
  instance fromNat.inst: Coe Nat Pair := ⟨fromNat⟩
  
  def depth: Pair → Nat
  | zero => 0
  | pair a b => Nat.succ (max a.depth b.depth)
  
  
  /-
    `Pair.zero` encodes the empty list, while
    
        Pair.pair head tailEncoding
    
    encodes the list
    
        [ head, ...tail ] \,,
    
    where `tail` is the list encoded by `tailEncoding`.
  -/
  def arrayLength: Pair → Nat
  | zero => 0
  | pair _ b => Nat.succ b.arrayLength
  
  def arrayAt (p: Pair) (n: Nat): Option Pair :=
    match p, n with
    | zero, _ => none
    | pair head _tail, Nat.zero => head
    | pair _head tail, Nat.succ pred => tail.arrayAt pred
  
  
  def arrayLast (head tail: Pair): Pair :=
    match tail with
    | zero => head
    | pair tailHead tailTail => tailHead.arrayLast tailTail
  
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
  def I: (op: Op) → (args: pairSignature.Args op Pair) → Set Pair
    | Op.zero => fun _ p => p = Pair.zero
    | Op.pair => fun args p =>
        ∃ (a: ↑(args ArityTwo.zth))
          (b: ↑(args ArityTwo.fst))
        ,
          p = Pair.pair a b
  
  theorem I.isMonotonic
    (op: Op)
    (args0 args1: pairSignature.Args op Pair)
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

-- The salgebra of pairs.
@[reducible] def pairSalgebra: Salgebra pairSignature :=
  ⟨Pair, pairSalgebra.I, pairSalgebra.I.isMonotonic⟩


/-
  `fn.pairCallJust arg` is the triset of pairs `b` such that
  `(arg, b)` is in `fn`.
  
  You can think of `fn` as a set of input-output pairs representing
  a function `f: Pair → Set3 Pair`.
-/
def Set3.pairCallJust
  (fn: Set3 Pair)
  (arg: Pair)
:
  Set3 Pair
:= {
  defMem := fun p => fn.defMem (Pair.pair arg p)
  posMem := fun p => fn.posMem (Pair.pair arg p)
  defLePos := fun _ pInDef => pInDef.toPos
}

def Set3.PairMem
  (s e: Set3 Pair)
:
  Prop
:=
  ∃ i: Pair, s.pairCallJust i = e

instance Set3.pairInstMem:
  Membership (Set3 Pair) (Set3 Pair)
:=
  ⟨Set3.PairMem⟩
