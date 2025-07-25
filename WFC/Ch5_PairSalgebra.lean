/-
  Here we define a particular salgebra of special interest.
  Its carrier type is Pair, which is inductively defined as
  either zero (called the improper pair) or a pair of pairs.
  
  The pair signature consists of two operations on pairs, the constant
  `zero` and the binary function `pair`. Additionally, there are the
  set theoretic union and intersection, and two conditional operators,
  yielding the full triset iff the argument is nonempty, resp. full.
  
  This simple salgebra allows expressing/defining a wide range
  mathematical objects and concepts, and seems expressible enough
  for general mathematics.
  
  Notes:
  - In the appendix 1 (WIP), it is shown (TBD) that this salgebra is
    equivalent to the salgebra of natural numbers (with zero,
    successor, addition, and multiplication) under a standard
    correspondence between pairs and naturals.
  - The conditional operators are dual to each other. At least one
    of them is necessary for the sake of expressivity, and `condSome`
    seems to be the more useful one. However, both are included out
    of suspicion that the latter might be useful for dealing with
    negation of conditionals, since it gives us a kind of de-Morgan's
    laws for conditionals, that is:
    
      ~(condSome expr) = condFull (cpl expr)
      ~(condFull expr) = condSome (cpl expr)
    
    If not for much else, maybe this other conditional has use
    for representing intermediate forms of expressions while type
    checking. If this suspicion turns out to be false, I would not
    mind removing `condFull` from the signature.
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
  protected def eq: l0 = l1 → r0 = r1 → pair l0 r0 = pair l1 r1
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
  -- If inhabited, then any, else empty.
| condSome
  -- If full, then any, else empty.
| condFull
| un
| ir

def pairSignature.Params: Op → Type
| Op.zero => ArityZero
| Op.pair => ArityTwo
| Op.condSome => ArityOne
| Op.condFull => ArityOne
| Op.un => ArityTwo
| Op.ir => ArityTwo

def pairSignature: Signature := {
  Op := pairSignature.Op,
  Params := pairSignature.Params,
}


def Set.Full (t: Set T): Prop := ∀ x: T, x ∈ t

namespace pairSalgebra
  open pairSignature
  
  /-
    The interpretation function for the pair signature.
    Recall that the interpretation accepts and returns
    sets of elements of the carrier type.
    
    I(Op.zero) = { Pair.zero }
    I(Op.pair, arg0, arg1) = { Pair.pair a b | a ∈ arg0, b ∈ arg1 }
    I(Op.cond, arg0) = { p | ∃ a ∈ arg0 }
  -/
  def I: (op: Op) → (args: pairSignature.Args op Pair) → Set Pair
    | Op.zero, _, p => p = Pair.zero
    | Op.pair, args, p =>
        ∃ (a: ↑(args ArityTwo.zth))
          (b: ↑(args ArityTwo.fst))
        ,
          p = Pair.pair a b
    | Op.condSome, args, _ => (args ArityOne.zth).Nonempty
    | Op.condFull, args, _ => (args ArityOne.zth).Full
    | Op.un, args, p =>
        args ArityTwo.zth p ∨ args ArityTwo.fst p
    | Op.ir, args, p =>
        args ArityTwo.zth p ∧ args ArityTwo.fst p
  
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
      | Op.condSome =>
        fun _ ⟨p, inArg⟩ => ⟨p, le ArityOne.zth inArg⟩
      | Op.condFull =>
        fun _ inArg p => le ArityOne.zth (inArg p)
      | Op.un =>
        fun _ pInArgs0 =>
          pInArgs0.elim
            (fun pInArgs0 => Or.inl (le ArityTwo.zth pInArgs0))
            (fun pInArgs0 => Or.inr (le ArityTwo.fst pInArgs0))
      | Op.ir =>
        fun _ ⟨inL, inR⟩ => ⟨
          le ArityTwo.zth inL,
          le ArityTwo.fst inR,
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


noncomputable abbrev DefList.pairWfm
  (dl: DefList pairSignature)
:
  Valuation Pair
:=
  dl.wellFoundedModel pairSalgebra

noncomputable abbrev DefList.pairExprInterp
  (dl: DefList pairSignature)
:=
  dl.exprInterp pairSalgebra
