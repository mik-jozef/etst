import Utils
import Mathlib.Order.MinMax

-- Ehhhm, should I rather call them binary trees?
inductive Pair where
| zero: Pair -- Zero is considered an improper pair.
| pair (a b: Pair): Pair

def decideEq: (a b: Pair) → Decidable (a = b)
| Pair.zero, Pair.zero => isTrue rfl
| Pair.zero, Pair.pair _ _ => isFalse (fun nope => Pair.noConfusion nope)
| Pair.pair _ _, Pair.zero => isFalse (fun nope => Pair.noConfusion nope)
| Pair.pair aA aB, Pair.pair bA bB =>
  let eqA := decideEq aA bA
  let eqB := decideEq aB bB
  
  match eqA, eqB with
  | isTrue aEq, isTrue bEq => isTrue (congr (congr rfl aEq) bEq)
  | isFalse aNeq, _ =>
    isFalse
      (fun nope => (Pair.noConfusion nope fun aEq _ => aNeq aEq))
  | _, isFalse bNeq =>
    isFalse
      (fun nope => (Pair.noConfusion nope fun _ bEq => bNeq bEq))

instance Pair.decidableEq: DecidableEq Pair := decideEq
      

namespace Pair
  def fromNat: Nat → Pair
  | Nat.zero => Pair.zero
  | Nat.succ n => Pair.pair (fromNat n) Pair.zero
  
  def depth: Pair → Nat
  | zero => 0
  | pair a b => Nat.succ (max a.depth b.depth)
  
  
  def fromNat.injEq
    (eq: fromNat n = fromNat m)
  :
    n = m
  :=
    match n, m with
    | Nat.zero, Nat.zero => rfl
    | Nat.zero, Nat.succ _ => Pair.noConfusion eq
    | Nat.succ _, Nat.zero => Pair.noConfusion eq
    | Nat.succ _nPred, Nat.succ _mPred =>
      let eqFromPred :=
        Pair.noConfusion eq fun predEq _ => predEq
      
      congrArg Nat.succ (fromNat.injEq eqFromPred)
  
  def fromNat.injNeq:
    n ≠ m → fromNat n ≠ fromNat m
  :=
    injEq.contra
  
  
  def depthSuccLeL (a b: Pair):
    Nat.succ a.depth ≤ (pair a b).depth
  :=
    Nat.succ_le_succ (Nat.le_max_left a.depth b.depth)
  
  def depthSuccLeR (a b: Pair):
    Nat.succ b.depth ≤ (pair a b).depth
  :=
    Nat.succ_le_succ (Nat.le_max_right a.depth b.depth)
  
  
  def depthLeL (a b: Pair):
    a.depth ≤ (pair a b).depth
  :=
    Nat.le_of_succ_le (depthSuccLeL a b)
  
  def depthLeR (a b: Pair):
    b.depth ≤ (pair a b).depth
  :=
    Nat.le_of_succ_le (depthSuccLeR a b)
  
  
  def depthLtL (a b: Pair):
    a.depth < (pair a b).depth
  :=
    depthSuccLeL a b
  
  def depthLtR (a b: Pair):
    b.depth < (pair a b).depth
  :=
    depthSuccLeR a b
  
  def depth.casesEq (a b: Pair):
    Or
      (And
        ((pair a b).depth = Nat.succ a.depth)
        (b.depth ≤ a.depth))
      (And
        ((pair a b).depth = Nat.succ b.depth)
        (a.depth < b.depth))
  :=
    (max_cases a.depth b.depth).elim
      (fun ⟨eq, le⟩ => Or.inl (And.intro (congr rfl eq) le))
      (fun ⟨eq, lt⟩ => Or.inr (And.intro (congr rfl eq) lt))
  
  
  def depth.leZth (aA aB bA bB: Pair):
    (pair aA bA).depth
      <
    (pair (pair aA aB) (pair bA bB)).depth
  :=
    let leSA := Pair.depthSuccLeL aA aB
    let leSB := Pair.depthSuccLeL bA bB
    (Pair.depth.casesEq aA bA).elim
      (fun ⟨eq, _⟩ => eq ▸ (leSA.trans_lt (Pair.depthLtL _ _)))
      (fun ⟨eq, _⟩ => eq ▸ (leSB.trans_lt (Pair.depthLtR _ _)))
  
  def depth.leZthFst (aA aB bA bB: Pair):
    (pair aA bB).depth
      <
    (pair (pair aA aB) (pair bA bB)).depth
  :=
    let leSA := Pair.depthSuccLeL aA aB
    let leSB := Pair.depthSuccLeR bA bB
    (Pair.depth.casesEq aA bB).elim
      (fun ⟨eq, _⟩ => eq ▸ (leSA.trans_lt (Pair.depthLtL _ _)))
      (fun ⟨eq, _⟩ => eq ▸ (leSB.trans_lt (Pair.depthLtR _ _)))
  
  def depth.zeroEq: depth Pair.zero = 0 := rfl
  
  def depth.eqZeroOfEqZero
    (eqZero: depth p = 0)
  :
    p = zero
  :=
    match p with
    | zero => rfl
    | pair _ _ => Nat.noConfusion eqZero
  
  
  def depth.eqL
    (ba: b.depth ≤ a.depth)
  :
    (pair a b).depth = Nat.succ a.depth
  :=
    congr rfl (max_eq_iff.mpr (Or.inl (And.intro rfl ba)))
  
  def depth.eqR
    (ab: a.depth ≤ b.depth)
  :
    (pair a b).depth = Nat.succ b.depth
  :=
    congr rfl (max_eq_iff.mpr (Or.inr (And.intro rfl ab)))
  
  
  def IsNatEncoding: Set Pair
  | zero => True
  | pair a b => (IsNatEncoding a) ∧ b = zero
  
  def NatEncoding := { p // IsNatEncoding p }
  
  
  def fromNat.isNatEncoding (n: Nat):
    IsNatEncoding (fromNat n)
  :=
    match n with
    | Nat.zero => trivial
    | Nat.succ pred => And.intro (isNatEncoding pred) rfl
  
  def fromNat.depthEq: (n: Nat) → (Pair.fromNat n).depth = n
  | Nat.zero => rfl
  | Nat.succ pred =>
    (depth.casesEq (fromNat pred) zero).elim
      (fun ⟨eq, _⟩ =>
        eq ▸ congr rfl (depthEq pred))
      (fun ⟨_, ltZero⟩ =>
        False.elim (Nat.not_lt_zero _ ltZero))
  
  
  def depth.nat.eqSuccDepthPred
    {a b: Pair}
    (isNat: IsNatEncoding (pair a b))
  :
    depth (pair a b)
      =
    Nat.succ (depth a)
  :=
    (depth.casesEq a b).elim
      (fun ⟨eq, _⟩ => eq)
      (fun ⟨_, le⟩ =>
        False.elim (Nat.not_lt_zero _ (isNat.right ▸ le)))
  
  def depth.nat.injEq
    (isNatA: IsNatEncoding a)
    (isNatB: IsNatEncoding b)
    (eq: depth a = depth b)
  :
    a = b
  :=
    match a, b with
    | zero, zero => rfl
    | zero, pair bA bB =>
      let eqL: 0 = depth (pair bA bB) :=
        depth.zeroEq.symm.trans eq
      let eqR := depth.nat.eqSuccDepthPred isNatB
      
      Nat.noConfusion (eqL.trans eqR)
    | pair aA aB, zero =>
      let eqL: 0 = depth (pair aA aB) :=
        depth.zeroEq.symm.trans eq.symm
      let eqR := depth.nat.eqSuccDepthPred isNatA
      
      Nat.noConfusion (eqL.trans eqR)
    | pair aA aB, pair bA bB =>
      let eqPredSucc: Nat.succ (depth aA) = Nat.succ (depth bA) :=
        (depth.nat.eqSuccDepthPred isNatA).symm.trans
          (eq.trans (depth.nat.eqSuccDepthPred isNatB))
      let eqPred: depth aA = depth bA :=
        Nat.noConfusion eqPredSucc id
      let eqA: aA = bA :=
        depth.nat.injEq isNatA.left isNatB.left eqPred
      let eqB: aB = bB :=
        isNatA.right.trans isNatB.right.symm
      
      congr (congr rfl eqA) eqB
  
  def depth.nat.injNeq
    (isNatA: IsNatEncoding a)
    (isNatB: IsNatEncoding b)
    (neq: a ≠ b)
  :
    depth a ≠ depth b
  :=
    (depth.nat.injEq isNatA isNatB).contra neq
  
  
  def arrayLength: Pair → Nat
  | zero => 0
  | pair _ b => Nat.succ b.arrayLength
  
  def arrayLength.eqSuccTail (a b: Pair):
    (pair a b).arrayLength = Nat.succ b.arrayLength
  :=
    rfl
  
  def arrayLength.ltTail (a b: Pair):
    b.arrayLength < (pair a b).arrayLength
  :=
    Nat.lt_succ_self b.arrayLength
  
  def arrayLength.ltOfLtTail
    (ab: tailA.arrayLength < tailB.arrayLength)
    (headA headB: Pair)
  :
    (pair headA tailA).arrayLength < (pair headB tailB).arrayLength
  :=
    Nat.succ_lt_succ ab
  
  def arrayLength.leOfLeTail
    (ab: tailA.arrayLength ≤ tailB.arrayLength)
    (headA headB: Pair)
  :
    (pair headA tailA).arrayLength ≤ (pair headB tailB).arrayLength
  :=
    Nat.succ_le_succ ab
  
  def arrayLength.eqOfEqTail
    (ab: tailA.arrayLength = tailB.arrayLength)
    (headA headB: Pair)
  :
    (pair headA tailA).arrayLength = (pair headB tailB).arrayLength
  :=
    by unfold arrayLength; exact congr rfl ab
  
  
  def arrayAt (p: Pair) (n: Nat): Option Pair :=
    match p, n with
    | zero, _ => none
    | pair head _tail, Nat.zero => head
    | pair _head tail, Nat.succ pred => tail.arrayAt pred
  
  def arrayAt.tailEq
    (eqAt: (pair head tail).arrayAt (pair n zero).depth = p)
  :
    tail.arrayAt n.depth = p
  :=
    let zeroLe: zero.depth ≤ n.depth := (Nat.zero_le n.depth)
    
    show (pair head tail).arrayAt (depth n).succ = p from
      (depth.eqL zeroLe) ▸ eqAt
  
  def arrayAt.consEq
    (eqAt: tail.arrayAt n.depth = p)
    (head: Pair)
  :
    (pair head tail).arrayAt (pair n zero).depth = p
  :=
    let zeroLe: zero.depth ≤ n.depth := (Nat.zero_le n.depth)
    
    (depth.eqL zeroLe) ▸ eqAt
  
  def arrayAt.nopeNoneOfWithinBounds
    {arr: Pair}
    (withinBounds: n < arr.arrayLength)
    (eqNone: arr.arrayAt n = none)
  :
    P
  :=
    match arr, n with
    | zero, _ => False.elim (Nat.not_lt_zero _ withinBounds)
    | pair _ tail, Nat.succ nPred =>
      let nPredWithinBounds:
        nPred < tail.arrayLength
      :=
        Nat.lt_of_succ_lt_succ withinBounds
      
      nopeNoneOfWithinBounds nPredWithinBounds eqNone
  
  
  def arrayLast (head tail: Pair): Pair :=
    match tail with
    | zero => head
    | pair tailHead tailTail => tailHead.arrayLast tailTail
  
  def arrayUpToLast (head tail: Pair): Pair :=
    match tail with
    | zero => zero
    | pair tailHead tailTail =>
      pair head (tailHead.arrayUpToLast tailTail)
  
  def arrayUpToLast.lengthEq
    (head tail: Pair)
  :
    (head.arrayUpToLast tail).arrayLength = tail.arrayLength
  :=
    match tail with
    | zero => rfl
    | pair tailHead tailTail =>
      let ih := lengthEq tailHead tailTail
      
      arrayLength.eqOfEqTail
        ih head (tailHead.arrayUpToLast tailTail)
  
  def arrayUpToLast.lengthLt
    (head tail: Pair)
  :
    (head.arrayUpToLast tail).arrayLength
      <
    (pair head tail).arrayLength
  :=
    match tail with
    | zero => Nat.zero_lt_succ _
    | pair tailHead tailTail =>
      let ih := lengthLt tailHead tailTail
      
      arrayLength.ltOfLtTail ih head (tailHead.arrayUpToLast tailTail)
end Pair
