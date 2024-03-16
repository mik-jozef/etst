import Utils
import Mathlib.Order.MinMax

-- Ehhhm, should I rather call them binary trees?
inductive Pair where
| zero: Pair -- Zero is considered an improper pair.
| pair (a b: Pair): Pair

-- def Pair.Expr := _root_.Expr pairSignature

namespace Pair
  def fromNat: Nat → Pair
  | Nat.zero => Pair.zero
  | Nat.succ n => Pair.pair (fromNat n) Pair.zero
  
  def depth: Pair → Nat
  | zero => 0
  | pair a b => Nat.succ (max a.depth b.depth)
  
  
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
  
end Pair
