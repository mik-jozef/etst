import Etst.WFC.Ch2_Interpretation

namespace Etst


namespace Pair
  protected def eq: l0 = l1 → r0 = r1 → pair l0 r0 = pair l1 r1
  | rfl, rfl => rfl
  
  /-
    `Pair.null` encodes the number zero, while `Pair.pair n zero`
    encodes the successor of `n`.
  -/
  def IsNatEncoding: Set Pair
  | null => True
  | pair a b => (IsNatEncoding a) ∧ b = null
  
  def NatEncoding := { p // IsNatEncoding p }
  
  
  def fromNat: Nat → Pair
  | Nat.zero => Pair.null
  | Nat.succ n => Pair.pair (fromNat n) null
  
  instance fromNat.inst: Coe Nat Pair := ⟨fromNat⟩
  
  def depth: Pair → Nat
  | null => 0
  | pair a b => Nat.succ (max a.depth b.depth)
  
  
  /-
    `Pair.null` encodes the empty list, while
    
        Pair.pair head tailEncoding
    
    encodes the list
    
        [ head, ...tail ] \,,
    
    where `tail` is the list encoded by `tailEncoding`.
  -/
  def arrayLength: Pair → Nat
  | null => 0
  | pair _ b => Nat.succ b.arrayLength
  
  def arrayAt (p: Pair) (n: Nat): Option Pair :=
    match p, n with
    | null, _ => none
    | pair head _tail, Nat.zero => head
    | pair _head tail, Nat.succ pred => tail.arrayAt pred
  
  
  def arrayLast (head tail: Pair): Pair :=
    match tail with
    | null => head
    | pair tailHead tailTail => tailHead.arrayLast tailTail
  
  def arrayUpToLast (head tail: Pair): Pair :=
    match tail with
    | null => null
    | pair tailHead tailTail =>
      pair head (tailHead.arrayUpToLast tailTail)
  
  
  def fromNat_inj_eq
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
      
      congrArg Nat.succ (fromNat_inj_eq eqFromPred)
  
  def fromNat_inj_neq:
    n ≠ m → fromNat n ≠ fromNat m
  :=
    not_imp_not.mpr fromNat_inj_eq
  
  
  def depth_cases_eq (a b: Pair):
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
  
  def fromNat_depth_eq: (n: Nat) → (Pair.fromNat n).depth = n
  | Nat.zero => rfl
  | Nat.succ pred =>
    (depth_cases_eq (fromNat pred) null).elim
      (fun ⟨eq, _⟩ =>
        eq ▸ congr rfl (fromNat_depth_eq pred))
      (fun ⟨_, ltZero⟩ =>
        False.elim (Nat.not_lt_zero _ ltZero))
  
  
  def pairS3
    (s0 s1: Set3 Pair)
  :
    Set3 Pair
  := {
    defMem := { p | ∃ p0 ∈ s0.defMem, ∃ p1 ∈ s1.defMem, p = Pair.pair p0 p1 },
    posMem := { p | ∃ p0 ∈ s0.posMem, ∃ p1 ∈ s1.posMem, p = Pair.pair p0 p1 },
    defLePos := fun _ ⟨p0, p0InDef, ⟨p1, p1InDef, pEq⟩⟩ =>
      ⟨p0, s0.defLePos p0InDef, p1, s1.defLePos p1InDef, pEq⟩
  }
  
end Pair


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
