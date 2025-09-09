import Etst.WFC.Ch4_PairSalgebra

namespace Etst


namespace Pair
  
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
  
end Pair
