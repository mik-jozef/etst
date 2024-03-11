import PairDictOrder

namespace Pair
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
      ((pair a b).depth = Nat.succ a.depth)
      ((pair a b).depth = Nat.succ b.depth)
  :=
    (max_cases a.depth b.depth).elim
      (fun ⟨eq, _⟩ => Or.inl (congr rfl eq))
      (fun ⟨eq, _⟩ => Or.inr (congr rfl eq))
  
  
  -- TODO depthDictOrder
end Pair
