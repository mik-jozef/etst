/-
  Defines the Cantor pairing function and its inverses.
  
  I figured these proofs by playing around in Desmos, and staring
  at the Wikipedia article and this answer:
  https://math.stackexchange.com/a/225422/
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

import WFC.Ch5_PairSalgebra


structure Nat.MarginDecomposition (base n margin: Nat) where
  tp: Nat -- Tipping point
  extra: Nat
  eq_n: base + tp = n
  margin_eq: margin = tp + extra

def Nat.decomposeMargin
  {base n margin: Nat}
  (base_le: base ≤ n)
  (n_le: n ≤ base + margin)
:
  MarginDecomposition base n margin
:= {
  tp := n - base
  extra := margin - (n - base)
  eq_n := by omega
  margin_eq := by omega
}

def Nat.sub_mul_self'
  (le: b ≤ a)
:
  (a - b) * (a - b) = a * a + b * b - 2 * a * b
:= by
  let ⟨n, eq⟩ := Nat.exists_eq_add_of_le' le
  rw [eq, Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.mul_add]
  rw [Nat.mul_add, Nat.add_mul]
  let eq0:
    n * n + n * b + (b * n + b * b) + b * b - (2 * n * b + 2 * b * b)
      =
    n * n + n * b + b * n + b * b + b * b - 2 * n * b - 2 * b * b
  := by omega
  let eq1:
    n * n + n * b + b * n + b * b + b * b
      =
    n * n + 2 * n * b + 2 * b * b
  := by linarith
  rw [eq0, eq1]
  omega

def Nat.triangle (n: Nat): Nat := n * (n + 1) / 2

def Nat.triangle_zero: triangle 0 = 0 := rfl
def Nat.triangle_one: triangle 1 = 1 := rfl

def Nat.triangle_zero_le
  (n: Nat)
:
  triangle 0 ≤ n
:=
  triangle_zero ▸ zero_le n

def Nat.triangle_mul_two
  (n: Nat)
:
  n * (n + 1) / 2 * 2 = n * (n + 1)
:=
  let ⟨k, evenOrOdd⟩ := Nat.even_or_odd' n
  evenOrOdd.elim
    (fun isEven => by
      rw [mul_comm n, isEven, mul_comm 2 k, ←mul_assoc]
      rw [Nat.mul_div_cancel _ zero_lt_two])
    (fun isOdd => by
      let eq: n * (n + 1) = n * (k + 1) * 2 := by
        conv => lhs; rhs; rw [isOdd]
        linarith
      rw [eq, Nat.mul_div_cancel _ zero_lt_two])

def Nat.triangle_add_eq_succ
  (n: Nat)
:
  triangle n + (n + 1) = triangle (n + 1)
:= by
  unfold triangle
  apply Nat.eq_of_mul_eq_mul_right zero_lt_two
  rw [Nat.add_mul, triangle_mul_two, triangle_mul_two]
  linarith

def Nat.triangle_succ_sub_eq
  (n: Nat)
:
  triangle (n + 1) - triangle n = n + 1
:= by
  unfold triangle
  apply Nat.eq_of_mul_eq_mul_right zero_lt_two
  rw [Nat.sub_mul, triangle_mul_two, triangle_mul_two]
  rw [add_mul, mul_add]
  omega

def Nat.pred_triangle_le_triangle:
  (n: Nat) →
  n.pred.triangle ≤ n.triangle
|
  0 => le_rfl
| n+1 => triangle_add_eq_succ n ▸ le_add_right _ _

def Nat.triangle_le_of_le
  (le: a ≤ b)
:
  triangle a ≤ triangle b
:=
  if h: a = b
  then h ▸ le_rfl
  else
    let le_pred := le_pred_of_lt (lt_of_le_of_ne le h)
    let ih := triangle_le_of_le le_pred
    ih.trans (pred_triangle_le_triangle b)

def Nat.le_triangle: (n: Nat) → n ≤ n.triangle
| 0 => zero_le _
| n+1 =>
  triangle_add_eq_succ n ▸
  Nat.add_le_add (le_triangle n) (Nat.le_add_left 1 n)

def Nat.lt_triangle
  (ne_zero: n ≠ 0)
  (ne_one: n ≠ 1)
:
  n < triangle n
:=
  match n with
  | 2 => by decide
  | nPred+2+1 =>
    let ih := lt_triangle (by simp) (by simp)
    triangle_add_eq_succ (nPred+2) ▸
    add_lt_add_of_lt_of_lt ih (by simp)

def Nat.triangle_eq_self
  (eq: triangle n = n)
:
  n = 0 ∨ n = 1
:=
  match n with
  | 0 => Or.inl rfl
  | 1 => Or.inr rfl
  | nPred+2 =>
    let lt := lt_triangle (n := nPred+2) (by simp) (by simp)
    False.elim (lt.ne eq.symm)

def Nat.pred_lt_of_triangle_not_le
  (not_le: ¬ triangle m ≤ n)
:
  m.pred < m
:=
  pred_lt fun eq => not_le (eq ▸ zero_le _)

-- Returns the greatest `i` such that `i.triangle ≤ n`.
-- Floor of the inverse of the triangle function.
def Nat.triangleIndex
  (n: Nat)
:
  Nat
:=
  iter n n
  where
    iter (n m: Nat) :=
      if h: triangle m ≤ n then
        m
      else
        have := pred_lt_of_triangle_not_le h
        iter n m.pred

def Nat.triangleIndex.iter_id_of_le
  (le: m.triangle ≤ n)
:
  iter n m = m
:= by
  unfold iter
  rw [dif_pos le]

def Nat.triangleIndex.iter_eq_prev_of_not_le
  (not_le: ¬ m.triangle ≤ n)
:
  iter n m = iter n m.pred
:= by
  conv => lhs; unfold iter
  rw [dif_neg not_le]

def Nat.triangleIndex.iter_le
  (n m: Nat)
:
  (iter n m).triangle ≤ n
:=
  if h: triangle m ≤ n
  then (iter_id_of_le h).symm ▸ h
  else
    have := pred_lt_of_triangle_not_le h
    iter_eq_prev_of_not_le h ▸
    iter_le n m.pred

def Nat.triangleIndex_le
  (n: Nat)
:
  n.triangleIndex.triangle ≤ n
:=
  triangleIndex.iter_le n n

def Nat.triangleIndex.lt_iter_succ
  (n m: Nat)
:
  m.triangle ≤ n ∨ n < (iter n m).succ.triangle
:=
  match m with
  | 0 => Or.inl (zero_le _)
  | mPred+1 =>
    Or.inrEm fun not_le => by
      rw [iter_eq_prev_of_not_le not_le, pred]
      match lt_iter_succ n mPred with
      | Or.inl pred_le =>
        rw [iter_id_of_le pred_le]
        exact lt_of_not_ge not_le
      | Or.inr n_lt =>
        exact n_lt

def Nat.triangleIndex.lt_succ
  (n: Nat)
:
  n < n.triangleIndex.succ.triangle
:=
  match lt_iter_succ n n with
  | Or.inl le =>
    match (triangle_eq_self (le.antisymm (le_triangle n))) with
    | Or.inl eq0 => by rw [eq0]; with_unfolding_all decide
    | Or.inr eq1 => by rw [eq1]; with_unfolding_all decide
  | Or.inr lt => lt


def Nat.mul_self_le_succ_mul_succ
  (n: Nat)
:
  n * n ≤ n.succ * n.succ
:=
  Nat.mul_le_mul (le_succ n) (le_succ n)

def Nat.sqrt_le_sqrt_add_left
  (n a: Nat)
:
  n.sqrt ≤ (a + n).sqrt
:=
  sqrt_le_sqrt (le_add_left n a)

def Nat.sqrt_le_sqrt_add_rite
  (n a: Nat)
:
  n.sqrt ≤ (n + a).sqrt
:=
  sqrt_le_sqrt (le_add_right n a)

def Nat.add_sqrt_le
  (a b: Nat)
:
  (a + b).sqrt ≤ a.sqrt + b.sqrt
:=
  let leA: a ≤ a.sqrt * a.sqrt + 2 * a.sqrt := by
    rw [two_mul, ←Nat.add_assoc]
    exact sqrt_le_add a
  
  let leB:
    b ≤ b.sqrt * b.sqrt + 2 * b.sqrt + 2 * a.sqrt * b.sqrt
  := by
    apply Nat.le_add_right_of_le
    rw [two_mul, ←Nat.add_assoc]
    exact sqrt_le_add b
  
  let eq:
    (a.sqrt + b.sqrt + 1) * (a.sqrt + b.sqrt + 1)
      =
    (a.sqrt * a.sqrt + 2 * a.sqrt) +
    (b.sqrt * b.sqrt + 2 * b.sqrt +
    2 * a.sqrt * b.sqrt) +
    1
  :=
    by linarith
  
  le_of_lt_succ
    (sqrt_lt.mpr
      (eq ▸ lt_add_one_of_le (Nat.add_le_add leA leB)))


-- The Cantor pairing function
-- https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function
def Nat.cantorPair (a b: Nat):Nat :=
  (a + b) * (a + b + 1) / 2 + b

def Nat.cantorPair.w (n: Nat): Nat :=
  ((8 * n + 1).sqrt - 1) / 2

def Nat.cantorPair.t (n: Nat): Nat :=
  w n * (w n + 1) / 2

def Nat.cantorFst (n: Nat): Nat := n - cantorPair.t n

def Nat.cantorZth (n: Nat): Nat :=
  cantorPair.w n - cantorFst n


def Nat.cantorPair.w_le: (n: Nat) → w n ≤ n
| 0 => le_rfl
| 1 =>
  let eq: w 1 = 1 := by with_unfolding_all rfl
  
  eq.symm ▸ le_rfl
| n+2 => by
  let eqA: (8 * 2 + 1).sqrt = 4 := by with_unfolding_all rfl
  
  unfold w
  apply Nat.div_le_of_le_mul
  apply Nat.sub_le_of_le_add
  rw [mul_add, add_assoc]
  apply le_trans (add_sqrt_le (8 * n) (8 * 2 + 1))
  rw [eqA, mul_add, two_mul 2, add_assoc, add_assoc]
  rw [add_comm 2 1, ←add_assoc, ←add_assoc]
  apply Nat.add_le_add_right
  apply Nat.le_of_lt_succ
  apply Nat.sqrt_lt.mpr
  
  have:
    (2 * n + 1).succ * (2 * n + 1).succ
      =
    4 * n * n + 8 * n + 4
  :=
    by rw [succ_eq_add_one]; linarith
  
  omega

def Nat.cantorFst_le (n: Nat): n.cantorFst ≤ n :=
  Nat.sub_le n _

def Nat.cantorZth_le (n: Nat): n.cantorZth ≤ n :=
  le_trans
    (Nat.sub_le (Nat.cantorPair.w n) _)
    (Nat.cantorPair.w_le n)


def Nat.cantorPair.w_eq_add.magic
  (a b extra: Nat)
:
  Nat
:=
  ((4 * (a + b) * (a + b + 1) + extra + 1).sqrt - 1) / 2

def Nat.cantorPair.w_eq_add.wab_eq
  (a b: Nat)
:
  w (a.cantorPair b) = magic a b (8 * b)
:= by
  let eq8: 8 = 2 * 4 := rfl
  
  unfold magic w cantorPair
  rw [mul_add, mul_comm, eq8, ←mul_assoc]
  rw [triangle_mul_two, mul_comm, ←mul_assoc]

def Nat.cantorPair.w_eq_add.ub_le_n:
  magic a b (8 * b) ≤ a + b
:=
  have:
    (4 * (a + b) * (a + b + 1) + 8 * b + 1).sqrt < 3 + 2 * (a + b)
  :=
    Nat.sqrt_lt.mpr (by linarith)
  
  by unfold magic; omega

def Nat.cantorPair.w_eq_add.n_le_lb:
  a + b ≤ magic a b 0
:=
  have:
    2 * (a + b) + 1 ≤ (4 * (a + b) * (a + b + 1) + 0 + 1).sqrt
  :=
    Nat.le_sqrt.mpr (by linarith)
  
  by unfold magic; omega

def Nat.cantorPair.w_eq_add:
  w (a.cantorPair b) = a + b
:=
  open w_eq_add in
  have:
    (4 * (a + b) * (a + b + 1) + 0 + 1).sqrt
      ≤
    (4 * (a + b) * (a + b + 1) + 8 * b + 1).sqrt
  :=
    sqrt_le_sqrt (by linarith)
  
  let le: magic a b 0 ≤ magic a b (8 * b) :=
    by unfold magic; omega
  
  wab_eq a b ▸
  le_antisymm ub_le_n (n_le_lb.trans le)

def Nat.cantorPair_surjective
  (n: Nat)
:
  ∃ a b, n = cantorPair a b
:=
  let i := n.triangleIndex
  let le := by
    apply le_of_lt_succ
    rw [succ_eq_add_one, add_assoc]
    rw [triangle_add_eq_succ n.triangleIndex]
    exact triangleIndex.lt_succ n
  
  let ⟨
    b,
    a,
    (eqN: i.triangle + b = n),
    marginEq,
  ⟩ :=
    decomposeMargin (margin := i) n.triangleIndex_le le
  
  let marginEq: i = a + b := Nat.add_comm b a ▸ marginEq
  
  ⟨a, b, by rw [marginEq] at eqN; exact eqN.symm⟩


def Nat.cantorPair_fst_eq
  (a b: Nat)
:
  (cantorPair a b).cantorFst = b
:= by
  unfold cantorFst cantorPair.t
  rw [cantorPair.w_eq_add]
  unfold cantorPair
  exact Nat.add_sub_cancel_left _ _

def Nat.cantorPair_zth_eq
  (a b: Nat)
:
  (cantorPair a b).cantorZth = a
:= by
  unfold cantorZth
  rw [cantorPair_fst_eq, cantorPair.w_eq_add]
  exact Nat.add_sub_cancel _ _

def Nat.cantorPair_zth_fst_eq
  (n: Nat)
:
  cantorPair n.cantorZth n.cantorFst = n
:=
  let ⟨a, b, eq⟩ := cantorPair_surjective n
  eq ▸
  (cantorPair_zth_eq a b).symm ▸
  (cantorPair_fst_eq a b).symm ▸
  rfl
