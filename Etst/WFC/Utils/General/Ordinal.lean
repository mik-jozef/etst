import Mathlib.SetTheory.Ordinal.Family

import Etst.BasicUtils


namespace Ordinal
  abbrev succ (n: Ordinal) := Order.succ n
  
  instance coeToType.{u}: Coe (Ordinal.{u}) (Type (u + 1)) where
    coe n := { nn: Ordinal // nn < n }
  
  abbrev IsSuccPrelimit (n: Ordinal): Prop := Order.IsSuccPrelimit n
  abbrev IsSuccLimit (n: Ordinal): Prop := Order.IsSuccLimit n
  
  def succ_middle_eq
    {x} {n: Ordinal}
    (nx: n ≤ x)
    (xnSucc: x ≤ n.succ)
  :
    x = n ∨ x = n.succ
  :=
    if h: n = x then
      Or.inl h.symm
    else
      let nxLt := lt_of_le_of_ne nx h
      let nSuccLe: n.succ ≤ x := Order.succ_le_of_lt nxLt
      Or.inr (nSuccLe.antisymm xnSucc).symm
  
  def pred_middle_eq
    {x} {n: Ordinal}
    (xn: x ≤ n)
    (xnSucc: n.pred ≤ x)
  :
    x = n ∨ x = n.pred
  :=
    if h: IsSuccPrelimit n then
      let predNEq := pred_eq_iff_isSuccPrelimit.mpr h
      let nx := predNEq ▸ xnSucc
      Or.inl (xn.antisymm nx)
    else
      let eqPredSucc: n = n.pred.succ :=
        (succ_pred_eq_iff_not_isSuccPrelimit.mpr h).symm
      (succ_middle_eq xnSucc (eqPredSucc ▸ xn)).elim
        Or.inr
        (fun eq => Or.inl (eqPredSucc ▸ eq))
  
  def pred_no_middle
    {x} {n: Ordinal}
    (nx: x < n)
    (xnSucc: n.pred < x)
  :
    False
  :=
    let orEq := pred_middle_eq (le_of_lt nx) (le_of_lt xnSucc)
    False.elim (orEq.elim
      (fun eqX => lt_irrefl x (eqX ▸ nx))
      (fun eqPred => lt_irrefl x (eqPred ▸ xnSucc)))
  
  def le_pred_of_lt
    {a b: Ordinal}
    (ab: a < b)
  :
    a ≤ b.pred
  :=
    (Ordinal.instLinearOrder.le_total a b.pred).elim
      (id)
      (fun bPredLeA =>
        if h: a = b.pred then
          h ▸ Ordinal.instLinearOrder.le_refl _
        else
          let bPredLtA := lt_of_le_of_ne' bPredLeA h
          False.elim (pred_no_middle ab bPredLtA))
  
  def zero_lt
    {n: Ordinal}
    (ne: n ≠ 0)
  :
    0 < n
  :=
    (eq_zero_or_pos n).elim (False.elim ∘ ne) id
  
  def pred_lt
    {n} (nLim: ¬ IsSuccPrelimit n)
  :
    n.pred < n
  :=
    Ordinal.pred_lt_iff_not_isSuccPrelimit.mpr nLim
  
end Ordinal
