/-
  Some helper functions and definitions for ordinals.
-/

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

import old.Utils.BasicUtils


instance _.u: Coe (Ordinal.{u}) (Type (u + 1)) where
  coe n := { nn: Ordinal // nn < n }

namespace Ordinal
  def succ (n: Ordinal) := Order.succ n
  
  def not_min_of_not_zero
    {n: Ordinal}
    (notZero: n ≠ 0)
  :
    ¬ IsMin n
  :=
    fun isMin =>
      let leZero := isMin (Ordinal.zero_le n)
      let eqZero := Ordinal.le_zero.mp leZero
      notZero eqZero
  
  abbrev IsSuccPrelimit (n: Ordinal): Prop := Order.IsSuccPrelimit n
  abbrev IsSuccLimit (n: Ordinal): Prop := Order.IsSuccLimit n
  
  def IsSuccPrelimit.toIsSuccLimit
    (ispl: IsSuccPrelimit n)
    (notZero: n ≠ 0)
  :
    IsSuccLimit n
  :=
    And.intro
      (not_min_of_not_zero notZero)
      ispl
  
  def pred_of_succ_not_lt
    {nn n: Ordinal}
    (nnLt: nn < n)
    (succNLt: ¬nn.succ < n)
  :
    nn.succ = n
  :=
    let succLe := Order.succ_le_of_lt nnLt
    let ltOrEq := lt_or_eq_of_le succLe
    
    ltOrEq.elim
      (fun nnLt => False.elim (succNLt nnLt))
      id
  
  def IsSucc (n: Ordinal) := ∃ nn: Ordinal, nn.succ = n
  
  def IsSucc.fromNotPrelimit
    {n: Ordinal}
    (notPrelimit: ¬ IsSuccPrelimit n)
  :
    IsSucc n
  :=
    notPrelimit.toEx fun nn nImpl =>
      let ⟨nnLt, succNLt⟩ := nImpl.dne
      pred_of_succ_not_lt nnLt (succNLt (Order.lt_succ nn))
  
  def predLtOfNotPrelimit
    {n: Ordinal}
    (notLimit: ¬ n.IsSuccPrelimit)
  :
    n.pred < n
  :=
    pred_lt_iff_not_isSuccPrelimit.mpr notLimit
  
  def succ.isInjective: Function.Injective succ := Order.succ_injective
  
  def not_max (n: Ordinal): ¬IsMax n :=
    not_isMax_of_lt (Order.lt_succ n)
  
  def lt_succ_self (n: Ordinal): n < n.succ :=
    Order.lt_succ_of_not_isMax (not_max n)
  
  def le_succ_self (n: Ordinal): n ≤ n.succ :=
    le_of_lt (lt_succ_self n)
  
  def succ_lt_of_lt
    {a b: Ordinal}
    (ab: a < b)
  :
    a.succ < b.succ
  :=
    let aLtBSucc: a < b.succ := ab.trans_le (le_succ_self b)
    let succLe: a.succ ≤ b.succ := Order.succ_le_of_lt aLtBSucc
    let neqSucc: a.succ ≠ b.succ :=
      fun eq => ab.ne (succ.isInjective eq)
    lt_of_le_of_ne' succLe neqSucc.symm
  
  def lt_of_lt_succ
    {a b: Ordinal}
    (ab: a.succ < b.succ)
  :
    a < b
  :=
    let aLeBSucc: a < b.succ := (le_succ_self a).trans_lt ab
    let le: a ≤ b := Order.le_of_lt_succ aLeBSucc
    let neqSucc: a ≠ b := fun eq => ab.ne (congr rfl eq)
    lt_of_le_of_ne' le neqSucc.symm
  
  def succ_middle_eq
    {n: Ordinal}
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
    {n: Ordinal}
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
      let or := succ_middle_eq xnSucc (eqPredSucc ▸ xn)
      or.elim
        (fun eq => Or.inr eq)
        (fun eq => Or.inl (eqPredSucc ▸ eq))
  
  def pred_no_middle
    {n: Ordinal}
    (nx: x < n)
    (xnSucc: n.pred < x)
  :
    False
  :=
    let orEq := pred_middle_eq (le_of_lt nx) (le_of_lt xnSucc)
    False.elim (orEq.elim
      (fun eqX => lt_irrefl x (eqX ▸ nx))
      (fun eqPred => lt_irrefl x (eqPred ▸ xnSucc)))
  
  def succ_pred_of_not_prelimit
    {n: Ordinal}
    (notLimit: ¬n.IsSuccPrelimit)
  :
    n.pred.succ = n
  :=
    succ_pred_eq_iff_not_isSuccPrelimit.mpr notLimit
  
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
  
  def succ_not_prelimit (n: Ordinal): ¬ IsSuccPrelimit n.succ :=
    fun isPrelimit =>
      let notMin := not_min_of_not_zero (succ_ne_zero n)
      Order.not_isSuccLimit_succ _ ⟨notMin, isPrelimit⟩
  
  def IsSuccPrelimit.succ_lt
    {n: Ordinal}
    (nn: ↑n)
    (nIsLimit: n.IsSuccPrelimit)
  :
    nn.val.succ < n
  :=
    if h: n = 0 then
      False.elim (Ordinal.not_lt_zero nn (h ▸ nn.property))
    else
      (nIsLimit.toIsSuccLimit h).succ_lt nn.property
  
  def le_max_left (a b: Ordinal): a ≤ max a b :=
    if h: a ≤ b then
      let eqB: max a b = b := max_eq_right_iff.mpr h
      
      eqB.symm ▸ h
    else
      let eqA: max a b = a := max_eq_left_iff.mpr (le_of_not_ge h)
      
      eqA.symm ▸ Preorder.le_refl _
  
  def le_max_rite (a b: Ordinal): b ≤ max a b :=
    if h: a ≤ b then
      let eqB: max a b = b := max_eq_right_iff.mpr h
      
      eqB.symm ▸ Preorder.le_refl _
    else
      let eqA: max a b = a := max_eq_left_iff.mpr (le_of_not_ge h)
      
      eqA.symm ▸ (le_of_not_ge h)
  
  def lt_succ (n: Ordinal): n < n.succ := Order.lt_succ n
  
  def ne_zero_of_lt
    {n m: Ordinal}
    (lt: n < m)
  :
    m ≠ 0
  :=
    fun eq => Ordinal.not_lt_zero n (eq ▸ lt)
  
  def one_lt
    {n: Ordinal}
    (notZero: n ≠ 0)
    (notOne: n ≠ 1)
  :
    1 < n
  :=
    (lt_or_ge 1 n).elim
      id
      (fun ge =>
        False.elim
          ((lt_or_eq_of_le ge).elim
            (notZero ∘ lt_one_iff_zero.mp)
            notOne))
  
  def lt_add_rite
    (a: Ordinal.{u})
    (neqZero: b ≠ 0)
  :
    a < a + b
  := by
    let zeroLt := Ordinal.pos_iff_ne_zero.mpr neqZero
    nth_rw 1 [←add_zero a]
    exact add_lt_add_left zeroLt a
  
end Ordinal
