/-
  Some helper functions for ordinals.
-/

import Utils.BasicUtils
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic


instance _.u: Coe (Ordinal.{u}) (Type (u + 1)) where
  coe n := { nn: Ordinal // nn < n }

namespace Ordinal
  def succ (n: Ordinal) := Order.succ n
  
  -- IsLimit from Mathlib considers, regrettably,
  -- zero not to be a limit ordinal.
  def IsActualLimit (n: Ordinal): Prop :=
    ∀ a < n, a.succ < n
  
  def IsActualLimit.toIsLimit
    (ial: IsActualLimit n)
    (notZero: n ≠ 0)
  :
    IsLimit n
  :=
    And.intro notZero ial
  
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
  
  def IsSucc.fromNotLimit
    {n: Ordinal}
    (notLimit: ¬IsActualLimit n)
  :
    IsSucc n
  :=
    notLimit.toEx fun _nn nImpl =>
      let ⟨nnLt, succNLt⟩ := nImpl.implToAnd
      pred_of_succ_not_lt nnLt succNLt
  
  def notLimitToPredLt
    {n: Ordinal}
    (notLimit: ¬n.IsActualLimit)
  :
    n.pred < n
  :=
    let isSucc := Ordinal.IsSucc.fromNotLimit notLimit
    let pred := isSucc.unwrap
    
    Ordinal.pred_lt_iff_is_succ.mpr ⟨pred, pred.property.symm⟩
  
  def succ.isInjective: Function.Injective succ := Order.succ_injective
  
  def not_max (n: Ordinal): ¬IsMax n :=
    fun isMax =>
      let ⟨m, nLtM⟩ := (noMaxOrder.exists_gt n).unwrap
      let mLeN := isMax (le_of_lt nLtM)
      
      let eq: n = m := (le_of_lt nLtM).antisymm mLeN
      
      nLtM.ne eq
  
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
    if h: ∃ a, n = Order.succ a then
      let eqPredSucc: n = n.pred.succ :=
        (succ_pred_iff_is_succ.mpr h).symm
      let or := succ_middle_eq xnSucc (eqPredSucc ▸ xn)
      or.elim
        (fun eq => Or.inr eq)
        (fun eq => Or.inl (eqPredSucc ▸ eq))
    else
      let predNEq := pred_eq_iff_not_succ.mpr h
      let nx := predNEq ▸ xnSucc
      Or.inl (xn.antisymm nx)
  
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
  
  def succ_pred_of_not_limit
    {n: Ordinal}
    (notLimit: ¬n.IsActualLimit)
  :
    n.pred.succ = n
  :=
    let nPred := (IsSucc.fromNotLimit notLimit).unwrap
    
    succ_pred_iff_is_succ.mpr ⟨nPred, nPred.property.symm⟩
  
  def le_pred_of_lt
    {a b: Ordinal}
    (ab: a < b)
  :
    a ≤ b.pred
  :=
    (Ordinal.linearOrder.le_total a b.pred).elim
      (id)
      (fun bPredLeA =>
        if h: a = b.pred then
          h ▸ Ordinal.linearOrder.le_refl _
        else
          let bPredLtA := lt_of_le_of_ne' bPredLeA h
          False.elim (pred_no_middle ab bPredLtA))
  
  def succ_not_limit (n: Ordinal): ¬IsActualLimit n.succ :=
    fun isLimit =>
      let ltSelf := isLimit n (lt_succ_self n)
      lt_irrefl n.succ ltSelf
  
  def IsActualLimit.succ_lt
    {n: Ordinal}
    (nn: ↑n)
    (nIsLimit: n.IsActualLimit)
  :
    nn.val.succ < n
  :=
    if h: n = 0 then
      False.elim (Ordinal.not_lt_zero nn (h ▸ nn.property))
    else
      (nIsLimit.toIsLimit h).succ_lt nn.property
  
  def le_max_left (a b: Ordinal): a ≤ max a b :=
    if h: a ≤ b then
      let eqB: max a b = b := max_eq_right_iff.mpr h
      
      eqB.symm ▸ h
    else
      let eqA: max a b = a := max_eq_left_iff.mpr (le_of_not_le h)
      
      eqA.symm ▸ Preorder.le_refl _
  
  def le_max_rite (a b: Ordinal): b ≤ max a b :=
    if h: a ≤ b then
      let eqB: max a b = b := max_eq_right_iff.mpr h
      
      eqB.symm ▸ Preorder.le_refl _
    else
      let eqA: max a b = a := max_eq_left_iff.mpr (le_of_not_le h)
      
      eqA.symm ▸ (le_of_not_le h)
  
  def zero.isLimit: IsActualLimit 0 :=
    fun n nLtZero => False.elim (Ordinal.not_lt_zero n nLtZero)
  
end Ordinal
