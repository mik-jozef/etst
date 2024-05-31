/-
  PartialOrder.optionTop, given a partial order on T,
  defines a partial order on `Option T` that places
  none above all other elements.
  
  This file also contains some related helper proofs.
-/

import Mathlib.Init.Order.Defs


namespace PartialOrder
  def Option.Le (ord: PartialOrder T): Option T → Option T → Prop
    | none, none => True
    | none, some _ => False
    | some _, none => True
    | some t0, some t1 => ord.le t0 t1
  
  def Option.Lt (ord: PartialOrder T): Option T → Option T → Prop
    | none, none => False
    | none, some _ => False
    | some _, none => True
    | some t0, some t1 => ord.lt t0 t1
  
  def Option.Le.toLt
    (lt: Option.Le ord a b)
    (neq: a ≠ b)
  :
    Option.Lt ord a b
  :=
    match a, b with
    | none, none => False.elim (neq rfl)
    | none, some _ => False.elim lt
    | some _, none => trivial
    | some _, some _ => lt_of_le_of_ne lt fun eq => neq (congr rfl eq)
  
  def Option.Lt.toLe (lt: Option.Lt ord a b): Option.Le ord a b :=
    match a, b with
    | none, none => False.elim lt
    | none, some _ => False.elim lt
    | some _, none => trivial
    | some _, some _ => le_of_lt lt
  
  def Option.Lt.toNeq (lt: Option.Lt ord a b): a ≠ b :=
    match a, b with
    | none, none => False.elim lt
    | none, some _ => False.elim lt
    | some _, none => Option.noConfusion
    | some _, some _ =>
        fun eq => ne_of_lt lt (Option.noConfusion eq id)
  
  def optionTop.leAntisymmSome {ord: PartialOrder T}
    {a b: T}
    (ab: Option.Le ord (some a) (some b))
    (ba: Option.Le ord (some b) (some a))
  :
    some a = some b
  :=
    congr rfl (ord.le_antisymm a b ab ba)
  
  def optionTop (ord: PartialOrder T): PartialOrder (Option T) where
    le := Option.Le ord
    
    le_refl
      | none => trivial
      | some t => ord.le_refl t
    
    le_antisymm
      | none, none, _, _ => rfl
      | none, some _, nope, _ => False.elim nope
      | some _, none, _, nope => False.elim nope
      | some _, some _, ab, ba => optionTop.leAntisymmSome ab ba
    
    le_trans
      | none, _, none, _, _ => trivial
      | some _, _, none, _, _ => trivial
      | none, none, some _, _, nope => False.elim nope
      | none, some _, some _, nope, _ => False.elim nope
      | some a, some b, some c, ab, bc => ord.le_trans a b c ab bc
    
    lt := Option.Lt ord
    
    lt_iff_le_not_le
      | none, none =>
          Iff.intro
            (fun nn => False.elim nn)
            (fun ⟨_,nn⟩ => False.elim (nn trivial))
      | none, some _ =>
          Iff.intro
            (fun nope => False.elim nope)
            (fun ⟨nope,_⟩ => False.elim nope)
      | some _, none =>
          Iff.intro
            (fun _ => ⟨trivial, False.elim⟩)
            (fun _ => trivial)
      | some _, some _ =>
          Iff.intro (
            fun ab => ⟨
              ab.toLe,
              fun ba =>
                False.elim (
                  ab.toNeq (optionTop.leAntisymmSome ab.toLe ba)
                ),
          ⟩) (
            fun ⟨le, neLe⟩ => le.toLt fun eq => neLe (eq ▸ le)
          )
  
  def optionTop.noneGreatest
    {ord: PartialOrder T}
    (t: Option T)
  :
    ord.optionTop.le t none
  :=
    -- TODO: your theorem prover shouldn't need a switch.
    match t with
      | none => trivial
      | some _ => trivial
  
  def optionTop.greatestNone
    {ord: PartialOrder T}
    {t: Option T}
    (tGreatest: ∀ tt: Option T, ord.optionTop.le tt t)
  :
    t = none
  :=
    Classical.byContradiction fun neqNone =>
      match t with
        | none => neqNone rfl
        | some _ => tGreatest none
  
  def optionTop.noneLeToEqNone
    {ord: PartialOrder T}
    {t: Option T}
    (noneLe: ord.optionTop.le none t)
  :
    t = none
  :=
    ord.optionTop.le_antisymm _ _ (noneGreatest t) noneLe
  
  
  def leLtAntisymm
    {ord: PartialOrder T}
    (ab: ord.le a b)
    (ba: ord.lt b a)
  :
    P
  :=
    False.elim
      ((lt_or_eq_of_le ab).elim
        (fun abLt => lt_asymm ba abLt)
        (fun eq => lt_irrefl _ (eq ▸ ba)))
  
  def ltLeAntisymm
    {ord: PartialOrder T}
    (ab: ord.lt a b)
    (ba: ord.le b a)
  :
    P
  :=
    False.elim
      ((lt_or_eq_of_le ba).elim
        (fun baLt => lt_asymm ab baLt)
        (fun eq => lt_irrefl _ (eq.symm ▸ ab)))
  
end PartialOrder


-- The square le relation: `x ⊑ y`.
class SqLE (T : Type u) where
  le : T → T → Prop

-- The square lt relation: `x ⊏ y`.
class SqLT (T : Type u) where
  lt : T → T → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt
