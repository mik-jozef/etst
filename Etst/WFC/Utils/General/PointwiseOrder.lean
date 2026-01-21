import Mathlib.Data.Set.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Preorder.Chain
import Mathlib.Logic.Function.Basic

import Etst.BasicUtils


def IsChainComplete {T} (ord: PartialOrder T): Prop :=
  ∀ ⦃ch⦄, IsChain ord.le ch → ∃ t: T, IsLUB ch t

noncomputable def IsChainComplete.sup
  {T} {ord: PartialOrder T}
  (isCc: IsChainComplete ord)
  {ch: Set T}
  (isChain: IsChain ord.le ch)
:
  T
:=
  (isCc isChain).choose

def IsChain.iUnion_of_subset
  {I T} {Le}
  (s: I → Set T)
  (areChains: ∀ i: I, IsChain Le (s i))
  (isSubset: ∀ i j: I, s i ⊆ s j ∨ s j ⊆ s i)
:
  IsChain Le (⋃ i, s i)
:=
  fun
    _t0
    ⟨s0, ⟨i0, (eq0: s i0 = s0)⟩, t0In⟩
    _t1
    ⟨s1, ⟨i1, (eq1: s i1 = s1)⟩, t1In⟩
    neq
  =>
    (isSubset i0 i1).elim
      (fun s0Le =>
        areChains i1 (s0Le (eq0 ▸ t0In)) (eq1 ▸ t1In) neq)
      (fun s1Le =>
        areChains i0 (eq0 ▸ t0In) (s1Le (eq1 ▸ t1In)) neq)


def PartialOrder.pointwise
  {Y} (X: Type*)
  (_: PartialOrder Y)
:
  PartialOrder (X → Y)
where
  le a b := ∀ x: X, a x ≤ b x
  
  le_refl _ := fun _ => le_rfl
  le_antisymm _ _ := fun ab ba => funext fun v =>
    PartialOrder.le_antisymm _ _ (ab v) (ba v)
  le_trans _ _ _ := fun ab bc v => Preorder.le_trans _ _ _ (ab v) (bc v)


def Set.pointwiseImage
  {D} {I: Type*}
  (set: Set (I → D))
  (i: I)
:
  Set D
:=
  set.image fun f => f i

def PartialOrder.isUB_pointwise_isUB
  {D I} {ord: PartialOrder D} {set: Set (I → D)} {ub}
  (isUb: upperBounds set ub)
  (i: I)
:
  upperBounds (set.pointwiseImage i) (ub i)
:=
  fun _d ⟨_f, fIn, eq⟩ => eq ▸ isUb fIn i

def PartialOrder.isLUB_pointwise_isLUB
  {D I} {ord: PartialOrder D} {set: Set (I → D)} {lub}
  (isLub: IsLUB set lub)
  (i: I)
:
  IsLUB (set.pointwiseImage i) (lub i)
:=
  And.intro
    (isUB_pointwise_isUB isLub.left i)
    (fun d dUb =>
      let lubUpdated := Function.update lub i d
      let lubUpdatedEq: lubUpdated i = d :=
        Function.update_self i d lub
      let lubLe: lub ≤ lubUpdated :=
        isLub.right (fun f fIn ii =>
          if h: ii = i then
            h ▸ lubUpdatedEq ▸ dUb ⟨f, fIn, rfl⟩
          else by
            unfold lubUpdated
            rw [Function.update_of_ne h d lub]
            exact isLub.left fIn ii)
      let lubUpdatedLe: lubUpdated i ≤ d :=
        Function.update_self i d lub ▸ le_rfl
      (lubLe i).trans lubUpdatedLe)


def IsChain.pointwiseImage
  {D I} {ord: PartialOrder D} {ch}
  (isChain: IsChain (ord.pointwise I).le ch)
  (i: I)
:
  IsChain ord.le (ch.pointwiseImage i)
:=
  fun _d0 ⟨_f0, f0In, isAtPoint0⟩ _d1 ⟨_f1, f1In, isAtPoint1⟩ _ =>
    isAtPoint0 ▸ isAtPoint1 ▸
    match isChain.total f0In f1In with
    | Or.inl le => Or.inl (le i)
    | Or.inr ge => Or.inr (ge i)

noncomputable def IsChain.pointwiseSup
  {D I} {ord: PartialOrder D} {ch}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
:
  I → D
:=
  fun i => (isCc (isChain.pointwiseImage i)).unwrap

def IsChain.pointwiseSup_sup_at_point
  {D I} {ord: PartialOrder D} {ch}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
  (i: I)
:
  IsLUB (ch.pointwiseImage i) (isChain.pointwiseSup isCc i)
:=
  (isCc (isChain.pointwiseImage i)).unwrap.property

def IsChain.pointwiseSup_isLUB
  {D I} {ord: PartialOrder D} {ch}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
:
  IsLUB ch (isChain.pointwiseSup isCc)
:=
  And.intro
    (fun f fIn i =>
      let ⟨isUb, _⟩ := isChain.pointwiseSup_sup_at_point isCc i
      isUb ⟨f, fIn, rfl⟩)
    (fun _f0 f0In i =>
      let ⟨_, isLeUb⟩ := isChain.pointwiseSup_sup_at_point isCc i
      isLeUb fun _d ⟨_f1, f1In, eq⟩ => eq ▸ f0In f1In i)


def CompleteLattice.pointwise
  {Y} (X: Type*)
  (cl: CompleteLattice Y)
:
  CompleteLattice (X → Y)
where
  __ := PartialOrder.pointwise X cl.toPartialOrder
  top _ := cl.top
  bot _ := cl.bot
  
  le_top _ := le_top
  bot_le _ := bot_le
  
  sup a b x := a x ⊔ b x
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ := sup_le
  
  inf a b x := a x ⊓ b x
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  
  sSup s x := sSup (s.pointwiseImage x)
  le_sSup s f fIn x :=
    le_sSup (s.pointwiseImage x) (f x) ⟨f, fIn, rfl⟩
  sSup_le s f leF x :=
    sSup_le
      (s.pointwiseImage x)
      (f x)
      (fun _y ⟨fY, fYIn, eq⟩ => eq ▸ leF fY fYIn x)

  sInf s x := sInf (s.pointwiseImage x)
  sInf_le s f fIn x :=
    sInf_le (s.pointwiseImage x) (f x) ⟨f, fIn, rfl⟩
  le_sInf s f leF x :=
    le_sInf
      (s.pointwiseImage x)
      (f x)
      (fun _y ⟨fY, fYIn, eq⟩ => eq ▸ leF fY fYIn x)
