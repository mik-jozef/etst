module
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Chain

import Mathlib.Data.Set.Basic
import Etst.BasicUtils

public section


exposed def IsChainComplete {T} (ord: PartialOrder T): Prop :=
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

theorem IsChain.iUnion_of_subset
  {I T} {Le}
  (s: I → Set T)
  (areChains: ∀ i: I, IsChain Le (s i))
  (isSubset: ∀ i j: I, s i ⊆ s j ∨ s j ⊆ s i)
:
  IsChain Le (⋃ i, s i)
:=
  fun
    _t0
    ⟨_, ⟨i0, rfl⟩, t0In⟩
    _t1
    ⟨_, ⟨i1, rfl⟩, t1In⟩
    neq
  =>
    (isSubset i0 i1).elim
      (fun s0Le =>
        areChains i1 (s0Le t0In) t1In neq)
      (fun s1Le =>
        areChains i0 t0In (s1Le t1In) neq)


@[expose, reducible]
def PartialOrder.pointwise
  {Y} (X: Type*)
  (_: PartialOrder Y)
:
  PartialOrder (X → Y)
where
  le a b := ∀ x: X, a x ≤ b x
  
  le_refl _ _ := le_rfl
  le_antisymm _ _ ab ba := funext fun v =>
    PartialOrder.le_antisymm _ _ (ab v) (ba v)
  le_trans _ _ _ ab bc v := Preorder.le_trans _ _ _ (ab v) (bc v)


exposed def Set.pointwiseImage
  {D} {I: Type*}
  (set: Set (I → D))
  (i: I)
:
  Set D
:=
  set.image fun f => f i

theorem PartialOrder.isUB_pointwise_isUB
  {D I} {ord: PartialOrder D} {set: Set (I → D)} {ub}
  (isUb: ub ∈ upperBounds set)
  (i: I)
:
  ub i ∈ upperBounds (set.pointwiseImage i)
:=
  fun _d ⟨_f, fIn, eq⟩ => eq ▸ isUb fIn i

theorem PartialOrder.isLUB_pointwise_isLUB
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


theorem IsChain.pointwiseImage
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

theorem IsChain.pointwiseSup_sup_at_point
  {D I} {ord: PartialOrder D} {ch}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
  (i: I)
:
  IsLUB (ch.pointwiseImage i) (isChain.pointwiseSup isCc i)
:=
  (isCc (isChain.pointwiseImage i)).unwrap.property

theorem IsChain.pointwiseSup_isLUB
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


@[expose, reducible]
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
  isLUB_sSup s := ⟨
    fun f fIn x =>
      (isLUB_sSup (s.pointwiseImage x)).1 ⟨f, fIn, rfl⟩,
    fun _ leF x =>
      (isLUB_sSup (s.pointwiseImage x)).2 (fun _ ⟨_, gIn, hy⟩ =>
        hy ▸ leF gIn x)
  ⟩

  sInf s x := sInf (s.pointwiseImage x)
  isGLB_sInf s := ⟨
    fun f fIn x =>
      (isGLB_sInf (s.pointwiseImage x)).1 ⟨f, fIn, rfl⟩,
    fun _ leF x =>
      (isGLB_sInf (s.pointwiseImage x)).2 (fun _ ⟨_, gIn, hy⟩ =>
        hy ▸ leF gIn x)
  ⟩
