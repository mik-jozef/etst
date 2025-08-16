
import Mathlib.Data.Set.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Preorder.Chain

import Etst.BasicUtils


def IsChainComplete (ord: PartialOrder T): Prop :=
  ∀ ⦃ch⦄, IsChain ord.le ch → ∃ t: T, IsLUB ch t


def PartialOrder.pointwise
  (X: Type*)
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
  {I: Type*}
  (set: Set (I → D))
  (i: I)
:
  Set D
:=
  fun d => ∃ f: set, d = f.val i

def IsChain.pointwiseImage
  {ord: PartialOrder D}
  (isChain: IsChain (ord.pointwise I).le ch)
  (i: I)
:
  IsChain ord.le (ch.pointwiseImage i)
:=
  fun _d0 ⟨f0, isAtPoint0⟩ _d1 ⟨f1, isAtPoint1⟩ _ =>
    isAtPoint0 ▸ isAtPoint1 ▸
    match isChain.total f0.property f1.property with
    | Or.inl le => Or.inl (le i)
    | Or.inr ge => Or.inr (ge i)


noncomputable def IsChain.pointwiseSup
  {ord: PartialOrder D}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
:
  I → D
:=
  fun i => (isCc (isChain.pointwiseImage i)).unwrap

def IsChain.pointwiseSup_sup_at_point
  {ord: PartialOrder D}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
  (i: I)
:
  IsLUB (ch.pointwiseImage i) (isChain.pointwiseSup isCc i)
:=
  (isCc (isChain.pointwiseImage i)).unwrap.property

def IsChain.pointwiseSup_isLUB
  {ord: PartialOrder D}
  (isChain: IsChain (ord.pointwise I).le ch)
  (isCc: IsChainComplete ord)
:
  IsLUB ch (isChain.pointwiseSup isCc)
:=
  And.intro
    (fun f fIn i =>
      let ⟨isUb, _⟩ := isChain.pointwiseSup_sup_at_point isCc i
      isUb ⟨⟨f, fIn⟩, rfl⟩)
    (fun _f0 f0In i =>
      let ⟨_, isLeUb⟩ := isChain.pointwiseSup_sup_at_point isCc i
      isLeUb fun _d ⟨⟨_f1, f1In⟩, eq⟩ => eq ▸ f0In f1In i)
