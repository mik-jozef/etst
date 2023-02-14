/-
  Stuff related to pointwise partial orders.
-/

import Fixpoint

open Classical

instance PartialOrder.pointwise
  (X Y: Type)
  (_: PartialOrder Y)
:
  PartialOrder (X → Y)
where
  le a b := ∀ x: X, a x .≤ b x
  
  refl a := fun v => PartialOrder.refl (a v)
  antisymm _ _ := fun ab ba => funext fun v => PartialOrder.antisymm _ _ (ab v) (ba v)
  trans _ _ _ := fun ab bc v => PartialOrder.trans _ _ _ (ab v) (bc v)
  
  ltToLeNeq := id
  leNeqToLt := id


def pointwiseSup.at
  [ord: PartialOrder D]
  (cc: isChainComplete ord)
  (ch: @Chain (I → D) (PartialOrder.pointwise I D ord))
  (i: I)
:
  Set D
:=
  fun d => ∃ f: ↑ch.val, d = f.val i

def pointwiseSup.atChain
  [ord: PartialOrder D]
  (cc: isChainComplete ord)
  (ch: @Chain (I → D) (PartialOrder.pointwise I D ord))
  (i: I)
:
  Chain D
:= ⟨
  pointwiseSup.at cc ch i,
  fun d0 d1 =>
    let d0F := choiceEx d0.property
    let d1F := choiceEx d1.property
    
    let fComparable := ch.property d0F d1F
    
    d0F.property ▸ d1F.property ▸ fComparable.elim
      (fun le => Or.inl (le i))
      (fun ge => Or.inr (ge i))
⟩

noncomputable def pointwiseSup.typed
  {I D: Type}
  [ord: PartialOrder D]
  (cc: isChainComplete ord)
  (ch: @Chain (I → D) (PartialOrder.pointwise I D ord))
:
  (i: I) → (Supremum (pointwiseSup.at cc ch i))
:=
  fun i =>
    let chAtI: Chain D := pointwiseSup.atChain cc ch i
    choiceEx (cc chAtI)

noncomputable def pointwiseSup
  {I D: Type}
  [ord: PartialOrder D]
  (cc: isChainComplete ord)
  (ch: @Chain (I → D) (PartialOrder.pointwise I D ord))
:
  @Supremum (I → D) (PartialOrder.pointwise I D ord) ch.val
:=
  let sup := pointwiseSup.typed cc ch
  let supUntyped: I → D := fun i => (sup i).val
  
  ⟨
    supUntyped,
    And.intro
      (fun (f: ↑ch.val) i => (sup i).property.left ⟨f.val i, ⟨f, rfl⟩⟩)
      (fun f fUB i =>
        let fiUB: f i ∈ isUpperBound (pointwiseSup.at cc ch i) :=
          fun d =>
            let ff := choiceEx d.property
            ff.property ▸ fUB ff i
        (sup i).property.right (f i) fiUB)
  ⟩

noncomputable def pointwiseSup.eqTyped
  {I D: Type}
  [ord: PartialOrder D]
  (cc: isChainComplete ord)
  (ch: @Chain (I → D) (PartialOrder.pointwise I D ord))
  (i: I)
:
  (pointwiseSup.typed cc ch i).val = (pointwiseSup cc ch).val i
:=
  rfl


def PartialOrder.pointwise.isChainComplete
  {X Y: Type}
  [ord: PartialOrder Y]
  (cc: isChainComplete ord)
:
  isChainComplete (PartialOrder.pointwise X Y ord)
:=
  fun ch => ⟨(pointwiseSup cc ch).val, (pointwiseSup cc ch).property⟩

def pointwiseSup.eqAt
  [ord: PartialOrder T]
  (cc: isChainComplete ord)
  (ch: @Chain (I → T) (PartialOrder.pointwise I T ord))
  (i: I)
:
  (pointwiseSup cc ch).val i = (Chain.sup (pointwiseSup.atChain cc ch i) cc).val
:=
  rfl
