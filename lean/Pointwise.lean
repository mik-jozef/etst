/-
  Stuff related to pointwise partial orders.
-/

import Fixpoint

open Classical

instance PartialOrder.pointwise
  (X: Type)
  {Y: Type}
  (_: PartialOrder Y)
:
  PartialOrder (X → Y)
where
  le a b := ∀ x: X, a x .≤ b x
  
  refl a := fun v => PartialOrder.refl (a v)
  antisymm _ _ := fun ab ba => funext fun v =>
    PartialOrder.antisymm _ _ (ab v) (ba v)
  trans _ _ _ := fun ab bc v => PartialOrder.trans _ _ _ (ab v) (bc v)
  
  ltToLeNeq := id
  leNeqToLt := id


def pointwiseSup.at
  (ord: PartialOrder D)
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  Set D
:=
  fun d => ∃ f: ↑ch.val, d = f.val i

def pointwiseSup.atChain
  (ord: PartialOrder D)
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  Chain ord
:= ⟨
  pointwiseSup.at ord ch i,
  fun d0 d1 =>
    let d0F := choiceEx d0.property
    let d1F := choiceEx d1.property
    
    let fComparable := ch.property d0F d1F
    
    d0F.property ▸ d1F.property ▸ fComparable.elim
      (fun le => Or.inl (le i))
      (fun ge => Or.inr (ge i))
⟩

def pointwiseSup.atChain.inCh
  (ord: PartialOrder D)
  (ch: Chain (ord.pointwise I))
  (dIn: d ∈ (pointwiseSup.atChain ord ch i).val)
:
  ∃ f: ↑ch.val, d = f.val i
:=
  let f := choiceEx dIn
  ⟨f, f.property⟩

def pointwiseSup.inCh.atChain
  (ord: PartialOrder D)
  (ch: Chain (ord.pointwise I))
  {f: ↑ch.val}
  (dIn: d = f.val i)
:
  d ∈ (pointwiseSup.atChain ord ch i).val
:=
  ⟨f, dIn⟩

noncomputable def pointwiseSup.typed
  {I D: Type}
  (ord: PartialOrder D)
  (cc: isChainComplete ord)
  (ch: Chain (ord.pointwise I))
:
  (i: I) → (Supremum ord (pointwiseSup.at ord ch i))
:=
  fun i =>
    let chAtI: Chain ord := pointwiseSup.atChain ord ch i
    choiceEx (cc chAtI)

noncomputable def pointwiseSup
  {I D: Type}
  (ord: PartialOrder D)
  (cc: isChainComplete ord)
  (ch: Chain (ord.pointwise I))
:
  Supremum (ord.pointwise I) ch.val
:=
  let sup := pointwiseSup.typed ord cc ch
  let supUntyped: I → D := fun i => (sup i).val
  
  ⟨
    supUntyped,
    And.intro
      (fun (f: ↑ch.val) i => (sup i).property.left ⟨f.val i, ⟨f, rfl⟩⟩)
      (fun f fUB i =>
        let fiUB: f i ∈ isUpperBound ord (pointwiseSup.at ord ch i) :=
          fun d =>
            let ff := choiceEx d.property
            ff.property ▸ fUB ff i
        (sup i).property.right (f i) fiUB)
  ⟩

noncomputable def pointwiseSup.eqTyped
  {I D: Type}
  (ord: PartialOrder D)
  (cc: isChainComplete ord)
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  (pointwiseSup.typed ord cc ch i).val = (pointwiseSup ord cc ch).val i
:=
  rfl

def isChainComplete.pointwise
  (cc: isChainComplete ord)
:
  isChainComplete (ord.pointwise I)
:=
  fun ch =>
    let sup := pointwiseSup ord cc ch
    ⟨sup.val, sup.property⟩

def pointwiseSup.eqAt.pointwiseSup
  (ord: PartialOrder T)
  (cc: isChainComplete ord)
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  (pointwiseSup ord cc ch).val i =
    (Chain.sup ord cc (pointwiseSup.atChain ord ch i)).val
:=
  rfl

def pointwiseSup.eqAt
  (ord: PartialOrder T)
  (cc: isChainComplete ord)
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  (ch.sup (ord.pointwise I) cc.pointwise).val i =
    (Chain.sup ord cc (pointwiseSup.atChain ord ch i)).val
:=
  let pSup := pointwiseSup ord cc ch
  --let chSup := ch.sup (ord.pointwise I) cc.pointwise
  let supEq: ch.sup (ord.pointwise I) cc.pointwise = pSup := sup.eq _ _ _
  
  supEq ▸ pointwiseSup.eqAt.pointwiseSup ord cc ch i
