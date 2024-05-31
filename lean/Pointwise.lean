/-
  Stuff related to pointwise partial orders.
-/

import Utils.Chain


instance PartialOrder.pointwise
  (X: Type u)
  {Y: Type v}
  (_: PartialOrder Y)
:
  PartialOrder (X → Y)
where
  le a b := ∀ x: X, a x ≤ b x
  
  le_refl a := fun v => Preorder.le_refl (a v)
  le_antisymm _ _ := fun ab ba => funext fun v =>
    PartialOrder.le_antisymm _ _ (ab v) (ba v)
  le_trans _ _ _ := fun ab bc v => Preorder.le_trans _ _ _ (ab v) (bc v)
  

def Set.pointwiseAt
  {I: Type u}
  (set: Set (I → D))
  (i: I)
:
  Set D
:=
  fun d => ∃ f: set, d = f.val i

def Chain.pointwiseAtSet
  {ord: PartialOrder D}
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  Set D
:=
  fun d => ∃ f: ↑ch, d = f.val i

def Chain.pointwiseAt
  {ord: PartialOrder D}
  (ch: Chain (ord.pointwise I))
  (i: I)
:
  Chain ord
:= ⟨
  ch.pointwiseAtSet i,
  fun _d0 d0In _d1 d1In =>
    let d0F := d0In.unwrap
    let d1F := d1In.unwrap
    
    let fComparable := ch.isChain.toComparable d0F d1F
    
    d0F.property ▸ d1F.property ▸ fComparable.elim
      (fun le _neq => Or.inl (le i))
      (fun geOrEq _neq =>
        (geOrEq.elim
          (fun ge => Or.inr (ge i))
          (fun eq => Or.inr (eq ▸ Preorder.le_refl _))))
⟩

def Chain.pointwiseSup.atIndex.inChain
  {ord: PartialOrder D}
  (ch: Chain (ord.pointwise I))
  (dIn: d ∈ (ch.pointwiseAt i).set)
:
  ∃ f: ↑ch, d = f.val i
:=
  let f := dIn.unwrap
  ⟨f, f.property⟩

def Chain.pointwiseSup.inChain.atIndex
  (ord: PartialOrder D)
  (ch: Chain (ord.pointwise I))
  {f: ↑ch}
  (dIn: d = f.val i)
:
  d ∈ (ch.pointwiseAt i).set
:=
  ⟨f, dIn⟩

noncomputable def Chain.pointwiseSup.typed
  {ord: PartialOrder D}
  (ch: Chain (ord.pointwise I))
  (cc: IsChainComplete ord)
:
  { f: I → D //
    ∀ i: I, IsSupremum ord (ch.pointwiseAt i) (f i) }
:= ⟨
  fun i => (cc.supExists (ch.pointwiseAt i)).unwrap,
  fun i => (cc.supExists (ch.pointwiseAt i)).unwrap.property
⟩

noncomputable def Chain.pointwiseSup
  {ord: PartialOrder D}
  (ch: Chain (ord.pointwise I))
  (cc: IsChainComplete ord)
:
  Supremum (ord.pointwise I) ch
:=
  let sup := pointwiseSup.typed ch cc
  
  ⟨
    sup,
    {
      isMember :=
        fun (f: ↑ch) i => (sup.property i).isMember ⟨f.val i, ⟨f, rfl⟩⟩
      isLeMember :=
        (fun f fUB i =>
          let fiUB: IsUpperBound ord (ch.pointwiseAt i) (f i) :=
            fun d =>
              let ff := d.property.unwrap
              ff.property ▸ fUB ff i
          (sup.property i).isLeMember fiUB)
    }
  ⟩

def IsChainComplete.pointwise
  (cc: IsChainComplete ord)
:
  IsChainComplete (ord.pointwise I)
:= {
  supExists :=
    fun ch =>
      let sup := ch.pointwiseSup cc
      ⟨sup.val, sup.property⟩
}

def Set.pointwiseSup.isSupAt
  {ord: PartialOrder D}
  {set: Set (I → D)}
  (sup: Supremum (ord.pointwise I) set)
  (i: I)
:
  IsSupremum ord ((set.pointwiseAt i)) (sup.val i)
:=
  {
    isMember := fun d =>
      let fWithD := d.property.unwrap
      let le: fWithD ≤ sup.val := sup.property.isMember fWithD
      
      fWithD.property ▸ le i
    isLeMember := fun d dIsUB =>
      let iToD: I → D :=
        fun ii => if ii = i then d else sup.val ii
      
      let isUB: IsUpperBound (ord.pointwise I) set iToD :=
        fun f ii =>
          if h: ii = i then
            let fIiLe := dIsUB ⟨f.val ii, ⟨f, h ▸ rfl⟩⟩
            let eq: iToD ii = d := if_pos h
            
            eq ▸ fIiLe
          else
            let fLe: f ≤ sup.val := sup.property.isMember f
            let eq: iToD ii = sup.val ii := if_neg h
            
            eq ▸ fLe ii
      
      let chSupLe: sup.val ≤ iToD :=
        sup.property.isLeMember isUB
      
      let iToDEq: iToD i = d := if_pos rfl
      
      iToDEq ▸ chSupLe i
  }

def Set.pointwiseSup.supAt
  {ord: PartialOrder D}
  {set: Set (I → D)}
  (sup: Supremum (ord.pointwise I) set)
  (i: I)
:
  Supremum ord ((set.pointwiseAt i))
:= ⟨
  (sup.val i),
  Set.pointwiseSup.isSupAt sup i,
⟩

def Set.pointwiseSup.eqAt
  {ord: PartialOrder D}
  {set: Set (I → D)}
  (setSup: Supremum (ord.pointwise I) set)
  {i: I}
  (supAtI: Supremum ord (set.pointwiseAt i))
:
  setSup.val i = supAtI.val
:=
  let mySupAt: Supremum ord (set.pointwiseAt i) := ⟨
    setSup.val i,
    isSupAt setSup i,
  ⟩
  
  let supEq := Supremum.eq mySupAt supAtI
  
  show mySupAt.val = supAtI.val from congr rfl supEq
