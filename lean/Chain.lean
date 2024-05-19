import Tuple

-- Ideally, IsLeast should take two property names [X] and [Y] as arguments,
-- and return a structure with these two properties. "left" and "right" = BAD :/
structure iIsLeast (le: T → T → Prop) (s: Set T) (t: T): Prop where
  isMember: t ∈ s
  isLeMember: ∀ ⦃tt: T⦄, tt ∈ s → le t tt

structure IsMinimal (lt: T → T → Prop) (s: Set T) (t: T): Prop where
  isMember: t ∈ s
  isLeMember: ∀ ⦃tt: T⦄, tt ∈ s → ¬lt tt t

def Least (le: T → T → Prop) (s: Set T): Type u :=
  { t: T // iIsLeast le s t }

def Least.eq
  (ord: PartialOrder T)
  (a b: Least ord.le s)
:
  a = b
:=
  let ab: a.val ≤ b.val := a.property.isLeMember b.property.isMember
  let ba: b.val ≤ a.val := b.property.isLeMember a.property.isMember
  
  Subtype.eq (ord.le_antisymm _ _ ab ba)

def iIsLeast.isUnique
  (ord: PartialOrder T)
  (t0IsLeast: iIsLeast ord.le s t0)
  (t1IsLeast: iIsLeast ord.le s t1)
:
  t0 = t1
:=
  let t0Le := t0IsLeast.isLeMember t1IsLeast.isMember
  let t1Le := t1IsLeast.isLeMember t0IsLeast.isMember
  
  ord.le_antisymm _ _ t0Le t1Le

noncomputable def List.least
  (ord: LinearOrder T)
  (list: List T)
  (sNonEmpty: list ≠ [])
:
  Least ord.le (fun t => t ∈ list)
:=
  match list with
    | [] => False.elim (sNonEmpty rfl)
    | head :: [] => ⟨
        head,
        {
          isMember := Mem.head []
          isLeMember :=
            fun _t tIn =>
              List.eq_of_mem_singleton tIn ▸
              ord.le_refl head
        },
      ⟩
    | head :: tailHead :: tailTail =>
        let leastOfTail :=
          least ord (tailHead :: tailTail) List.noConfusion
        
        if hLt: head < leastOfTail.val then
          ⟨
            head,
            {
              isMember := Mem.head _
              isLeMember :=
                fun _t tIn =>
                  match tIn with
                  | Mem.head _ => le_refl _
                  | Mem.tail _ tInTail =>
                      let tLe := leastOfTail.property.isLeMember tInTail
                      (hLt.trans_le tLe).le
            },
          ⟩
        else if hGt: leastOfTail.val < head then
          ⟨
            leastOfTail.val,
            {
              isMember := Mem.tail _ leastOfTail.property.isMember
              isLeMember :=
                fun _t tIn =>
                  match tIn with
                  | Mem.head _ => hGt.le
                  | Mem.tail _ tInTail =>
                    leastOfTail.property.isLeMember tInTail
            },
          ⟩
        else if hEq: head = leastOfTail.val then
          ⟨
            head,
            {
              isMember := Mem.head _
              isLeMember :=
                fun _t tIn =>
                  match tIn with
                  | Mem.head _ => le_refl _
                  | Mem.tail _ tInTail =>
                    hEq ▸ leastOfTail.property.isLeMember tInTail
            },
          ⟩
        else
          False.elim
            (match ord.ltTotal head leastOfTail.val with
            | IsComparable.IsLt lt => hLt lt
            | IsComparable.IsGt gt => hGt gt
            | IsComparable.IsEq eq => hEq eq)


noncomputable def Least.ofHasListOfAll
  (ord: LinearOrder T)
  {s: Set T}
  (isFinite: s.HasListOfAll)
  (sNonempty: t ∈ s)
:
  Least ord.le s
:=
  let list := isFinite.inIff
  let listNonempty :=
    fun (eqEmpty: list.val = []) =>
      let tInEmpty: t ∈ [] :=
        eqEmpty ▸ (list.property t).mp sNonempty
      
      nomatch tInEmpty
  
  let least := list.val.least ord listNonempty
  
  ⟨
    least.val,
    {
      isMember :=
        (list.property least.val).mpr least.property.isMember
      
      isLeMember :=
        fun t tIn =>
          least.property.isLeMember ((list.property t).mp tIn)
    }
  ⟩

def IsMinimal.leastOfConnected
  (isMinimal: IsMinimal lt s t)
  (isConnected: IsConnected lt)
  (ordersIff: ∀ t0 t1, le t0 t1 ↔ lt t0 t1 ∨ t0 = t1)
:
  iIsLeast le s t
:= {
  isMember := isMinimal.isMember
  isLeMember :=
    fun tt ttIn =>
      let ttNotLt := isMinimal.isLeMember ttIn
      
      open IsComparable in
      match isConnected t tt with
      | IsLt isLt => (ordersIff t tt).mpr (Or.inl isLt)
      | IsGt isGt => False.elim (ttNotLt isGt)
      | IsEq isEq => (ordersIff t tt).mpr (Or.inr isEq)
}

def IsUpperBound (_: PartialOrder T) (s: Set T) (t: T): Prop :=
  ∀ tt: ↑s, tt.val ≤ t
def UpperBound (ord: PartialOrder T) (s: Set T) := { t: T // IsUpperBound ord s t }

def IsSupremum (ord: PartialOrder T) (s: Set T) (t: T): Prop :=
  iIsLeast ord.le (IsUpperBound ord s) t
-- @deprecated? it's probably better to use T with IsSupremum.
-- One may deal with situations where the sets whose supremums
-- one deals with are the same sets but defined differently.
-- In such cases the suprema are of different types which
-- prevents eg. stating they are equal.
def Supremum (ord: PartialOrder T) (s: Set T) := Least ord.le (IsUpperBound ord s)

def Supremum.eq
  (a b: Supremum ord s)
:
  a = b
:=
  Least.eq ord a b

def IsSupremum.eq
  (a: IsSupremum ord sA tA)
  (b: IsSupremum ord sB tB)
  (eqSet: sA = sB)
:
  tA = tB
:=
  let bsa := eqSet ▸ b
  
  let sEq := (Supremum.eq ⟨tA, a⟩ ⟨tB, bsa⟩)
  
  Subtype.noConfusion sEq id

def IsFixedPoint (op: T → T): Set T := fun t => t = op t
def FixedPoint (op: T → T): Type u := IsFixedPoint op

def IsMonotonic
  (_: PartialOrder I)
  (_: PartialOrder D)
  (op: I → D)
:
  Prop
:=
  ∀ {t0 t1: I}, t0 ≤ t1 → op t0 ≤ op t1


structure Chain (ord: PartialOrder T) where
  set: Set T
  isChain: IsChain ord.le set

def Chain.eq: {a b: Chain ord} → a.set = b.set → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance
  {T: Type u}
  {ord: PartialOrder T}
:
  CoeSort (Chain ord) (Set T)
where
  coe chain := chain.set

  def Chain.empty: Chain ord := ⟨
    fun _ => False,
    fun _x xInEmpty => False.elim xInEmpty
  ⟩
  
  def Chain.IsEmpty (ch: Chain ord): Prop := ch = empty
  def Chain.AllNin {ord: PartialOrder T} (ch: Chain ord): Prop :=
    ∀ t: T, t ∉ ch.set
  def Chain.NexIn {ord: PartialOrder T} (ch: Chain ord): Prop :=
    ¬∃ t: T, t ∈ ch.set
  
  def Chain.IsEmpty.allNin
    {ch: Chain ord}
    (chEmpty: ch.IsEmpty)
  :
    ch.AllNin
  :=
    fun t tIn => (show t ∈ (empty).set from chEmpty ▸ tIn)
  
  def Chain.AllNin.isEmpty
    {ch: Chain ord}
    (chEmpty: ch.AllNin)
  :
    ch.IsEmpty
  :=
    Chain.eq (funext fun t => propext (Iff.intro
      (fun nope => chEmpty t nope)
      (fun nope => False.elim nope)))
  
  def Chain.NexIn.allNin
    {ch: Chain ord}
    (nexIn: ch.NexIn)
  :
    ch.AllNin
  :=
    nexIn.toAll (fun _ => id)
  
  def Chain.AllNin.nexIn
    {ch: Chain ord}
    (allIn: ch.AllNin)
  :
    ch.NexIn
  :=
    all.notEx allIn (fun _ => id)
  
  def Chain.NexIn.isEmpty
    {ch: Chain ord}
    (nexIn: ch.NexIn)
  :
    ch.IsEmpty
  :=
    nexIn.allNin.isEmpty
  
  def Chain.IsEmpty.nexIn
    {ch: Chain ord}
    (nexIn: ch.IsEmpty)
  :
    ch.NexIn
  :=
    nexIn.allNin.nexIn
  
def IsChain.subset
  {set: Set T}
  (ic: IsChain le set)
  (subset: Set T)
  (isSubset: subset ⊆ set)
:
  IsChain le subset
:=
  fun _e0 e0InSubset _e1 e1InSubset neq =>
    let e0InSet := isSubset e0InSubset
    let e1InSet := isSubset e1InSubset
    
    ic e0InSet e1InSet neq

def IsChain.toComparable
  {set: Set T}
  (ic: IsChain lt set)
  (a b: set)
:
  lt a b ∨ lt b a ∨ a = b
:=
  if h: a.val = b then
    Or.inr (Or.inr (Subtype.eq h))
  else
    (ic a.property b.property h).elim
      (fun ab => Or.inl ab)
      (fun ba => Or.inr (Or.inl ba))

structure IsChainComplete (ord: PartialOrder T): Prop where
  supExists: ∀ ch: Chain ord, ∃ t: T, IsSupremum ord ch.set t

noncomputable def Chain.sup
  (cc: IsChainComplete ord)
  (ch: Chain ord)
:
  Supremum ord ch.set
:=
  (cc.supExists ch).unwrap

def Chain.option.some
  (ord: PartialOrder T)
  (chainOpt: Chain (ord.optionTop))
:
  Chain ord
:= ⟨
  fun t => chainOpt.set t,
  fun _t0 t0Mem _t1 t1Mem neq =>
    (chainOpt.isChain t0Mem t1Mem (Option.neqConfusion neq)).elim
      (fun lt01 => Or.inl lt01)
      (fun lt10 => Or.inr lt10)
⟩

def Chain.sup.empty.isLeast
  (ch: Chain ord)
  (chEmpty: ch.IsEmpty)
  (chSup: Supremum ord ch)
:
  iIsLeast ord.le Set.full chSup.val
:= {
  isMember := trivial
  isLeMember :=
    (fun t _ =>
      let tIsUB: IsUpperBound ord ch t :=
        fun tCh => False.elim (chEmpty.allNin tCh tCh.property)
      chSup.property.isLeMember tIsUB)
}

noncomputable def IsChainComplete.optionTop.sup
  (cc: IsChainComplete ord)
  (chainOpt: Chain ord.optionTop)
:
  Supremum ord.optionTop chainOpt.set
:=
  let chain: Chain ord := Chain.option.some ord chainOpt
  let supChain := chain.sup cc
  
  ⟨
    if none ∈ chainOpt.set then
        none
      else
        supChain.val,
    {
      isMember :=
        (if h: none ∈ chainOpt.set then
          if_pos h ▸ (fun t => PartialOrder.optionTop.noneGreatest t.val)
        else
          if_neg h ▸ fun tSome =>
            match hh: tSome.val with
              | none => h (hh ▸ tSome.property)
              | some t =>
                  let tOptIn: some t ∈ chainOpt.set := hh ▸ tSome.property
                  let tInChain: t ∈ chain.set := tOptIn
                  supChain.property.isMember ⟨t, tInChain⟩)
      isLeMember :=
        fun upperBound ubIsUpperBound =>
          if h: none ∈ chainOpt.set then
            match upperBound with
              | none => if_pos h ▸ (ord.optionTop.le_refl none)
              | some _ => False.elim (ubIsUpperBound ⟨none, h⟩)
          else
            if_neg h ▸ match upperBound with
              | none => trivial
              | some ub =>
                  let ubIsUB: IsUpperBound ord chain.set ub :=
                    fun t => ubIsUpperBound ⟨t, t.property⟩
                  supChain.property.isLeMember ubIsUB
    },
  ⟩

def IsChainComplete.optionTop (cc: IsChainComplete ord):
  IsChainComplete ord.optionTop
:= {
  supExists := fun chainOpt => ⟨
      (IsChainComplete.optionTop.sup cc chainOpt).val,
      (IsChainComplete.optionTop.sup cc chainOpt).property
    ⟩
}

def IsChainComplete.supNoneIffNoneIn
  (cc: IsChainComplete ord)
  (chainOpt: Chain ord.optionTop)
  (sup: Supremum ord.optionTop chainOpt)
:
  sup.val = none ↔ none ∈ chainOpt.set
:=
  let mySup := optionTop.sup cc chainOpt
  let supEq: sup = mySup := Supremum.eq sup mySup
  
  supEq ▸ Iff.intro
    (fun supNone =>
      by_contradiction fun noneNin =>
        let chain: Chain ord := Chain.option.some ord chainOpt
        let supChain := chain.sup cc
        
        let eqSome: (optionTop.sup cc chainOpt).val = supChain.val := by
          unfold optionTop.sup
          exact dif_neg noneNin
        Option.noConfusion (supNone.symm.trans eqSome))
    (fun noneIn =>
      show (optionTop.sup cc chainOpt).val = none from by
        unfold optionTop.sup
        exact dif_pos noneIn)


def Supremum.leIfSetLeSet
  {ord: PartialOrder T}
  {a b: Set T}
  (aSup: Supremum ord a)
  (bSup: Supremum ord b)
  (ab: ∀ aT: a, ∃ bT: b, aT.val ≤ bT)
:
  aSup.val ≤ bSup.val
:=
  let bSupIsUpperBoundOfA:
    IsUpperBound ord a bSup.val
  :=
    fun aT =>
      let bT := (ab aT).unwrap
      bT.property.trans (bSup.property.isMember bT)
  
  aSup.property.isLeMember bSupIsUpperBoundOfA

def Supremum.leUB
  {ord: PartialOrder T}
  {set: Set T}
  (sup: Supremum ord set)
  ⦃t: T⦄
  (supUB: IsUpperBound ord set t)
:
  sup.val ≤ t
:=
  sup.property.isLeMember supUB
