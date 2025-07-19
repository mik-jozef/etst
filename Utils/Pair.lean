/-
  Proofs of properties of definitions in @file:/WFC/Pair.lean.
  See that file for the definitions themselves.
-/

import WFC.Ch5_PairSalgebra


-- Equality of pairs is decidable.
def decideEq: (a b: Pair) → Decidable (a = b)
| Pair.zero, Pair.zero => isTrue rfl
| Pair.zero, Pair.pair _ _ => isFalse (fun nope => Pair.noConfusion nope)
| Pair.pair _ _, Pair.zero => isFalse (fun nope => Pair.noConfusion nope)
| Pair.pair aA aB, Pair.pair bA bB =>
  let eqA := decideEq aA bA
  let eqB := decideEq aB bB
  
  match eqA, eqB with
  | isTrue aEq, isTrue bEq => isTrue (congr (congr rfl aEq) bEq)
  | isFalse aNeq, _ =>
    isFalse
      (fun nope => (Pair.noConfusion nope fun aEq _ => aNeq aEq))
  | _, isFalse bNeq =>
    isFalse
      (fun nope => (Pair.noConfusion nope fun _ bEq => bNeq bEq))

instance Pair.decidableEq: DecidableEq Pair := decideEq

namespace Pair
  def zeroLtSizeOf: (p: Pair) → 0 < sizeOf p
  | zero => Nat.zero_lt_succ _
  | pair a b => by simp
  
  def fromNat.injEq
    (eq: fromNat n = fromNat m)
  :
    n = m
  :=
    match n, m with
    | Nat.zero, Nat.zero => rfl
    | Nat.zero, Nat.succ _ => Pair.noConfusion eq
    | Nat.succ _, Nat.zero => Pair.noConfusion eq
    | Nat.succ _nPred, Nat.succ _mPred =>
      let eqFromPred :=
        Pair.noConfusion eq fun predEq _ => predEq
      
      congrArg Nat.succ (fromNat.injEq eqFromPred)
  
  def fromNat.injNeq:
    n ≠ m → fromNat n ≠ fromNat m
  :=
    injEq.contra
  
  def fromNat.fromSuccEq
    (n: Nat)
  :
    fromNat (Nat.succ n) = pair (fromNat n) zero
  :=
    rfl
  
  def fromNat.eqSuccOfEq
    (eq: fromNat n = p)
  :
    fromNat (Nat.succ n) = pair p zero
  :=
    eq ▸ fromSuccEq n
  
  
  def depthSuccLeL (a b: Pair):
    Nat.succ a.depth ≤ (pair a b).depth
  :=
    Nat.succ_le_succ (Nat.le_max_left a.depth b.depth)
  
  def depthSuccLeR (a b: Pair):
    Nat.succ b.depth ≤ (pair a b).depth
  :=
    Nat.succ_le_succ (Nat.le_max_right a.depth b.depth)
  
  
  def depthLeL (a b: Pair):
    a.depth ≤ (pair a b).depth
  :=
    Nat.le_of_succ_le (depthSuccLeL a b)
  
  def depthLeR (a b: Pair):
    b.depth ≤ (pair a b).depth
  :=
    Nat.le_of_succ_le (depthSuccLeR a b)
  
  
  def depthLtL (a b: Pair):
    a.depth < (pair a b).depth
  :=
    depthSuccLeL a b
  
  def depthLtR (a b: Pair):
    b.depth < (pair a b).depth
  :=
    depthSuccLeR a b
  
  def depth.casesEq (a b: Pair):
    Or
      (And
        ((pair a b).depth = Nat.succ a.depth)
        (b.depth ≤ a.depth))
      (And
        ((pair a b).depth = Nat.succ b.depth)
        (a.depth < b.depth))
  :=
    (max_cases a.depth b.depth).elim
      (fun ⟨eq, le⟩ => Or.inl (And.intro (congr rfl eq) le))
      (fun ⟨eq, lt⟩ => Or.inr (And.intro (congr rfl eq) lt))
  
  
  def depth.leZth (aA aB bA bB: Pair):
    (pair aA bA).depth
      <
    (pair (pair aA aB) (pair bA bB)).depth
  :=
    let leSA := Pair.depthSuccLeL aA aB
    let leSB := Pair.depthSuccLeL bA bB
    (Pair.depth.casesEq aA bA).elim
      (fun ⟨eq, _⟩ => eq ▸ (leSA.trans_lt (Pair.depthLtL _ _)))
      (fun ⟨eq, _⟩ => eq ▸ (leSB.trans_lt (Pair.depthLtR _ _)))
  
  def depth.leZthFst (aA aB bA bB: Pair):
    (pair aA bB).depth
      <
    (pair (pair aA aB) (pair bA bB)).depth
  :=
    let leSA := Pair.depthSuccLeL aA aB
    let leSB := Pair.depthSuccLeR bA bB
    (Pair.depth.casesEq aA bB).elim
      (fun ⟨eq, _⟩ => eq ▸ (leSA.trans_lt (Pair.depthLtL _ _)))
      (fun ⟨eq, _⟩ => eq ▸ (leSB.trans_lt (Pair.depthLtR _ _)))
  
  def depth.zeroEq: depth Pair.zero = 0 := rfl
  
  def depth.eqZeroOfEqZero
    (eqZero: depth p = 0)
  :
    p = zero
  :=
    match p with
    | zero => rfl
    | pair _ _ => Nat.noConfusion eqZero
  
  
  def depth.eqL
    (ba: b.depth ≤ a.depth)
  :
    (pair a b).depth = Nat.succ a.depth
  :=
    congr rfl (max_eq_iff.mpr (Or.inl (And.intro rfl ba)))
  
  def depth.eqR
    (ab: a.depth ≤ b.depth)
  :
    (pair a b).depth = Nat.succ b.depth
  :=
    congr rfl (max_eq_iff.mpr (Or.inr (And.intro rfl ab)))
  
  def depth.ltLOfEqSucc
    (ltSucc: (pair a b).depth < n.succ)
  :
    a.depth < n
  :=
    (casesEq a b).elim
      (fun ⟨eq, _⟩ =>
        Nat.lt_of_succ_lt_succ (eq ▸ ltSucc))
      (fun ⟨eq, lt⟩ =>
        let ltSucc := (Nat.succ_lt_succ lt).trans (eq ▸ ltSucc)
        Nat.lt_of_succ_lt_succ ltSucc)
  
  def depth.ltROfEqSucc
    (ltSucc: (pair a b).depth < n.succ)
  :
    b.depth < n
  :=
    (casesEq a b).elim
      (fun ⟨eq, le⟩ =>
        le.trans_lt (Nat.lt_of_succ_lt_succ (eq ▸ ltSucc)))
      (fun ⟨eq, _⟩ =>
        Nat.lt_of_succ_lt_succ (eq ▸ ltSucc))
  
  
  def isNatEncoding.decidable (p: Pair):
    Decidable (IsNatEncoding p)
  :=
    match p with
    | zero => isTrue trivial
    | pair _ (pair _ _) =>
      isFalse (fun nope => Pair.noConfusion nope.right)
    | pair a zero =>
      match isNatEncoding.decidable a with
      | isTrue isNatA =>
        isTrue (And.intro isNatA rfl)
      | isFalse aNotNat =>
        isFalse (fun nope => aNotNat nope.left)
  
  
  def fromNat.isNatEncoding (n: Nat):
    IsNatEncoding (fromNat n)
  :=
    match n with
    | Nat.zero => trivial
    | Nat.succ pred => And.intro (isNatEncoding pred) rfl
  
  def fromNat.depthEq: (n: Nat) → (Pair.fromNat n).depth = n
  | Nat.zero => rfl
  | Nat.succ pred =>
    (depth.casesEq (fromNat pred) zero).elim
      (fun ⟨eq, _⟩ =>
        eq ▸ congr rfl (depthEq pred))
      (fun ⟨_, ltZero⟩ =>
        False.elim (Nat.not_lt_zero _ ltZero))
  
  
  def depth.nat.eqSuccDepthPred
    (isNat: IsNatEncoding (pair a b))
  :
    depth (pair a b)
      =
    Nat.succ (depth a)
  :=
    (depth.casesEq a b).elim
      (fun ⟨eq, _⟩ => eq)
      (fun ⟨_, le⟩ =>
        False.elim (Nat.not_lt_zero _ (isNat.right ▸ le)))
  
  def depth.nat.injEq
    (isNatA: IsNatEncoding a)
    (isNatB: IsNatEncoding b)
    (eq: depth a = depth b)
  :
    a = b
  :=
    match a, b with
    | zero, zero => rfl
    | zero, pair bA bB =>
      let eqL: 0 = depth (pair bA bB) :=
        depth.zeroEq.symm.trans eq
      let eqR := depth.nat.eqSuccDepthPred isNatB
      
      Nat.noConfusion (eqL.trans eqR)
    | pair aA aB, zero =>
      let eqL: 0 = depth (pair aA aB) :=
        depth.zeroEq.symm.trans eq.symm
      let eqR := depth.nat.eqSuccDepthPred isNatA
      
      Nat.noConfusion (eqL.trans eqR)
    | pair aA aB, pair bA bB =>
      let eqPredSucc: Nat.succ (depth aA) = Nat.succ (depth bA) :=
        (depth.nat.eqSuccDepthPred isNatA).symm.trans
          (eq.trans (depth.nat.eqSuccDepthPred isNatB))
      let eqPred: depth aA = depth bA :=
        Nat.noConfusion eqPredSucc id
      let eqA: aA = bA :=
        depth.nat.injEq isNatA.left isNatB.left eqPred
      let eqB: aB = bB :=
        isNatA.right.trans isNatB.right.symm
      
      congr (congr rfl eqA) eqB
  
  def depth.nat.injNeq
    (isNatA: IsNatEncoding a)
    (isNatB: IsNatEncoding b)
    (neq: a ≠ b)
  :
    depth a ≠ depth b
  :=
    (depth.nat.injEq isNatA isNatB).contra neq
  
  def fromNat.eqOfDepth
    (isNat: IsNatEncoding p)
  :
    fromNat p.depth = p
  :=
    match p with
    | zero => rfl
    | pair _ zero =>
      depth.nat.eqSuccDepthPred isNat ▸
      fromNat.eqSuccOfEq (fromNat.eqOfDepth isNat.left)
  
  def IsNatEncoding.toNat
    (isNat: IsNatEncoding p)
  :
    Nat
  :=
    match p with
    | zero => 0
    | pair _ _ => (toNat isNat.left).succ
  
  def IsNatEncoding.toNatFromNatEq
    (isNat: IsNatEncoding p)
  :
    fromNat isNat.toNat = p
  :=
    -- Termination ought to be automatically inferred here.
    -- match p with
    -- | zero => rfl
    -- | pair pred z =>
    --   isNat.right ▸
    --   fromNat.eqSuccOfEq (toNatFromNatEq isNat.left)
    
    let isNatToEq:
      ∀ (isNat : IsNatEncoding p), fromNat (toNat isNat) = p
    :=
      p.rec
        (fun _ => rfl)
        (fun _ _ ihPred _ isNat =>
          -- Inlining this variable causes an error.
          let eqWithZ := fromNat.eqSuccOfEq (ihPred isNat.left)
          isNat.right ▸ eqWithZ)
    
    isNatToEq isNat
  
  
  def arrayLength.eqSuccTail (a b: Pair):
    (pair a b).arrayLength = Nat.succ b.arrayLength
  :=
    rfl
  
  def arrayLength.ltTail (a b: Pair):
    b.arrayLength < (pair a b).arrayLength
  :=
    Nat.lt_succ_self b.arrayLength
  
  def arrayLength.ltOfLtTail
    (ab: tailA.arrayLength < tailB.arrayLength)
    (headA headB: Pair)
  :
    (pair headA tailA).arrayLength < (pair headB tailB).arrayLength
  :=
    Nat.succ_lt_succ ab
  
  def arrayLength.leOfLeTail
    (ab: tailA.arrayLength ≤ tailB.arrayLength)
    (headA headB: Pair)
  :
    (pair headA tailA).arrayLength ≤ (pair headB tailB).arrayLength
  :=
    Nat.succ_le_succ ab
  
  def arrayLength.eqOfEqTail
    (ab: tailA.arrayLength = tailB.arrayLength)
    (headA headB: Pair)
  :
    (pair headA tailA).arrayLength = (pair headB tailB).arrayLength
  :=
    by unfold arrayLength; exact congr rfl ab
  
  
  def arrayAt.tailEq
    (eqAt: (pair head tail).arrayAt n.succ = p)
  :
    tail.arrayAt n = p
  :=
    eqAt
  
  def arrayAt.consEq
    (eqAt: tail.arrayAt n = p)
    (head: Pair)
  :
    (pair head tail).arrayAt n.succ = p
  :=
    eqAt
  
  def arrayAt.nopeNoneOfWithinBounds
    {arr: Pair}
    (withinBounds: n < arr.arrayLength)
    (eqNone: arr.arrayAt n = none)
  :
    P
  :=
    match arr, n with
    | zero, _ => False.elim (Nat.not_lt_zero _ withinBounds)
    | pair _ tail, Nat.succ nPred =>
      let nPredWithinBounds:
        nPred < tail.arrayLength
      :=
        Nat.lt_of_succ_lt_succ withinBounds
      
      nopeNoneOfWithinBounds nPredWithinBounds eqNone
  
  def arrayAt.lengthLeOfNone
    {arr: Pair}
    (eqNone: arr.arrayAt n = none)
  :
    arr.arrayLength ≤ n
  :=
    match arr, n with
    | zero, _ => Nat.zero_le _
    | pair _ _, Nat.zero => Option.noConfusion eqNone
    | pair _ _, Nat.succ _ =>
      let nPredLeTail :=
        arrayAt.lengthLeOfNone (arrayAt.tailEq eqNone)
      
      Nat.succ_le_succ nPredLeTail
  
  def arrayAt.lengthGtOfSome
    {arr: Pair}
    (eqSome: arr.arrayAt n = some p)
  :
    n < arr.arrayLength
  :=
    match arr, n with
    | zero, _ => Option.noConfusion eqSome
    | pair _ _, Nat.zero => Nat.zero_lt_succ _
    | pair _ _, Nat.succ _ =>
      let nPredLtTail :=
        arrayAt.lengthGtOfSome (arrayAt.tailEq eqSome)
      
      Nat.succ_lt_succ nPredLtTail
  
  
  def arrayLast.eqLastOfTail
    (eq: arrayLast head (pair tailHead tailTail) = p)
  :
    tailHead.arrayLast tailTail = p
  :=
    eq
  
  def arrayLast.eqLastOfCons
    (eq: arrayLast tailHead tailTail = p)
    (head: Pair)
  :
    head.arrayLast (pair tailHead tailTail) = p
  :=
    eq
  
  def arrayLast.eqOfEqAt
    (eqAt: (pair head tail).arrayAt n = some p)
    (eqLength: (pair head tail).arrayLength = n.succ)
  :
    head.arrayLast tail = p
  :=
    match tail, n with
    | zero, Nat.zero => Option.some.inj eqAt
    | zero, Nat.succ _ => Nat.noConfusion eqLength Nat.noConfusion
    | pair _tailHead _tailTail, Nat.zero =>
      Nat.noConfusion eqLength Nat.noConfusion
    | pair tailHead tailTail, Nat.succ _nPred =>
      let eqTailLength :=
        eqLength.symm.trans
          (arrayLength.eqSuccTail head (pair tailHead tailTail))
      
      let ih := arrayLast.eqOfEqAt
        (arrayAt.tailEq eqAt)
        (Nat.noConfusion eqTailLength Eq.symm)
      
      eqLastOfCons ih head
  
  
  def arrayUpToLast.lengthEqTail
    (head tail: Pair)
  :
    (head.arrayUpToLast tail).arrayLength = tail.arrayLength
  :=
    match tail with
    | zero => rfl
    | pair tailHead tailTail =>
      let ih := lengthEqTail tailHead tailTail
      
      arrayLength.eqOfEqTail
        ih head (tailHead.arrayUpToLast tailTail)
  
  def arrayUpToLast.succLengthEq
    (head tail: Pair)
  :
    (pair head tail).arrayLength
      =
    Nat.succ (head.arrayUpToLast tail).arrayLength
  :=
    (lengthEqTail head tail) ▸
    arrayLength.eqSuccTail head tail
  
  def arrayUpToLast.lengthLt
    (head tail: Pair)
  :
    (head.arrayUpToLast tail).arrayLength
      <
    (pair head tail).arrayLength
  :=
    match tail with
    | zero => Nat.zero_lt_succ _
    | pair tailHead tailTail =>
      let ih := lengthLt tailHead tailTail
      
      arrayLength.ltOfLtTail ih head (tailHead.arrayUpToLast tailTail)
  
  def arrayUpToLast.lengthEqOfNone
    (eqSome: (pair head tail).arrayAt n = some p)
    (eqNone: (head.arrayUpToLast tail).arrayAt n = none)
  :
    (pair head tail).arrayLength = n.succ
  :=
    let lengthPredLeN :=
      (succLengthEq head tail).symm ▸
      Nat.succ_le_succ (arrayAt.lengthLeOfNone eqNone)
    
    let nLtLength := arrayAt.lengthGtOfSome eqSome
    
    (Nat.eq_of_lt_of_le_succ nLtLength lengthPredLeN).symm
  
  
  def depth.setOfAllBelowIsFinite
    (n: Nat)
  :
    Set.HasListOfAll (fun (p: Pair) => p.depth < n)
  :=
    match n with
    | Nat.zero =>
      ⟨
        [],
        fun ⟨_p, pInS⟩ => False.elim (Nat.not_lt_zero _ pInS)
      ⟩
    | Nat.succ nPred =>
      let sPred: Set Pair := fun p => p.depth < nPred
      
      let isFinitePred := setOfAllBelowIsFinite nPred
      
      Set.HasListOfAll.ofPairsOfFinite
        isFinitePred
        isFinitePred
        Pair.pair
        _
        ⟨
          [Pair.zero],
          fun ⟨c, ⟨cDepthLt, neqMapped⟩⟩ =>
            let cEqZero: c = zero :=
              match c with
              | zero => rfl
              | pair a b =>
                let aInSPred: a ∈ sPred := ltLOfEqSucc cDepthLt
                let bInSPred: b ∈ sPred := ltROfEqSucc cDepthLt
                
                False.elim (neqMapped aInSPred bInSPred rfl)
            
            cEqZero ▸ List.Mem.head [],
        ⟩
  
  def depth.boundedByIsFinite
    {s: Set Pair}
    (isBounded: ∀ p ∈ s, p.depth < n)
  :
    s.HasListOfAll
  :=
    Set.HasListOfAll.ofIsLeFinite
      (setOfAllBelowIsFinite n)
      (fun p inS => isBounded p inS)
  
  
  def pairS3 (a b: Set3 Pair): Set3 Pair := {
    defMem :=
      fun p => ∃ (pa: a.defMem) (pb: b.defMem), p = pair pa pb
    posMem :=
      fun p => ∃ (pa: a.posMem) (pb: b.posMem), p = pair pa pb
    defLePos :=
      fun _ ⟨⟨pa, isDefA⟩, ⟨pb, isDefB⟩, eq⟩ =>
        ⟨⟨pa, isDefA.toPos⟩, ⟨pb, isDefB.toPos⟩, eq⟩
  }
  
end Pair
