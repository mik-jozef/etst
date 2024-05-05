import Chain
import PairDictOrder
import Utils
import WellFoundedOfLeast


namespace Pair
  inductive depthDictOrder.Lt (a b: Pair): Prop
  | EqDepth: a.depth = b.depth → dictOrder.Lt a b → Lt a b
  | NeqDepth: a.depth < b.depth → Lt a b
  
  def depthDictOrder.Le (a b: Pair) := Lt a b ∨ a = b
  
  
  def depthDictOrder.Lt.depthEq
    (lt: Lt a b)
    (eqDepth: a.depth = b.depth)
  :
    dictOrder.Lt a b
  :=
    lt.rec
      (fun _ lt => lt)
      (fun ltDepth =>
        False.elim (Nat.lt_irrefl _ (eqDepth ▸ ltDepth)))
  
  def depthDictOrder.Lt.depthNeq
    (lt: Lt a b)
    (neqDepth: a.depth ≠ b.depth)
  :
    a.depth < b.depth
  :=
    lt.rec
      (fun eq _ => False.elim (neqDepth eq))
      id
  
  
  def depthDictOrder.Lt.irefl
    (aa: Lt a a)
  :
    P
  :=
    (aa.depthEq rfl).irefl
  
  def depthDictOrder.leRefl a: Le a a := Or.inr rfl
  
  def depthDictOrder.Lt.antisymm
    (ab: Lt a b)
    (ba: Lt b a)
  :
    P
  :=
    if h: a.depth = b.depth then
      (ab.depthEq h).antisymm (ba.depthEq h.symm)
    else
      Nat.ltAntisymm
        (ab.depthNeq h)
        (ba.depthNeq (fun eq => h eq.symm))
  
  def depthDictOrder.Le.antisymm
    (ab: Le a b)
    (ba: Le b a)
  :
    a = b
  :=
    ab.elim
      (fun abLt =>
        ba.elim
          (fun baLt => depthDictOrder.Lt.antisymm abLt baLt)
          (fun eq => eq.symm))
      (fun eq => eq)
  
  def depthDictOrder.Lt.trans
    (ab: Lt a b)
    (bc: Lt b c)
  :
    Lt a c
  :=
    if hAB: a.depth = b.depth then
      if hBC: b.depth = c.depth then
        Lt.EqDepth
          (hAB.trans hBC)
          ((ab.depthEq hAB).trans (bc.depthEq hBC))
      else
        Lt.NeqDepth (hAB ▸ bc.depthNeq hBC)
    else
      if hBC: b.depth = c.depth then
        Lt.NeqDepth (hBC ▸ ab.depthNeq hAB)
      else
        Lt.NeqDepth ((ab.depthNeq hAB).trans (bc.depthNeq hBC))
  
  def depthDictOrder.Le.trans
    (ab: Le a b)
    (bc: Le b c)
  :
    Le a c
  :=
    ab.elim
      (fun abLt =>
        bc.elim
          (fun bcLt => Or.inl (depthDictOrder.Lt.trans abLt bcLt))
          (fun eq => eq ▸ ab))
      (fun eq => eq ▸ bc)
  
  def depthDictOrder.ltTotal
    (a b: Pair)
  :
    IsComparable Lt a b
  :=
    if h: a.depth = b.depth then
      (dictOrder.ltTotal a b).rec
        (fun lt => IsComparable.IsLt (Lt.EqDepth h lt))
        (fun gt => IsComparable.IsGt (Lt.EqDepth h.symm gt))
        (fun eq => IsComparable.IsEq eq)
    else
      (Nat.le_total a.depth b.depth).elim
        (fun le =>
          le.eq_or_lt.elim
            (fun eq => False.elim (h eq))
            (fun lt => IsComparable.IsLt (Lt.NeqDepth lt)))
        (fun ge =>
          ge.eq_or_lt.elim
            (fun eq => False.elim (h eq.symm))
            (fun gt => IsComparable.IsGt (Lt.NeqDepth gt)))
  
  def depthDictOrder.leTotal
    (a b: Pair)
  :
    Le a b ∨ Le b a
  :=
    open IsComparable in
    match ltTotal a b with
    | IsLt ab => Or.inl (Or.inl ab)
    | IsGt ba => Or.inr (Or.inl ba)
    | IsEq eq => eq ▸ Or.inl (leRefl _)
  
  
  noncomputable instance depthDictOrder: LinearOrder Pair where
    le := depthDictOrder.Le
    lt := depthDictOrder.Lt
    
    lt_iff_le_not_le _ _ :=
      Iff.intro
        (fun ab =>
          And.intro
            (Or.inl ab)
            (fun ba =>
              ba.elim
                (fun ba => ab.antisymm ba)
                (fun eq => (eq ▸ ab).irefl)))
        (fun ⟨abLe, notBaLe⟩ =>
          abLe.elim
            id
            (fun eq => False.elim (notBaLe (Or.inr eq.symm))))
    
    le_refl _ := Or.inr rfl
    
    le_antisymm _ _ := depthDictOrder.Le.antisymm
    
    le_trans _ _ _ := depthDictOrder.Le.trans
    
    le_total := depthDictOrder.leTotal
    
    decidableLE := inferInstance
  
  def depthDictOrder.zeroLeAny (a: Pair): zero ≤ a :=
    match a with
    | zero => Or.inr rfl
    | pair _ _ => Or.inl (Lt.NeqDepth (Nat.zero_lt_succ _))
  
  def depthDictOrder.nopeLtZero
    (a: Pair)
    (aLtZero: a < zero)
  :
    P
  :=
    False.elim
      (match a with
      | zero =>
        match aLtZero with
        | Lt.EqDepth _ lt => lt
        | Lt.NeqDepth depthLt => Nat.lt_irrefl _ depthLt
      | pair _ _ =>
        match aLtZero with
        | Lt.EqDepth _ lt => lt
        | Lt.NeqDepth depthLt => Nat.not_lt_zero _ depthLt)
  
  def depthDictOrder.Le.ltAntisymm
    (ab: Le a b)
    (ba: Lt b a)
  :
    P
  :=
    ab.elim
      (fun abLt => ba.antisymm abLt)
      (fun eq => (eq ▸ ba).irefl)
  
  def depthDictOrder.Lt.leAntisymm
    (ab: Lt a b)
    (ba: Le b a)
  :
    P
  :=
    ba.elim
      (fun baLt => ab.antisymm baLt)
      (fun eq => (eq.symm ▸ ab).irefl)
  
  
  def depthDictOrder.nonemptyHasLeast
    (s: Set Pair)
    {t: Pair}
    (sNonempty: t ∈ s)
  :
    ∃ least, iIsLeast Le s least
  :=
    let sBounded: Set Pair :=
      fun p => s p ∧ p.depth ≤ t.depth
    
    let sBoundedNonempty: t ∈ sBounded :=
      And.intro sNonempty (le_refl _)
    
    let sBounded_is_finite :=
      depth.boundedByIsFinite
        fun p (pInS: p ∈ sBounded) =>
          Nat.lt_succ_of_le pInS.right
    
    let ⟨lob, isLob⟩ :=
       Least.ofFinite depthDictOrder sBounded_is_finite sBoundedNonempty
    
    ⟨
      lob,
      {
        isMember := isLob.isMember.left,
        isLeMember :=
          fun p pInS =>
            match Nat.linearOrder.ltTotal p.depth t.depth with
            | IsComparable.IsLt pt =>
                isLob.isLeMember (And.intro pInS pt.le)
            | IsComparable.IsGt tp =>
                let lob_le_t := isLob.isLeMember
                  (And.intro sNonempty (le_refl _))
                lob_le_t.trans (Or.inl (Lt.NeqDepth tp))
            | IsComparable.IsEq eq =>
              isLob.isLeMember (And.intro pInS (eq ▸ le_refl _))
      }
    ⟩
  
  def depthDictOrder.isWellFounded:
    WellFounded depthDictOrder.Lt
  :=
    well_founded_of_least
      depthDictOrder.toPartialOrder
      depthDictOrder.nonemptyHasLeast
  
  def depthDictOrder.wfRel: WellFoundedRelation Pair := {
    rel := depthDictOrder.Lt,
    wf := depthDictOrder.isWellFounded
  }
  
end Pair
