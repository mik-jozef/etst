import Utils
import PairDictOrder


namespace Pair
  inductive depthDictOrder.Lt (a b: Pair): Prop
  | EqDepth: a.depth = b.depth → dictOrder.Lt a b → Lt a b
  | NeqDepth: a.depth < b.depth → Lt a b
  
  def depthDictOrder.Le (a b: Pair) := a = b ∨ Lt a b
  
  
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
  
  def depthDictOrder.leRefl a: Le a a := Or.inl rfl
  
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
      (fun eq => eq)
      (fun abLt =>
        ba.elim
          (fun eq => eq.symm)
          (fun baLt => depthDictOrder.Lt.antisymm abLt baLt))
  
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
      (fun eq => eq ▸ bc)
      (fun abLt =>
        bc.elim
          (fun eq => eq ▸ ab)
          (fun bcLt => Or.inr (depthDictOrder.Lt.trans abLt bcLt)))
  
  inductive depthDictOrder.LtTotal (a b: Pair): Prop where
  | IsLt: Lt a b → LtTotal a b
  | IsGt: Lt b a → LtTotal a b
  | IsEq: a = b → LtTotal a b
  
  def depthDictOrder.ltTotal
    (a b: Pair)
  :
    LtTotal a b
  :=
    if h: a.depth = b.depth then
      (dictOrder.ltTotal a b).rec
        (fun lt => LtTotal.IsLt (Lt.EqDepth h lt))
        (fun gt => LtTotal.IsGt (Lt.EqDepth h.symm gt))
        (fun eq => LtTotal.IsEq eq)
    else
      (Nat.le_total a.depth b.depth).elim
        (fun le =>
          le.eq_or_lt.elim
            (fun eq => False.elim (h eq))
            (fun lt => LtTotal.IsLt (Lt.NeqDepth lt)))
        (fun ge =>
          ge.eq_or_lt.elim
            (fun eq => False.elim (h eq.symm))
            (fun gt => LtTotal.IsGt (Lt.NeqDepth gt)))
  
  def depthDictOrder.leTotal
    (a b: Pair)
  :
    Le a b ∨ Le b a
  :=
    open LtTotal in
    match ltTotal a b with
    | IsLt ab => Or.inl (Or.inr ab)
    | IsGt ba => Or.inr (Or.inr ba)
    | IsEq eq => eq ▸ Or.inl (leRefl _)
  
  
  noncomputable instance depthDictOrder: LinearOrder Pair where
    le := depthDictOrder.Le
    lt := depthDictOrder.Lt
    
    lt_iff_le_not_le _ _ :=
      Iff.intro
        (fun ab =>
          And.intro
            (Or.inr ab)
            (fun ba =>
              ba.elim
                (fun eq => (eq ▸ ab).irefl)
                (fun ba => ab.antisymm ba)))
        (fun ⟨abLe, notBaLe⟩ =>
          abLe.elim
            (fun eq => False.elim (notBaLe (Or.inl eq.symm)))
            id)
    
    le_refl _ := Or.inl rfl
    
    le_antisymm _ _ := depthDictOrder.Le.antisymm
    
    le_trans _ _ _ := depthDictOrder.Le.trans
    
    le_total := depthDictOrder.leTotal
    
    decidableLE := inferInstance
  
  def depthDictOrder.zeroLeAny (a: Pair): zero ≤ a :=
    match a with
    | zero => Or.inl rfl
    | pair _ _ => Or.inr (Lt.NeqDepth (Nat.zero_lt_succ _))
  
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
      (fun eq => (eq ▸ ba).irefl)
      (fun abLt => ba.antisymm abLt)
  
  def depthDictOrder.Lt.leAntisymm
    (ab: Lt a b)
    (ba: Le b a)
  :
    P
  :=
    ba.elim
      (fun eq => (eq.symm ▸ ab).irefl)
      (fun baLt => ab.antisymm baLt)
end Pair
