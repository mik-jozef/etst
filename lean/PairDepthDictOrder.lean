import PairDictOrder

namespace Pair
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
  
  
  def fromNat.depthEq: (n: Nat) → (Pair.fromNat n).depth = n
  | Nat.zero => rfl
  | Nat.succ pred =>
      (depth.casesEq (fromNat pred) zero).elim
        (fun ⟨eq, _⟩ =>
          eq ▸ congr rfl (depthEq pred))
        (fun ⟨_, ltZero⟩ =>
          False.elim (Nat.not_lt_zero _ ltZero))
  
  
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
  
  
  def depthDictOrder.ltIrefl
    (aa: Lt a a)
  :
    P
  :=
    dictOrder.ltIrefl (aa.depthEq rfl)
  
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
      Nat.lt_antisymm
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
                (fun eq => depthDictOrder.ltIrefl (eq ▸ ab))
                (fun ba => depthDictOrder.Lt.antisymm ab ba)))
        (fun ⟨abLe, notBaLe⟩ =>
          abLe.elim
            (fun eq => False.elim (notBaLe (Or.inl eq.symm)))
            id)
    
    le_refl _ := Or.inl rfl
    
    le_antisymm _ _ := depthDictOrder.Le.antisymm
    
    le_trans _ _ _ := depthDictOrder.Le.trans
    
    le_total := depthDictOrder.leTotal
    
    decidableLE := inferInstance
end Pair
