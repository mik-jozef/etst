import ExampleWFCs

namespace Pair
  def dictOrder.Lt: Pair → Pair → Prop
  | zero, zero => False
  | zero, pair _ _ => True
  | pair _ _, zero => False
  | pair lA lB, pair rA rB =>
    Or
      (Lt lA rA)
      (lA = rA ∧ Lt lB rB)
  
  def dictOrder.Le (a b: Pair) := a = b ∨ Lt a b
  
  def dictOrder.ltIrefl
    (aa: Lt a a)
  :
    P
  :=
    match a with
    | zero => aa.elim
    | pair _ _ =>
      aa.elim
        (fun lt => ltIrefl lt)
        (fun ⟨_eq, lt⟩ => ltIrefl lt)
  
  def dictOrder.leRefl a: Le a a := Or.inl rfl
  
  def dictOrder.ltAntisymm
    (ab: Lt a b)
    (ba: Lt b a)
  :
    P
  :=
    match a, b with
    | zero, zero => ab.elim
    | zero, pair _ _ => ba.elim
    | pair _ _, zero => ab.elim
    | pair _aA _aB, pair _bA _bB =>
      ab.elim
        (fun ltAB =>
           ba.elim
             (fun ltBA => ltAntisymm ltAB ltBA)
             (fun ⟨eqA, _⟩ => ltIrefl (eqA ▸ ltAB)))
        (fun ⟨eqA, ltAB⟩ =>
          ba.elim
            (fun ltBA => ltIrefl (eqA ▸ ltBA))
            (fun ⟨_, ltBA⟩ => ltAntisymm ltAB ltBA))
  
  def dictOrder.leAntisymm
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
          (fun baLt => ltAntisymm abLt baLt))
  
  def dictOrder.ltTrans
    (ab: Lt a b)
    (bc: Lt b c)
  :
    Lt a c
  :=
    match a, b, c with
    | _, zero, zero => bc.elim
    | _, pair _ _, zero => bc.elim
    | zero, zero, _ => ab.elim
    | pair _ _, zero, _ => ab.elim
    | zero, pair _ _, pair _ _ => trivial
    | pair _aA _aB, pair _bA _bB, pair _cA _cB =>
      ab.elim
        (fun aLtAB =>
          bc.elim
            (fun aLtBC => Or.inl (ltTrans aLtAB aLtBC))
            (fun ⟨aEqBC, _bLtBC⟩ => Or.inl (aEqBC ▸ aLtAB)))
        (fun ⟨aEqAB, bLtAB⟩ =>
          bc.elim
            (fun aLtBC => Or.inl (aEqAB ▸ aLtBC))
            (fun ⟨aEqBC, bLtBC⟩ =>
              Or.inr
                (And.intro
                  (aEqAB.trans aEqBC)
                  (ltTrans bLtAB bLtBC))))
  
  def dictOrder.leTrans
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
          (fun bcLt => Or.inr (ltTrans abLt bcLt)))
  
  inductive dictOrder.LtTotal (a b: Pair): Prop where
  | IsLt: Lt a b → LtTotal a b
  | IsGt: Lt b a → LtTotal a b
  | IsEq: a = b → LtTotal a b
  
  def dictOrder.ltTotal
    (a b: Pair)
  :
    LtTotal a b
  :=
    open LtTotal in
    match a, b with
    | zero, zero => IsEq rfl
    | zero, pair _ _ => IsLt trivial
    | pair _ _, zero => IsGt trivial
    | pair aA aB, pair bA bB =>
      match ltTotal aA bA with
      | IsLt aLtAB => IsLt (Or.inl aLtAB)
      | IsGt aLtBA => IsGt (Or.inl aLtBA)
      | IsEq aEqAB =>
        match ltTotal aB bB with
        | IsLt bLtAB =>
            IsLt (Or.inr (And.intro aEqAB bLtAB))
        | IsGt bLtBA =>
            IsGt (Or.inr (And.intro aEqAB.symm bLtBA))
        | IsEq bEqAB =>
            IsEq (congr (congr rfl aEqAB) bEqAB)
  
  def dictOrder.leTotal
    (a b: Pair)
  :
    Le a b ∨ Le b a
  :=
    open LtTotal in
    match ltTotal a b with
    | IsLt ab => Or.inl (Or.inr ab)
    | IsGt ba => Or.inr (Or.inr ba)
    | IsEq eq => eq ▸ Or.inl (leRefl _)
  
  
  noncomputable instance Pair.dictOrder: LinearOrder Pair where
    le := dictOrder.Le
    lt := dictOrder.Lt
    
    lt_iff_le_not_le _ _ :=
      Iff.intro
        (fun ab =>
          And.intro
            (Or.inr ab)
            (fun ba =>
              ba.elim
                (fun eq => dictOrder.ltIrefl (eq ▸ ab))
                (fun ba => dictOrder.ltAntisymm ab ba)))
        (fun ⟨abLe, notBaLe⟩ =>
          abLe.elim
            (fun eq => False.elim (notBaLe (Or.inl eq.symm)))
            id)
    
    le_refl _ := Or.inl rfl
    
    le_antisymm _ _ := dictOrder.leAntisymm
    
    le_trans _ _ _ := dictOrder.leTrans
    
    le_total := dictOrder.leTotal
    
    decidableLE := inferInstance
end Pair