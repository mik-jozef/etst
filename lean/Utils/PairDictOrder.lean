/-
  The dictionary order on pairs, the base case being
  
      zero < pair a b \,.
-/

import WFC.Pair

namespace Pair
  namespace dictOrder
    def Lt: Pair → Pair → Prop
    | zero, zero => False
    | zero, pair _ _ => True
    | pair _ _, zero => False
    | pair lA lB, pair rA rB =>
      Or
        (Lt lA rA)
        (lA = rA ∧ Lt lB rB)
    
    def Le (a b: Pair) := Lt a b ∨ a = b
    
    def Lt.irefl
      (aa: Lt a a)
    :
      P
    :=
      match a with
      | zero => aa.elim
      | pair _ _ =>
        aa.elim
          (fun lt => lt.irefl)
          (fun ⟨_eq, lt⟩ => lt.irefl)
    
    def leRefl a: Le a a := Or.inr rfl
    
    def Lt.antisymm
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
              (fun ltBA => ltAB.antisymm ltBA)
              (fun ⟨eqA, _⟩ => (eqA ▸ ltAB).irefl))
          (fun ⟨eqA, ltAB⟩ =>
            ba.elim
              (fun ltBA => (eqA ▸ ltBA).irefl)
              (fun ⟨_, ltBA⟩ => ltAB.antisymm ltBA))
    
    def Le.antisymm
      (ab: Le a b)
      (ba: Le b a)
    :
      a = b
    :=
      ab.elim
        (fun abLt =>
          ba.elim
            (fun baLt => abLt.antisymm baLt)
            (fun eq => eq.symm))
        (fun eq => eq)
    
    def Lt.trans
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
              (fun aLtBC => Or.inl (aLtAB.trans aLtBC))
              (fun ⟨aEqBC, _bLtBC⟩ => Or.inl (aEqBC ▸ aLtAB)))
          (fun ⟨aEqAB, bLtAB⟩ =>
            bc.elim
              (fun aLtBC => Or.inl (aEqAB ▸ aLtBC))
              (fun ⟨aEqBC, bLtBC⟩ =>
                Or.inr
                  (And.intro
                    (aEqAB.trans aEqBC)
                    (bLtAB.trans bLtBC))))
    
    def Le.trans
      (ab: Le a b)
      (bc: Le b c)
    :
      Le a c
    :=
      ab.elim
        (fun abLt =>
          bc.elim
            (fun bcLt => Or.inl (abLt.trans bcLt))
            (fun eq => eq ▸ ab))
        (fun eq => eq ▸ bc)
    
    def ltTotal
      (a b: Pair)
    :
      IsComparable Lt a b
    :=
      open IsComparable in
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
    
    def leTotal
      (a b: Pair)
    :
      Le a b ∨ Le b a
    :=
      open IsComparable in
      match ltTotal a b with
      | IsLt ab => Or.inl (Or.inl ab)
      | IsGt ba => Or.inr (Or.inl ba)
      | IsEq eq => eq ▸ Or.inl (leRefl _)
  end dictOrder
  
  noncomputable local instance dictOrder: LinearOrder Pair where
    le := dictOrder.Le
    lt := dictOrder.Lt
    
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
    
    le_antisymm _ _ := dictOrder.Le.antisymm
    
    le_trans _ _ _ := dictOrder.Le.trans
    
    le_total := dictOrder.leTotal
    
    decidableLE := inferInstance
  
end Pair
