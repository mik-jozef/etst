/-
  The dictionary order on pairs, the base case
  being `zero < pair a b`.
-/

import Pair

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
  
  def dictOrder.Lt.irefl
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
  
  def dictOrder.leRefl a: Le a a := Or.inl rfl
  
  def dictOrder.Lt.antisymm
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
  
  def dictOrder.Le.antisymm
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
          (fun baLt => abLt.antisymm baLt))
  
  def dictOrder.Lt.trans
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
  
  def dictOrder.Le.trans
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
          (fun bcLt => Or.inr (abLt.trans bcLt)))
  
  def dictOrder.ltTotal
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
  
  def dictOrder.leTotal
    (a b: Pair)
  :
    Le a b ∨ Le b a
  :=
    open IsComparable in
    match ltTotal a b with
    | IsLt ab => Or.inl (Or.inr ab)
    | IsGt ba => Or.inr (Or.inr ba)
    | IsEq eq => eq ▸ Or.inl (leRefl _)
  
end Pair
