/-
  In this file, we prove monotonicity of the intp2 of Expr
  constructors. Unlike the file `intp2.lean`, where the assumptions
  are that the valuations are ordered, here we assume that the
  interpretations of the sub-expressions are ordered.
-/
import Etst.WFC.Utils.PairExpr

namespace Etst


namespace SingleLaneExpr
  def inter_mono_std_compl
    (le:
      Set.Subset
        (e1.intp2 bv1 c1 b1)
        (e0.intp2 bv0 c0 b0))
  :
    Set.Subset
      ((compl e0).intp2 bv0 b0 c0)
      ((compl e1).intp2 bv1 b1 c1)
  :=
    fun _ ins =>
      inCompl (fun isPos => inComplElim ins (le isPos))
  
  def eq_compl_of_eq
    (eq:
      Eq
        (e0.intp2 bv0 c0 b0)
        (e1.intp2 bv1 c1 b1))
  :
    Eq
      ((compl e0).intp2 bv0 b0 c0)
      ((compl e1).intp2 bv1 b1 c1)
  :=
    le_antisymm
      (inter_mono_std_compl (le_of_eq eq.symm))
      (inter_mono_std_compl (le_of_eq eq))
  
  
  def inter_mono_std_arbUn
    {bv0 bv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (le:
      ∀ dB,
      Set.Subset
        (e0.intp2 (dB :: bv0) b0 c0)
        (e1.intp2 (dB :: bv1) b1 c1))
  :
    Set.Subset
      ((arbUn e0).intp2 bv0 b0 c0)
      ((arbUn e1).intp2 bv1 b1 c1)
  :=
    fun _ in0 =>
      let ⟨dB, isDef⟩ := inArbUnElim in0
      inArbUn dB ((le dB) isDef)
  
  def eq_arbUn_of_eq
    {bv0 bv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (eq:
      ∀ dB,
      Eq
        (e0.intp2 (dB :: bv0) b0 c0)
        (e1.intp2 (dB :: bv1) b1 c1))
  :
    Eq
      ((arbUn e0).intp2 bv0 b0 c0)
      ((arbUn e1).intp2 bv1 b1 c1)
  :=
    le_antisymm
      (inter_mono_std_arbUn (fun dB => le_of_eq (eq dB)))
      (inter_mono_std_arbUn (fun dB => le_of_eq (eq dB).symm))
  
  
  def inter_mono_std_arbIr
    {bv0 bv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (le:
      ∀ dB,
      Set.Subset
        (e0.intp2 (dB :: bv0) b0 c0)
        (e1.intp2 (dB :: bv1) b1 c1))
  :
    Set.Subset
      ((arbIr e0).intp2 bv0 b0 c0)
      ((arbIr e1).intp2 bv1 b1 c1)
  :=
    fun _ h dB => (le dB) (h dB)
  
  def eq_arbIr_of_eq
    {bv0 bv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (eq:
      ∀ dB,
      Eq
        (e0.intp2 (dB :: bv0) b0 c0)
        (e1.intp2 (dB :: bv1) b1 c1))
  :
    Eq
      ((arbIr e0).intp2 bv0 b0 c0)
      ((arbIr e1).intp2 bv1 b1 c1)
  :=
    le_antisymm
      (inter_mono_std_arbIr (fun dB => le_of_eq (eq dB)))
      (inter_mono_std_arbIr (fun dB => le_of_eq (eq dB).symm))
  
end SingleLaneExpr

namespace BasicExpr
  open SingleLaneExpr
  
  def triIntp2_mono_std_compl
    (le: triIntp2 e1 bv1 c1 b1 ≤ triIntp2 e0 bv0 c0 b0)
  :
    triIntp2 (compl e0) bv0 b0 c0 ≤ triIntp2 (compl e1) bv1 b1 c1
  := {
    defLe := inter_mono_std_compl le.posLe
    posLe := inter_mono_std_compl le.defLe
  }

  def eq_triIntp2_compl_of_eq
    (eq: triIntp2 e0 bv0 c0 b0 = triIntp2 e1 bv1 c1 b1)
  :
    triIntp2 (compl e0) bv0 b0 c0 = triIntp2 (compl e1) bv1 b1 c1
  :=
    Set3.eq
      (eq_compl_of_eq (Set3.pos_eq eq))
      (eq_compl_of_eq (Set3.def_eq eq))
  
  
  def triIntp2_mono_std_arbUn
    (le:
      ∀ dB,
      triIntp2 e0 (dB :: bv0) b0 c0 ≤ triIntp2 e1 (dB :: bv1) b1 c1)
  :
    triIntp2 (arbUn e0) bv0 b0 c0 ≤ triIntp2 (arbUn e1) bv1 b1 c1
  := {
    defLe := inter_mono_std_arbUn (fun (dB: Pair) => (le dB).defLe)
    posLe := inter_mono_std_arbUn (fun (dB: Pair) => (le dB).posLe)
  }
  
  def eq_triIntp2_arbUn_of_eq
    (eq:
      ∀ dB,
      triIntp2 e0 (dB :: bv0) b0 c0 = triIntp2 e1 (dB :: bv1) b1 c1)
  :
    triIntp2 (arbUn e0) bv0 b0 c0 = triIntp2 (arbUn e1) bv1 b1 c1
  :=
    Set3.eq
      (eq_arbUn_of_eq (fun (dB: Pair) => Set3.def_eq (eq dB)))
      (eq_arbUn_of_eq (fun (dB: Pair) => Set3.pos_eq (eq dB)))
  
  
  def triIntp2_mono_std_arbIr
    (le:
      ∀ dB,
      triIntp2 e0 (dB :: bv0) b0 c0 ≤ triIntp2 e1 (dB :: bv1) b1 c1)
  :
    triIntp2 (arbIr e0) bv0 b0 c0 ≤ triIntp2 (arbIr e1) bv1 b1 c1
  := {
    defLe := inter_mono_std_arbIr (fun (dB: Pair) => (le dB).defLe)
    posLe := inter_mono_std_arbIr (fun (dB: Pair) => (le dB).posLe)
  }
  
  def eq_triIntp2_arbIr_of_eq
    (eq:
      ∀ dB,
      triIntp2 e0 (dB :: bv0) b0 c0 = triIntp2 e1 (dB :: bv1) b1 c1)
  :
    triIntp2 (arbIr e0) bv0 b0 c0 = triIntp2 (arbIr e1) bv1 b1 c1
  :=
    Set3.eq
      (eq_arbIr_of_eq (fun (dB: Pair) => Set3.def_eq (eq dB)))
      (eq_arbIr_of_eq (fun (dB: Pair) => Set3.pos_eq (eq dB)))

end BasicExpr


namespace SingleLaneExpr
  open Expr
  
  def intp2_mono_std_pair
    {l0 l1 r0 r1: SingleLaneExpr}
    (leL: intp2 l0 bv0 b0 c0 ≤ intp2 l1 bv1 b1 c1)
    (leR: intp2 r0 bv0 b0 c0 ≤ intp2 r1 bv1 b1 c1)
  :
    intp2 (pair l0 r0) bv0 b0 c0 ⊆ intp2 (pair l1 r1) bv1 b1 c1
  :=
    fun
    | .pair _ _, isDef =>
      let ⟨insL, insR⟩ := inPairElim isDef
      inPair (leL insL) (leR insR)
  
  def eq_intp2_pair_of_eq
    (eqL: intp2 l0 bv0 b0 c0 = intp2 l1 bv1 b1 c1)
    (eqR: intp2 r0 bv0 b0 c0 = intp2 r1 bv1 b1 c1)
  :
    intp2 (pair l0 r0) bv0 b0 c0 = intp2 (pair l1 r1) bv1 b1 c1
  :=
    le_antisymm
      (intp2_mono_std_pair (le_of_eq eqL) (le_of_eq eqR))
      (intp2_mono_std_pair (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  def intp2_mono_std_un
    (leL: intp2 l0 bv0 b0 c0 ≤ intp2 l1 bv1 b1 c1)
    (leR: intp2 r0 bv0 b0 c0 ≤ intp2 r1 bv1 b1 c1)
  :
    intp2 (un l0 r0) bv0 b0 c0 ⊆ intp2 (un l1 r1) bv1 b1 c1
  :=
    fun _ ins =>
      (inUnElim ins).elim
        (fun insL => inUnL (leL insL))
        (fun insR => inUnR (leR insR))
  
  def eq_intp2_un_of_eq
    (eqL: intp2 l0 bv0 b0 c0 = intp2 l1 bv1 b1 c1)
    (eqR: intp2 r0 bv0 b0 c0 = intp2 r1 bv1 b1 c1)
  :
    intp2 (un l0 r0) bv0 b0 c0 = intp2 (un l1 r1) bv1 b1 c1
  :=
    le_antisymm
      (intp2_mono_std_un (le_of_eq eqL) (le_of_eq eqR))
      (intp2_mono_std_un (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  def intp2_mono_std_ir
    (leL: intp2 l0 bv0 b0 c0 ≤ intp2 l1 bv1 b1 c1)
    (leR: intp2 r0 bv0 b0 c0 ≤ intp2 r1 bv1 b1 c1)
  :
    intp2 (ir l0 r0) bv0 b0 c0 ⊆ intp2 (ir l1 r1) bv1 b1 c1
  :=
    fun _ ins =>
      let ⟨insL, insR⟩ := inIrElim ins
      inIr (leL insL) (leR insR)
  
  def eq_intp2_ir_of_eq
    (eqL: intp2 l0 bv0 b0 c0 = intp2 l1 bv1 b1 c1)
    (eqR: intp2 r0 bv0 b0 c0 = intp2 r1 bv1 b1 c1)
  :
    intp2 (ir l0 r0) bv0 b0 c0 = intp2 (ir l1 r1) bv1 b1 c1
  :=
    le_antisymm
      (intp2_mono_std_ir (le_of_eq eqL) (le_of_eq eqR))
      (intp2_mono_std_ir (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  def intp2_mono_std_condSome
    (le: intp2 e0 bv0 b0 c0 ≤ intp2 e1 bv1 b1 c1)
  :
    intp2 (condSome e0) bv0 b0 c0 ⊆ intp2 (condSome e1) bv1 b1 c1
  :=
    fun _ ins =>
      let ⟨_, insE⟩ := inCondSomeElim ins (d := .null)
      inCondSome .null (le insE)
  
  def eq_intp2_condSome_of_eq
    (eq: intp2 e0 bv0 b0 c0 = intp2 e1 bv1 b1 c1)
  :
    intp2 (condSome e0) bv0 b0 c0 = intp2 (condSome e1) bv1 b1 c1
  :=
    le_antisymm
      (intp2_mono_std_condSome (le_of_eq eq))
      (intp2_mono_std_condSome (le_of_eq eq.symm))
  
  
  def intp2_mono_std_condFull
    (le: intp2 e0 bv0 b0 c0 ≤ intp2 e1 bv1 b1 c1)
  :
    intp2 (condFull e0) bv0 b0 c0 ⊆ intp2 (condFull e1) bv1 b1 c1
  :=
    fun _ ins =>
      let insE := inCondFullElim ins
      inCondFull .null (fun d => le (insE d))
  
  def eq_intp2_condFull_of_eq
    (eq: intp2 e0 bv0 b0 c0 = intp2 e1 bv1 b1 c1)
  :
    intp2 (condFull e0) bv0 b0 c0 = intp2 (condFull e1) bv1 b1 c1
  :=
    le_antisymm
      (intp2_mono_std_condFull (le_of_eq eq))
      (intp2_mono_std_condFull (le_of_eq eq.symm))
  
end SingleLaneExpr

namespace BasicExpr
  open Expr
  open SingleLaneExpr
  
  def triIntp2_mono_std_pair
    (leL: triIntp2 l0 bv0 b0 c0 ≤ triIntp2 l1 bv1 b1 c1)
    (leR: triIntp2 r0 bv0 b0 c0 ≤ triIntp2 r1 bv1 b1 c1)
  :
    triIntp2 (pair l0 r0) bv0 b0 c0 ≤ triIntp2 (pair l1 r1) bv1 b1 c1
  := {
    defLe := intp2_mono_std_pair leL.defLe leR.defLe
    posLe := intp2_mono_std_pair leL.posLe leR.posLe
  }
  
  def eq_triIntp2_pair_of_eq
    (eqL: triIntp2 l0 bv0 b0 c0 = triIntp2 l1 bv1 b1 c1)
    (eqR: triIntp2 r0 bv0 b0 c0 = triIntp2 r1 bv1 b1 c1)
  :
    triIntp2 (pair l0 r0) bv0 b0 c0 = triIntp2 (pair l1 r1) bv1 b1 c1
  :=
    Set3.eq
      (eq_intp2_pair_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp2_pair_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  def triIntp2_mono_std_un
    (leL: triIntp2 l0 bv0 b0 c0 ≤ triIntp2 l1 bv1 b1 c1)
    (leR: triIntp2 r0 bv0 b0 c0 ≤ triIntp2 r1 bv1 b1 c1)
  :
    triIntp2 (un l0 r0) bv0 b0 c0 ≤ triIntp2 (un l1 r1) bv1 b1 c1
  := {
    defLe := intp2_mono_std_un leL.defLe leR.defLe
    posLe := intp2_mono_std_un leL.posLe leR.posLe
  }
  
  def eq_triIntp2_un_of_eq
    (eqL: triIntp2 l0 bv0 b0 c0 = triIntp2 l1 bv1 b1 c1)
    (eqR: triIntp2 r0 bv0 b0 c0 = triIntp2 r1 bv1 b1 c1)
  :
    triIntp2 (un l0 r0) bv0 b0 c0 = triIntp2 (un l1 r1) bv1 b1 c1
  :=
    Set3.eq
      (eq_intp2_un_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp2_un_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  def triIntp2_mono_std_ir
    (leL: triIntp2 l0 bv0 b0 c0 ≤ triIntp2 l1 bv1 b1 c1)
    (leR: triIntp2 r0 bv0 b0 c0 ≤ triIntp2 r1 bv1 b1 c1)
  :
    triIntp2 (ir l0 r0) bv0 b0 c0 ≤ triIntp2 (ir l1 r1) bv1 b1 c1
  := {
    defLe := intp2_mono_std_ir leL.defLe leR.defLe
    posLe := intp2_mono_std_ir leL.posLe leR.posLe
  }
  
  def eq_triIntp2_ir_of_eq
    (eqL: triIntp2 l0 bv0 b0 c0 = triIntp2 l1 bv1 b1 c1)
    (eqR: triIntp2 r0 bv0 b0 c0 = triIntp2 r1 bv1 b1 c1)
  :
    triIntp2 (ir l0 r0) bv0 b0 c0 = triIntp2 (ir l1 r1) bv1 b1 c1
  :=
    Set3.eq
      (eq_intp2_ir_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp2_ir_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  def triIntp2_mono_std_condSome
    (le: triIntp2 e0 bv0 b0 c0 ≤ triIntp2 e1 bv1 b1 c1)
  :
    triIntp2 (condSome e0) bv0 b0 c0 ≤ triIntp2 (condSome e1) bv1 b1 c1
  := {
    defLe := intp2_mono_std_condSome le.defLe
    posLe := intp2_mono_std_condSome le.posLe
  }
  
  def eq_triIntp2_condSome_of_eq
    (eq: triIntp2 e0 bv0 b0 c0 = triIntp2 e1 bv1 b1 c1)
  :
    triIntp2 (condSome e0) bv0 b0 c0 = triIntp2 (condSome e1) bv1 b1 c1
  :=
    Set3.eq
      (eq_intp2_condSome_of_eq (Set3.def_eq eq))
      (eq_intp2_condSome_of_eq (Set3.pos_eq eq))
  
  
  def triIntp2_mono_std_condFull
    (le: triIntp2 e0 bv0 b0 c0 ≤ triIntp2 e1 bv1 b1 c1)
  :
    triIntp2 (condFull e0) bv0 b0 c0 ≤ triIntp2 (condFull e1) bv1 b1 c1
  := {
    defLe := intp2_mono_std_condFull le.defLe
    posLe := intp2_mono_std_condFull le.posLe
  }
  
  def eq_triIntp2_condFull_of_eq
    (eq: triIntp2 e0 bv0 b0 c0 = triIntp2 e1 bv1 b1 c1)
  :
    triIntp2 (condFull e0) bv0 b0 c0 = triIntp2 (condFull e1) bv1 b1 c1
  :=
    Set3.eq
      (eq_intp2_condFull_of_eq (Set3.def_eq eq))
      (eq_intp2_condFull_of_eq (Set3.pos_eq eq))
  
end BasicExpr
