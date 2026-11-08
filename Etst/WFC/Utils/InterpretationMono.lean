/-
  In this file, we prove monotonicity of the interpretation of Expr
  constructors. Unlike the file `Interpretation.lean`, where the
  assumptions are that the valuations are ordered, here we assume
  that the interpretations of the sub-expressions are ordered.
-/
module
public import Etst.WFC.Utils.PairExpr
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst

variable {b0 b1 c0 c1: Valuation Pair}
variable {fv0 fv1: List Pair}


namespace SingleLaneExpr
  open Expr
  variable {l0 l1 r0 r1 e0 e1: SingleLaneExpr}
  
  theorem intp_mono_std_prod
    {l0 l1 r0 r1: SingleLaneExpr}
    (leL: intp l0 fv0 b0 c0 ≤ intp l1 fv1 b1 c1)
    (leR: intp r0 fv0 b0 c0 ≤ intp r1 fv1 b1 c1)
  :
    intp (prod l0 r0) fv0 b0 c0 ⊆ intp (prod l1 r1) fv1 b1 c1
  :=
    fun
    | .pair _ _, isDef =>
      let ⟨insL, insR⟩ := inProdElim isDef
      inProd (leL insL) (leR insR)
  
  theorem eq_intp_prod_of_eq
    (eqL: intp l0 fv0 b0 c0 = intp l1 fv1 b1 c1)
    (eqR: intp r0 fv0 b0 c0 = intp r1 fv1 b1 c1)
  :
    intp (prod l0 r0) fv0 b0 c0 = intp (prod l1 r1) fv1 b1 c1
  :=
    le_antisymm
      (intp_mono_std_prod (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_prod (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  theorem intp_mono_std_un
    (leL: intp l0 fv0 b0 c0 ≤ intp l1 fv1 b1 c1)
    (leR: intp r0 fv0 b0 c0 ≤ intp r1 fv1 b1 c1)
  :
    intp (un l0 r0) fv0 b0 c0 ⊆ intp (un l1 r1) fv1 b1 c1
  :=
    fun _ ins =>
      (inUnElim ins).elim
        (fun insL => inUnL (leL insL))
        (fun insR => inUnR (leR insR))
  
  theorem eq_intp_un_of_eq
    (eqL: intp l0 fv0 b0 c0 = intp l1 fv1 b1 c1)
    (eqR: intp r0 fv0 b0 c0 = intp r1 fv1 b1 c1)
  :
    intp (un l0 r0) fv0 b0 c0 = intp (un l1 r1) fv1 b1 c1
  :=
    le_antisymm
      (intp_mono_std_un (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_un (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  theorem intp_mono_std_ir
    (leL: intp l0 fv0 b0 c0 ≤ intp l1 fv1 b1 c1)
    (leR: intp r0 fv0 b0 c0 ≤ intp r1 fv1 b1 c1)
  :
    intp (ir l0 r0) fv0 b0 c0 ⊆ intp (ir l1 r1) fv1 b1 c1
  :=
    fun _ ins =>
      let ⟨insL, insR⟩ := inIrElim ins
      inIr (leL insL) (leR insR)
  
  theorem eq_intp_ir_of_eq
    (eqL: intp l0 fv0 b0 c0 = intp l1 fv1 b1 c1)
    (eqR: intp r0 fv0 b0 c0 = intp r1 fv1 b1 c1)
  :
    intp (ir l0 r0) fv0 b0 c0 = intp (ir l1 r1) fv1 b1 c1
  :=
    le_antisymm
      (intp_mono_std_ir (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_ir (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  theorem intp_mono_std_some
    (le: intp e0 fv0 b0 c0 ≤ intp e1 fv1 b1 c1)
  :
    intp (some e0) fv0 b0 c0 ⊆ intp (some e1) fv1 b1 c1
  :=
    fun _ ins =>
      let ⟨_, insE⟩ := inSomeElim ins (p := .null)
      inSome .null (le insE)
  
  theorem eq_intp_some_of_eq
    (eq: intp e0 fv0 b0 c0 = intp e1 fv1 b1 c1)
  :
    intp (some e0) fv0 b0 c0 = intp (some e1) fv1 b1 c1
  :=
    le_antisymm
      (intp_mono_std_some (le_of_eq eq))
      (intp_mono_std_some (le_of_eq eq.symm))
  
  
  theorem intp_mono_std_full
    (le: intp e0 fv0 b0 c0 ≤ intp e1 fv1 b1 c1)
  :
    intp (full e0) fv0 b0 c0 ⊆ intp (full e1) fv1 b1 c1
  :=
    fun _ ins =>
      let insE := inFullElim ins
      inFull .null (fun p => le (insE p))
  
  theorem eq_intp_full_of_eq
    (eq: intp e0 fv0 b0 c0 = intp e1 fv1 b1 c1)
  :
    intp (full e0) fv0 b0 c0 = intp (full e1) fv1 b1 c1
  :=
    le_antisymm
      (intp_mono_std_full (le_of_eq eq))
      (intp_mono_std_full (le_of_eq eq.symm))
  
  
  theorem intp_mono_std_compl
    (le:
      Set.Subset
        (e1.intp fv1 c1 b1)
        (e0.intp fv0 c0 b0))
  :
    Set.Subset
      ((compl e0).intp fv0 b0 c0)
      ((compl e1).intp fv1 b1 c1)
  :=
    fun _ ins =>
      inCompl (fun isPos => inComplElim ins (le isPos))
  
  theorem intp_mono_std_compl_elim
    (le:
      Set.Subset
        ((compl e0).intp fv0 b0 c0)
        ((compl e1).intp fv1 b1 c1))
  :
    Set.Subset
      (e1.intp fv1 c1 b1)
      (e0.intp fv0 c0 b0)
  :=
    fun _ ins =>
      byContradiction
        (fun nin => inComplElim (le (inCompl nin)) ins)
  
  theorem eq_intp_compl_of_eq
    (eq:
      Eq
        (e0.intp fv0 c0 b0)
        (e1.intp fv1 c1 b1))
  :
    Eq
      ((compl e0).intp fv0 b0 c0)
      ((compl e1).intp fv1 b1 c1)
  :=
    le_antisymm
      (intp_mono_std_compl (le_of_eq eq.symm))
      (intp_mono_std_compl (le_of_eq eq))
  
  theorem eq_intp_of_eq_compl
    (eq:
      Eq
        ((compl e0).intp fv0 b0 c0)
        ((compl e1).intp fv1 b1 c1))
  :
    Eq
      (e0.intp fv0 c0 b0)
      (e1.intp fv1 c1 b1)
  :=
    le_antisymm
      (intp_mono_std_compl_elim (le_of_eq eq.symm))
      (intp_mono_std_compl_elim (le_of_eq eq))
  
  theorem intp_compl_compl_eq
    (expr: SingleLaneExpr)
    (fv: List Pair)
    (b c: Valuation Pair)
  :
    intp (.compl (.compl expr)) b c fv = intp expr b c fv
  :=
    Set.ext fun _ => ⟨Not.dne, not_not_intro⟩
  
  
  theorem intp_mono_std_arbIr
    {fv0 fv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (le:
      ∀ pB,
      Set.Subset
        (e0.intp (pB :: fv0) b0 c0)
        (e1.intp (pB :: fv1) b1 c1))
  :
    Set.Subset
      ((arbIr e0).intp fv0 b0 c0)
      ((arbIr e1).intp fv1 b1 c1)
  :=
    fun _ h pB => (le pB) (h pB)
  
  theorem eq_intp_arbIr_of_eq
    {fv0 fv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (eq:
      ∀ pB,
      Eq
        (e0.intp (pB :: fv0) b0 c0)
        (e1.intp (pB :: fv1) b1 c1))
  :
    Eq
      ((arbIr e0).intp fv0 b0 c0)
      ((arbIr e1).intp fv1 b1 c1)
  :=
    le_antisymm
      (intp_mono_std_arbIr (fun pB => le_of_eq (eq pB)))
      (intp_mono_std_arbIr (fun pB => le_of_eq (eq pB).symm))
  
end SingleLaneExpr

namespace BasicExpr
  open SingleLaneExpr
  variable {l0 l1 r0 r1 e0 e1: BasicExpr}
  
  theorem triIntp_mono_std_prod
    (leL: triIntp l0 fv0 b0 c0 ≤ triIntp l1 fv1 b1 c1)
    (leR: triIntp r0 fv0 b0 c0 ≤ triIntp r1 fv1 b1 c1)
  :
    triIntp (prod l0 r0) fv0 b0 c0 ≤ triIntp (prod l1 r1) fv1 b1 c1
  := {
    defLe := intp_mono_std_prod leL.defLe leR.defLe
    posLe := intp_mono_std_prod leL.posLe leR.posLe
  }
  
  theorem eq_triIntp_prod_of_eq
    (eqL: triIntp l0 fv0 b0 c0 = triIntp l1 fv1 b1 c1)
    (eqR: triIntp r0 fv0 b0 c0 = triIntp r1 fv1 b1 c1)
  :
    triIntp (prod l0 r0) fv0 b0 c0 = triIntp (prod l1 r1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_prod_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp_prod_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  theorem triIntp_mono_std_un
    (leL: triIntp l0 fv0 b0 c0 ≤ triIntp l1 fv1 b1 c1)
    (leR: triIntp r0 fv0 b0 c0 ≤ triIntp r1 fv1 b1 c1)
  :
    triIntp (un l0 r0) fv0 b0 c0 ≤ triIntp (un l1 r1) fv1 b1 c1
  := {
    defLe := intp_mono_std_un leL.defLe leR.defLe
    posLe := intp_mono_std_un leL.posLe leR.posLe
  }
  
  theorem eq_triIntp_un_of_eq
    (eqL: triIntp l0 fv0 b0 c0 = triIntp l1 fv1 b1 c1)
    (eqR: triIntp r0 fv0 b0 c0 = triIntp r1 fv1 b1 c1)
  :
    triIntp (un l0 r0) fv0 b0 c0 = triIntp (un l1 r1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_un_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp_un_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  theorem triIntp_mono_std_ir
    (leL: triIntp l0 fv0 b0 c0 ≤ triIntp l1 fv1 b1 c1)
    (leR: triIntp r0 fv0 b0 c0 ≤ triIntp r1 fv1 b1 c1)
  :
    triIntp (ir l0 r0) fv0 b0 c0 ≤ triIntp (ir l1 r1) fv1 b1 c1
  := {
    defLe := intp_mono_std_ir leL.defLe leR.defLe
    posLe := intp_mono_std_ir leL.posLe leR.posLe
  }
  
  theorem eq_triIntp_ir_of_eq
    (eqL: triIntp l0 fv0 b0 c0 = triIntp l1 fv1 b1 c1)
    (eqR: triIntp r0 fv0 b0 c0 = triIntp r1 fv1 b1 c1)
  :
    triIntp (ir l0 r0) fv0 b0 c0 = triIntp (ir l1 r1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_ir_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp_ir_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  theorem triIntp_mono_std_some
    (le: triIntp e0 fv0 b0 c0 ≤ triIntp e1 fv1 b1 c1)
  :
    triIntp (some e0) fv0 b0 c0 ≤ triIntp (some e1) fv1 b1 c1
  := {
    defLe := intp_mono_std_some le.defLe
    posLe := intp_mono_std_some le.posLe
  }
  
  theorem eq_triIntp_some_of_eq
    (eq: triIntp e0 fv0 b0 c0 = triIntp e1 fv1 b1 c1)
  :
    triIntp (some e0) fv0 b0 c0 = triIntp (some e1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_some_of_eq (Set3.def_eq eq))
      (eq_intp_some_of_eq (Set3.pos_eq eq))
  
  
  theorem triIntp_mono_std_full
    (le: triIntp e0 fv0 b0 c0 ≤ triIntp e1 fv1 b1 c1)
  :
    triIntp (full e0) fv0 b0 c0 ≤ triIntp (full e1) fv1 b1 c1
  := {
    defLe := intp_mono_std_full le.defLe
    posLe := intp_mono_std_full le.posLe
  }
  
  theorem eq_triIntp_full_of_eq
    (eq: triIntp e0 fv0 b0 c0 = triIntp e1 fv1 b1 c1)
  :
    triIntp (full e0) fv0 b0 c0 = triIntp (full e1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_full_of_eq (Set3.def_eq eq))
      (eq_intp_full_of_eq (Set3.pos_eq eq))
  
  
  theorem triIntp_mono_std_compl
    (le: triIntp e1 fv1 c1 b1 ≤ triIntp e0 fv0 c0 b0)
  :
    triIntp (compl e0) fv0 b0 c0 ≤ triIntp (compl e1) fv1 b1 c1
  := {
    defLe := intp_mono_std_compl le.posLe
    posLe := intp_mono_std_compl le.defLe
  }

  theorem eq_triIntp_compl_of_eq
    (eq: triIntp e0 fv0 c0 b0 = triIntp e1 fv1 c1 b1)
  :
    triIntp (compl e0) fv0 b0 c0 = triIntp (compl e1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_compl_of_eq (Set3.pos_eq eq))
      (eq_intp_compl_of_eq (Set3.def_eq eq))
  
  
  theorem triIntp_mono_std_arbIr
    (le:
      ∀ pB,
      triIntp e0 (pB :: fv0) b0 c0 ≤ triIntp e1 (pB :: fv1) b1 c1)
  :
    triIntp (arbIr e0) fv0 b0 c0 ≤ triIntp (arbIr e1) fv1 b1 c1
  := {
    defLe := intp_mono_std_arbIr (fun (pB: Pair) => (le pB).defLe)
    posLe := intp_mono_std_arbIr (fun (pB: Pair) => (le pB).posLe)
  }
  
  theorem eq_triIntp_arbIr_of_eq
    (eq:
      ∀ pB,
      triIntp e0 (pB :: fv0) b0 c0 = triIntp e1 (pB :: fv1) b1 c1)
  :
    triIntp (arbIr e0) fv0 b0 c0 = triIntp (arbIr e1) fv1 b1 c1
  :=
    Set3.eq
      (eq_intp_arbIr_of_eq (fun (pB: Pair) => Set3.def_eq (eq pB)))
      (eq_intp_arbIr_of_eq (fun (pB: Pair) => Set3.pos_eq (eq pB)))
  
end BasicExpr
