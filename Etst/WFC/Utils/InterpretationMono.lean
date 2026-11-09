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


namespace Expr
  variable
    {kind: ExprKind}
    {lane: kind.Lane}
    {l0 l1 r0 r1 e0 e1: Expr kind}
  
  theorem intp_toggle_toggle_eq
    (expr: Expr kind)
    (lane: kind.Lane)
    (b c: Valuation Pair)
    (fv: List Pair)
  :
    expr.intp lane.toggle.toggle b c fv = expr.intp lane b c fv
  :=
    lane.toggle_toggle ▸ rfl
  
  theorem intp_mono_std_prod
    (leL: l0.intp lane b0 c0 fv0 ≤ l1.intp lane b1 c1 fv1)
    (leR: r0.intp lane b0 c0 fv0 ≤ r1.intp lane b1 c1 fv1)
  :
    Set.Subset
      ((prod l0 r0).intp lane b0 c0 fv0)
      ((prod l1 r1).intp lane b1 c1 fv1)
  :=
    fun
    | .pair _ _, isDef =>
      let ⟨insL, insR⟩ := inProdElim isDef
      inProd (leL insL) (leR insR)
  
  theorem eq_intp_prod_of_eq
    (eqL: l0.intp lane b0 c0 fv0 = l1.intp lane b1 c1 fv1)
    (eqR: r0.intp lane b0 c0 fv0 = r1.intp lane b1 c1 fv1)
  :
    Eq
      ((prod l0 r0).intp lane b0 c0 fv0)
      ((prod l1 r1).intp lane b1 c1 fv1)
  :=
    le_antisymm
      (intp_mono_std_prod (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_prod (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  theorem intp_mono_std_un
    (leL: l0.intp lane b0 c0 fv0 ≤ l1.intp lane b1 c1 fv1)
    (leR: r0.intp lane b0 c0 fv0 ≤ r1.intp lane b1 c1 fv1)
  :
    (un l0 r0).intp lane b0 c0 fv0 ⊆ (un l1 r1).intp lane b1 c1 fv1
  :=
    fun _ ins =>
      (inUnElim ins).elim
        (fun insL => inUnL (leL insL))
        (fun insR => inUnR (leR insR))
  
  theorem eq_intp_un_of_eq
    (eqL: l0.intp lane b0 c0 fv0 = l1.intp lane b1 c1 fv1)
    (eqR: r0.intp lane b0 c0 fv0 = r1.intp lane b1 c1 fv1)
  :
    (un l0 r0).intp lane b0 c0 fv0 = (un l1 r1).intp lane b1 c1 fv1
  :=
    le_antisymm
      (intp_mono_std_un (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_un (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  theorem intp_mono_std_ir
    (leL: l0.intp lane b0 c0 fv0 ≤ l1.intp lane b1 c1 fv1)
    (leR: r0.intp lane b0 c0 fv0 ≤ r1.intp lane b1 c1 fv1)
  :
    (ir l0 r0).intp lane b0 c0 fv0 ⊆ (ir l1 r1).intp lane b1 c1 fv1
  :=
    fun _ ins =>
      let ⟨insL, insR⟩ := inIrElim ins
      inIr (leL insL) (leR insR)
  
  theorem eq_intp_ir_of_eq
    (eqL: l0.intp lane b0 c0 fv0 = l1.intp lane b1 c1 fv1)
    (eqR: r0.intp lane b0 c0 fv0 = r1.intp lane b1 c1 fv1)
  :
    (ir l0 r0).intp lane b0 c0 fv0 = (ir l1 r1).intp lane b1 c1 fv1
  :=
    le_antisymm
      (intp_mono_std_ir (le_of_eq eqL) (le_of_eq eqR))
      (intp_mono_std_ir (le_of_eq eqL.symm) (le_of_eq eqR.symm))
  
  
  theorem intp_mono_std_some
    (le: e0.intp lane b0 c0 fv0 ≤ e1.intp lane b1 c1 fv1)
  :
    (some e0).intp lane b0 c0 fv0 ⊆ (some e1).intp lane b1 c1 fv1
  :=
    fun _ ins =>
      let ⟨_, insE⟩ := inSomeElim ins (p := .null)
      inSome .null (le insE)
  
  theorem eq_intp_some_of_eq
    (eq: e0.intp lane b0 c0 fv0 = e1.intp lane b1 c1 fv1)
  :
    (some e0).intp lane b0 c0 fv0 = (some e1).intp lane b1 c1 fv1
  :=
    le_antisymm
      (intp_mono_std_some (le_of_eq eq))
      (intp_mono_std_some (le_of_eq eq.symm))
  
  
  theorem intp_mono_std_full
    (le: e0.intp lane b0 c0 fv0 ≤ e1.intp lane b1 c1 fv1)
  :
    (full e0).intp lane b0 c0 fv0 ⊆ (full e1).intp lane b1 c1 fv1
  :=
    fun _ ins =>
      let insE := inFullElim ins
      inFull .null (fun p => le (insE p))
  
  theorem eq_intp_full_of_eq
    (eq: e0.intp lane b0 c0 fv0 = e1.intp lane b1 c1 fv1)
  :
    (full e0).intp lane b0 c0 fv0 = (full e1).intp lane b1 c1 fv1
  :=
    le_antisymm
      (intp_mono_std_full (le_of_eq eq))
      (intp_mono_std_full (le_of_eq eq.symm))
  
  
  theorem intp_antimono_std_compl
    (le:
      Set.Subset
        (e1.intp lane.toggle c1 b1 fv1)
        (e0.intp lane.toggle c0 b0 fv0))
  :
    Set.Subset
      ((compl e0).intp lane b0 c0 fv0)
      ((compl e1).intp lane b1 c1 fv1)
  :=
    fun _ ins =>
      inCompl fun isPos => inComplElim ins (le isPos)
  
  theorem intp_antimono_std_compl_toggle
    (le:
      Set.Subset
        (e1.intp lane c1 b1 fv1)
        (e0.intp lane c0 b0 fv0))
  :
    Set.Subset
      ((compl e0).intp lane.toggle b0 c0 fv0)
      ((compl e1).intp lane.toggle b1 c1 fv1)
  :=
    fun _ ins =>
    inComplToggle
    fun isPos =>
    inComplToggleElim ins (le isPos)
  
  theorem intp_antimono_std_compl_elim
    (le:
      Set.Subset
        ((compl e0).intp lane b0 c0 fv0)
        ((compl e1).intp lane b1 c1 fv1))
  :
    Set.Subset
      (e1.intp lane.toggle c1 b1 fv1)
      (e0.intp lane.toggle c0 b0 fv0)
  :=
    fun _ ins =>
    byContradiction
    fun nin => inComplElim (le (inCompl nin)) ins
  
  theorem intp_antimono_std_compl_toggle_elim
    (le:
      Set.Subset
        ((compl e0).intp lane.toggle b0 c0 fv0)
        ((compl e1).intp lane.toggle b1 c1 fv1))
  :
    Set.Subset
      (e1.intp lane c1 b1 fv1)
      (e0.intp lane c0 b0 fv0)
  :=
    fun _ ins =>
    byContradiction
    fun nin =>
    inComplToggleElim (le (inComplToggle nin)) ins
  
  theorem eq_intp_compl_of_eq
    (eq:
      Eq
        (e0.intp lane.toggle c0 b0 fv0)
        (e1.intp lane.toggle c1 b1 fv1))
  :
    Eq
      ((compl e0).intp lane b0 c0 fv0)
      ((compl e1).intp lane b1 c1 fv1)
  :=
    le_antisymm
      (intp_antimono_std_compl (le_of_eq eq.symm))
      (intp_antimono_std_compl (le_of_eq eq))
  
  theorem eq_intp_compl_toggle_of_eq
    (eq:
      Eq
        (e0.intp lane c0 b0 fv0)
        (e1.intp lane c1 b1 fv1))
  :
    Eq
      ((compl e0).intp lane.toggle b0 c0 fv0)
      ((compl e1).intp lane.toggle b1 c1 fv1)
  :=
    le_antisymm
      (intp_antimono_std_compl_toggle (le_of_eq eq.symm))
      (intp_antimono_std_compl_toggle (le_of_eq eq))
  
  theorem eq_intp_of_eq_compl
    (eq:
      Eq
        ((compl e0).intp lane b0 c0 fv0)
        ((compl e1).intp lane b1 c1 fv1))
  :
    Eq
      (e0.intp lane.toggle c0 b0 fv0)
      (e1.intp lane.toggle c1 b1 fv1)
  :=
    le_antisymm
      (intp_antimono_std_compl_elim (le_of_eq eq.symm))
      (intp_antimono_std_compl_elim (le_of_eq eq))
  
  theorem eq_intp_of_eq_compl_toggle
    (eq:
      Eq
        ((compl e0).intp lane.toggle b0 c0 fv0)
        ((compl e1).intp lane.toggle b1 c1 fv1))
  :
    Eq
      (e0.intp lane c0 b0 fv0)
      (e1.intp lane c1 b1 fv1)
  :=
    le_antisymm
      (intp_antimono_std_compl_toggle_elim (le_of_eq eq.symm))
      (intp_antimono_std_compl_toggle_elim (le_of_eq eq))
  
  theorem intp_compl_compl_eq
    (expr: Expr kind)
    (lane: kind.Lane)
    (b c: Valuation Pair)
    (fv: List Pair)
  :
    (compl (compl expr)).intp lane b c fv = expr.intp lane b c fv
  :=
    Set.ext fun _ =>
      Iff.intro
        (fun ins => lane.toggle_toggle ▸ ins.dne)
        (fun ins => not_not_intro (lane.toggle_toggle ▸ ins))
  
  
  theorem intp_mono_std_arbIr
    {fv0 fv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (le:
      ∀ pB,
      Set.Subset
        (e0.intp lane b0 c0 (pB :: fv0))
        (e1.intp lane b1 c1 (pB :: fv1)))
  :
    Set.Subset
      ((arbIr e0).intp lane b0 c0 fv0)
      ((arbIr e1).intp lane b1 c1 fv1)
  :=
    fun _ h pB => (le pB) (h pB)
  
  theorem eq_intp_arbIr_of_eq
    {fv0 fv1: List Pair}
    {b0 c0 b1 c1: Valuation Pair}
    (eq:
      ∀ pB,
      Eq
        (e0.intp lane b0 c0 (pB :: fv0))
        (e1.intp lane b1 c1 (pB :: fv1)))
  :
    Eq
      ((arbIr e0).intp lane b0 c0 fv0)
      ((arbIr e1).intp lane b1 c1 fv1)
  :=
    le_antisymm
      (intp_mono_std_arbIr (fun pB => le_of_eq (eq pB)))
      (intp_mono_std_arbIr (fun pB => le_of_eq (eq pB).symm))
  
  
  variable {l0 l1 r0 r1 e0 e1: Expr .basic}
  
  theorem triIntp_mono_std_prod
    (leL: l0.triIntp b0 c0 fv0 ≤ l1.triIntp b1 c1 fv1)
    (leR: r0.triIntp b0 c0 fv0 ≤ r1.triIntp b1 c1 fv1)
  :
    (prod l0 r0).triIntp b0 c0 fv0 ≤ (prod l1 r1).triIntp b1 c1 fv1
  := {
    defLe := intp_mono_std_prod leL.defLe leR.defLe
    posLe := intp_mono_std_prod leL.posLe leR.posLe
  }
  
  theorem eq_triIntp_prod_of_eq
    (eqL: l0.triIntp b0 c0 fv0 = l1.triIntp b1 c1 fv1)
    (eqR: r0.triIntp b0 c0 fv0 = r1.triIntp b1 c1 fv1)
  :
    (prod l0 r0).triIntp b0 c0 fv0 = (prod l1 r1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_prod_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp_prod_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  theorem triIntp_mono_std_un
    (leL: l0.triIntp b0 c0 fv0 ≤ l1.triIntp b1 c1 fv1)
    (leR: r0.triIntp b0 c0 fv0 ≤ r1.triIntp b1 c1 fv1)
  :
    (un l0 r0).triIntp b0 c0 fv0 ≤ (un l1 r1).triIntp b1 c1 fv1
  := {
    defLe := intp_mono_std_un leL.defLe leR.defLe
    posLe := intp_mono_std_un leL.posLe leR.posLe
  }
  
  theorem eq_triIntp_un_of_eq
    (eqL: l0.triIntp b0 c0 fv0 = l1.triIntp b1 c1 fv1)
    (eqR: r0.triIntp b0 c0 fv0 = r1.triIntp b1 c1 fv1)
  :
    (un l0 r0).triIntp b0 c0 fv0 = (un l1 r1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_un_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp_un_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  theorem triIntp_mono_std_ir
    (leL: l0.triIntp b0 c0 fv0 ≤ l1.triIntp b1 c1 fv1)
    (leR: r0.triIntp b0 c0 fv0 ≤ r1.triIntp b1 c1 fv1)
  :
    (ir l0 r0).triIntp b0 c0 fv0 ≤ (ir l1 r1).triIntp b1 c1 fv1
  := {
    defLe := intp_mono_std_ir leL.defLe leR.defLe
    posLe := intp_mono_std_ir leL.posLe leR.posLe
  }
  
  theorem eq_triIntp_ir_of_eq
    (eqL: l0.triIntp b0 c0 fv0 = l1.triIntp b1 c1 fv1)
    (eqR: r0.triIntp b0 c0 fv0 = r1.triIntp b1 c1 fv1)
  :
    (ir l0 r0).triIntp b0 c0 fv0 = (ir l1 r1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_ir_of_eq (Set3.def_eq eqL) (Set3.def_eq eqR))
      (eq_intp_ir_of_eq (Set3.pos_eq eqL) (Set3.pos_eq eqR))
  
  
  theorem triIntp_mono_std_some
    (le: e0.triIntp b0 c0 fv0 ≤ e1.triIntp b1 c1 fv1)
  :
    (some e0).triIntp b0 c0 fv0 ≤ (some e1).triIntp b1 c1 fv1
  := {
    defLe := intp_mono_std_some le.defLe
    posLe := intp_mono_std_some le.posLe
  }
  
  theorem eq_triIntp_some_of_eq
    (eq: e0.triIntp b0 c0 fv0 = e1.triIntp b1 c1 fv1)
  :
    (some e0).triIntp b0 c0 fv0 = (some e1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_some_of_eq (Set3.def_eq eq))
      (eq_intp_some_of_eq (Set3.pos_eq eq))
  
  
  theorem triIntp_mono_std_full
    (le: e0.triIntp b0 c0 fv0 ≤ e1.triIntp b1 c1 fv1)
  :
    (full e0).triIntp b0 c0 fv0 ≤ (full e1).triIntp b1 c1 fv1
  := {
    defLe := intp_mono_std_full le.defLe
    posLe := intp_mono_std_full le.posLe
  }
  
  theorem eq_triIntp_full_of_eq
    (eq: e0.triIntp b0 c0 fv0 = e1.triIntp b1 c1 fv1)
  :
    (full e0).triIntp b0 c0 fv0 = (full e1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_full_of_eq (Set3.def_eq eq))
      (eq_intp_full_of_eq (Set3.pos_eq eq))
  
  
  theorem triIntp_antimono_std_compl
    (le: e1.triIntp c1 b1 fv1 ≤ e0.triIntp c0 b0 fv0)
  :
    (compl e0).triIntp b0 c0 fv0 ≤ (compl e1).triIntp b1 c1 fv1
  := {
    defLe := intp_antimono_std_compl le.posLe
    posLe := intp_antimono_std_compl le.defLe
  }

  theorem eq_triIntp_compl_of_eq
    (eq: e0.triIntp c0 b0 fv0 = e1.triIntp c1 b1 fv1)
  :
    (compl e0).triIntp b0 c0 fv0 = (compl e1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_compl_of_eq (Set3.pos_eq eq))
      (eq_intp_compl_of_eq (Set3.def_eq eq))
  
  
  theorem triIntp_mono_std_arbIr
    (le:
      ∀ pB,
      e0.triIntp b0 c0 (pB :: fv0) ≤ e1.triIntp b1 c1 (pB :: fv1))
  :
    (arbIr e0).triIntp b0 c0 fv0 ≤ (arbIr e1).triIntp b1 c1 fv1
  := {
    defLe := intp_mono_std_arbIr fun pB => (le pB).defLe
    posLe := intp_mono_std_arbIr fun pB => (le pB).posLe
  }
  
  theorem eq_triIntp_arbIr_of_eq
    (eq:
      ∀ pB,
      e0.triIntp b0 c0 (pB :: fv0) = e1.triIntp b1 c1 (pB :: fv1))
  :
    (arbIr e0).triIntp b0 c0 fv0 = (arbIr e1).triIntp b1 c1 fv1
  :=
    Set3.eq
      (eq_intp_arbIr_of_eq fun pB => Set3.def_eq (eq pB))
      (eq_intp_arbIr_of_eq fun pB => Set3.pos_eq (eq pB))
  
end Expr
