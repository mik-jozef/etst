/-
  # Chapter 6: Self-Definability (a Universal Indexing Triset)
  
  Recall from Chapter 3 the definition of a definable triset
  (`DefList.IsDefinable`). In this chapter, we show that there
  exists a definable triset `uniSetMap: Set3 Pair` that in a sense
  "contains" all definable trisets of pairs.
  
  More precisely, `uniSetMap` is such that for any definable triset
  `dt`, there exists an `index: Pair` such that for any `p: Pair`,
  
      p ∈ dt ↔ (index, p) ∈ uniSetMap \,,
  
  where the above equivalence holds for both the definitive and
  possible membership.
  
  We show that `uniSetMap` is itself definable by constructing a
  definition list that defines it. The traditional contradictions
  a la Russell are avoided thanks to the three-valued nature of
  trisets -- one cannot obtain a contradiction by diagonalization
  because the undetermined elements of a triset are undetermined
  in its complement as well.
  
  The triset `uniSetMap` (along with its characteristic property)
  is the only result of this chapter that we will use in the rest
  of the project. The construction itself, as well as the proof of
  its correctness are of secondary interest; the interested reader
  may look at the utility files in the folder
  `/Etst/WFC/Utils/SelfDefinability/` for the details.
-/
module
public import Etst.WFC.Utils.DefList
public import Etst.WFC.Utils.SelfDefinability.UniSetMapDl
import Etst.WFC.Utils.SelfDefinability.UniSetMapAtLe
import Etst.WFC.Utils.SelfDefinability.UniSetMapAtGe

public section
namespace Etst


theorem DefList.uniSetMapAt_eq
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: Expr .basic)
:
  Eq
    (uniSetMapAt dl n fv expr)
    (expr.triIntp (dl.prefix n).wfm (dl.prefix n).wfm fv)
:=
  Set3.ordApx.le_antisymm
    _ _
    (uniSetMapDl.uniSetMapAt_le dl n fv expr)
    (uniSetMapDl.uniSetMapAt_ge dl n fv expr)

theorem FinBoundedDl.ex_uniSetMapAt_eq
  (dl: FinBoundedDl)
  (fv: List Pair)
  (expr: Expr .basic)
:
  ∃ n,
    Eq
      (uniSetMapAt dl.toDefList n fv expr)
      (expr.triIntp dl.wfm dl.wfm fv)
:=
  let ⟨n, eqAtN⟩ := dl.ex_prefix_wfm_eq_expr fv expr
  ⟨n, (dl.uniSetMapAt_eq n fv expr).trans eqAtN⟩

theorem FiniteDefList.uniSetMapAt_eq
  (dl: FiniteDefList)
  (fv: List Pair)
  (expr: Expr .basic)
:
  Eq
    (uniSetMapAt dl.toDefList dl.size fv expr)
    (expr.triIntp dl.wfm dl.wfm fv)
:=
  dl.prefix_size_wfm_eq ▸
  dl.toDefList.uniSetMapAt_eq dl.size fv expr


theorem uniSetMap_isUniversal {s}
  (isDef: DefList.IsDefinable s)
:
  s ∈ uniSetMap
:=
  let ⟨dl, x, sEq⟩ := isDef
  let ⟨n, eqAtI⟩ := dl.ex_uniSetMapAt_eq [] (.const () x)
  let i := uniSetMapIndex dl.toDefList n [] (.const () x)
  ⟨i, eqAtI.trans sEq.symm⟩

theorem uniSetMap_isDefinable: DefList.IsDefinable uniSetMap := ⟨
  uniSetMapDl.dl.toFinBoundedDl,
  uniSetMapDl.const "uniSetMap",
  rfl,
⟩

theorem uniSetMap_containsItself: uniSetMap ∈ uniSetMap :=
  uniSetMap_isUniversal uniSetMap_isDefinable
