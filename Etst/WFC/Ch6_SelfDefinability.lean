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

import Etst.WFC.Utils.DefList
import Etst.WFC.Utils.SelfDefinability.UniSetMapAtLe
import Etst.WFC.Utils.SelfDefinability.UniSetMapAtGe

namespace Etst


def uniSetMapDl.uniSetMapAt_eq
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  uniSetMapAt dl n fv expr = expr.triIntp fv (dl.prefix n).wfm
:=
  Set3.ordApx.le_antisymm
    _ _
    (uniSetMapAt_le dl n fv expr)
    (uniSetMapAt_ge dl n fv expr)

def uniSetMapDl.ex_uniSetMapAt_eq
  (dl: FinBoundedDL)
  (fv: List Pair)
  (expr: BasicExpr)
:
  ∃ n, uniSetMapAt dl.toDefList n fv expr = expr.triIntp fv dl.wfm
:=
  let ⟨n, eqAtN⟩ := dl.ex_prefix_wfm_eq_expr fv expr
  ⟨n, (uniSetMapAt_eq dl.toDefList n fv expr).trans eqAtN⟩

def uniSetMap.isUniversal {s}
  (isDef: DefList.IsDefinable s)
:
  s ∈ uniSetMap
:=
  let ⟨dl, x, sEq⟩ := isDef
  let ⟨n, eqAtI⟩ := uniSetMapDl.ex_uniSetMapAt_eq dl [] (.const x)
  let i := uniSetMapIndex dl.toDefList n [] (.const x)
  ⟨i, eqAtI.trans sEq.symm⟩


def uniSetMap.isDefinable: DefList.IsDefinable uniSetMap := ⟨
  uniSetMapDl.toFinBoundedDL,
  uniSetMapDl.consts.uniSetMap,
  rfl,
⟩

def uniSetMap.containsItself: uniSetMap ∈ uniSetMap :=
  uniSetMap.isUniversal uniSetMap.isDefinable
