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
  `/Etst/WFC/Utils/UniSetMap/` for the details.
-/

import Etst.WFC.Utils.DefListEq
import Etst.WFC.Utils.SelfDefinability.UniSetMapAtLe
import Etst.WFC.Utils.SelfDefinability.UniSetMapAtGe

namespace Etst


def FinBoundedDL.ex_prefix_wfm_eq
  (dl: FinBoundedDL)
  (x: Nat)
:
  ∃ n, (dl.prefix n).wfm x = dl.wfm x
:=
  let dlDef := dl.toDefList
  let names y := y = x ∨ DefList.DependsOn dlDef.getDef x y
  let ⟨bound, depsLt⟩ := dl.isFinBounded x
  let n := max (x + 1) bound
  let xLtN: x < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_max_left _ _)
  let defsEq:
    DefListEq.EqDefsOn dlDef (dlDef.prefix n) id names
  :=
    fun y yIn =>
      let yLtN: y < n :=
        match yIn with
        | Or.inl yEq => yEq ▸ xLtN
        | Or.inr depOn =>
          Nat.lt_of_lt_of_le
            (depsLt depOn)
            (Nat.le_max_right _ _)
      (Expr.mapConst_eq_id _).trans (dlDef.prefix_eq_at yLtN).symm
  let closed _ yIn _ zUsed :=
      match yIn with
      | Or.inl yEq =>
        Or.inr <| yEq ▸ DefList.DependsOn.Base zUsed
      | Or.inr depOn =>
        Or.inr <| depOn.push zUsed
  let eqAtN := DefList.eq_defs_eq_vals defsEq closed x (Or.inl rfl)
  ⟨n, eqAtN.symm⟩


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

def uniSetMap.isUniversal {s}
  (isDef: DefList.IsDefinable s)
:
  s ∈ uniSetMap
:=
  let ⟨dl, x, sEq⟩ := isDef
  let ⟨n, eqAtN⟩ := dl.ex_prefix_wfm_eq x
  let i := uniSetMapIndex dl.toDefList n [] (.const x)
  let eqAtI := uniSetMapDl.uniSetMapAt_eq dl.toDefList n [] (.const x)
  ⟨i, Eq.trans (eqAtI.trans eqAtN) sEq.symm⟩


def uniSetMap.isDefinable: DefList.IsDefinable uniSetMap := ⟨
  uniSetMapDl.toFinBoundedDL,
  uniSetMapDl.consts.uniSetMap,
  rfl,
⟩

def uniSetMap.containsItself: uniSetMap ∈ uniSetMap :=
  uniSetMap.isUniversal uniSetMap.isDefinable
