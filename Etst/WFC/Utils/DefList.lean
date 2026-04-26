import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Expr.ConstRenaming

namespace Etst

namespace DefListEq
  abbrev InvariantOn
    (map: Nat → Nat)
    (names: Set Nat)
    (vSrc vDst: Valuation Pair)
  :
    Prop
  :=
    ∀ x ∈ names, vSrc x = vDst (map x)
  
  abbrev EqDefsOn
    (dlSrc dlDst: DefList)
    (map: Nat → Nat)
    (names: Set Nat)
  :
    Prop
  :=
    ∀ x ∈ names, (dlSrc.getDef x).mapConst map = dlDst.getDef (map x)
  
  abbrev ClosedUnderUses
    (dl: DefList)
    (names: Set Nat)
  :
    Prop
  :=
    ∀ x ∈ names, ∀ y ∈ (dl.getDef x).UsesConst, y ∈ names
  
  
  def intpDefs2_eqOn {map dlSrc dlDst names bSrc bDst cSrc cDst}
    (defsEq: EqDefsOn dlSrc dlDst map names)
    (closed: ClosedUnderUses dlSrc names)
    (eqB: InvariantOn map names bSrc bDst)
    (eqC: InvariantOn map names cSrc cDst)
    {x: Nat}
    (xIn: x ∈ names)
  :
    dlSrc.intpDefs2 bSrc cSrc x = dlDst.intpDefs2 bDst cDst (map x)
  :=
    let eq :=
      BasicExpr.mapConst_triIntp2
        map
        (fun y yUsed => eqB y (closed x xIn y yUsed))
        (fun y yUsed => eqC y (closed x xIn y yUsed))
    eq.symm.trans (defsEq x xIn ▸ rfl)
  
  
  def operatorC_lfp_eqOn {map names dlSrc dlDst bSrc bDst}
    (defsEq: EqDefsOn dlSrc dlDst map names)
    (closed: ClosedUnderUses dlSrc names)
    (eqB: InvariantOn map names bSrc bDst)
  :
    InvariantOn map names
      (operatorC.lfp dlSrc bSrc)
      (operatorC.lfp dlDst bDst)
  :=
    let _ := Valuation.ordStdLattice Pair
    OrderHom.lfpStage_induction2
      (operatorC dlSrc bSrc)
      (operatorC dlDst bDst)
      (InvariantOn map names)
      (fun n _ ih x xIn => by
        let _ := Set3.ordStd Pair
        let prevSrc (m: ↑n): Valuation Pair :=
          (operatorC dlSrc bSrc).lfpStage m
        let prevDst (m: ↑n): Valuation Pair :=
          (operatorC dlDst bDst).lfpStage m
        let isLubSrc :=
          PartialOrder.isLUB_pointwise_isLUB
            (isLUB_iSup (f := prevSrc))
            x
        let isLubDst :=
          PartialOrder.isLUB_pointwise_isLUB
            (isLUB_iSup (f := prevDst))
            (map x)
        let atEq:
          (Set.range prevSrc).pointwiseImage x
            =
          (Set.range prevDst).pointwiseImage (map x)
        := by
          ext t
          constructor
          · rintro ⟨_v, ⟨m, rfl⟩, tvEq⟩
            exact ⟨prevDst m, ⟨m, rfl⟩, (ih m x xIn).symm.trans tvEq⟩
          · rintro ⟨_v, ⟨m, rfl⟩, tvEq⟩
            exact ⟨prevSrc m, ⟨m, rfl⟩, (ih m x xIn).trans tvEq⟩
        exact (IsLUB.unique isLubSrc (atEq ▸ isLubDst)))
      (fun _ _ predLt ih x xIn =>
        let eqC y yIn := ih ⟨_, predLt⟩ y yIn
        intpDefs2_eqOn defsEq closed eqB eqC xIn)
  
end DefListEq

open DefListEq in
def DefList.eq_defs_eq_vals
  {dlSrc dlDst: DefList}
  {map: Nat → Nat}
  {names: Set Nat}
  (defsEq: EqDefsOn dlSrc dlDst map names)
  (closed: ClosedUnderUses dlSrc names)
:
  InvariantOn map names dlSrc.wfm dlDst.wfm
:=
  let _ := Valuation.ordApx Pair
  let _ : Inhabited (Valuation Pair) := inferInstance
  OrderHom.lfpStageCc_induction2
    isCcApx
    isCcApx
    (operatorB dlSrc)
    (operatorB dlDst)
    (InvariantOn map names)
    (fun n _ ih isChainSrc isChainDst x xIn =>
      let prevSrc (m: ↑n): Valuation Pair :=
        (operatorB dlSrc).lfpStageCc isCcApx m
      let prevDst (m: ↑n): Valuation Pair :=
        (operatorB dlDst).lfpStageCc isCcApx m
      let _ := Set3.ordApx Pair
      let isLubSrc :=
        PartialOrder.isLUB_pointwise_isLUB
          ((isCcApx isChainSrc).choose_spec)
          x
      let isLubDst :=
        PartialOrder.isLUB_pointwise_isLUB
          ((isCcApx isChainDst).choose_spec)
          (map x)
      let atEq:
        (Set.range prevSrc).pointwiseImage x
          =
        (Set.range prevDst).pointwiseImage (map x)
      := by
        ext t
        constructor
        · rintro ⟨_v, ⟨⟨m, mLt⟩, rfl⟩, tvEq⟩
          exact ⟨
            prevDst ⟨m, mLt⟩,
            ⟨⟨m, mLt⟩, rfl⟩,
            tvEq ▸ (ih ⟨m, mLt⟩ x xIn).symm
          ⟩
        · rintro ⟨_v, ⟨⟨m, mLt⟩, rfl⟩, tvEq⟩
          exact ⟨
            prevSrc ⟨m, mLt⟩,
            ⟨⟨m, mLt⟩, rfl⟩,
            tvEq ▸ (ih ⟨m, mLt⟩ x xIn)
          ⟩
      IsLUB.unique isLubSrc (atEq ▸ isLubDst)
    )
    (fun _ _ predLt ih =>
      operatorC_lfp_eqOn defsEq closed (ih ⟨_, predLt⟩))


def DefList.prefix
  (dl: DefList)
  (n: Nat)
:
  DefList
:= {
  getDef x := if x < n then dl.getDef x else .none
  isClean x :=
    if h: x < n
    then if_pos h ▸ dl.isClean x
    else if_neg h ▸ nofun
}

def DefList.prefix_eq_at
  {dl: DefList}
  {n x} (lt: x < n)
:
  (dl.prefix n).getDef x = dl.getDef x
:=
  if_pos lt

def DefList.prefix_none_at
  {dl: DefList}
  {n x} (nlt: ¬ x < n)
:
  (dl.prefix n).getDef x = .none
:=
  if_neg nlt


def FinBoundedDL.ex_expr_uses_bound
  (dl: FinBoundedDL)
  (expr: BasicExpr)
:
  ∃ n,
  ∀ x ∈ expr.UsesConst,
    x < n ∧ DefList.IsDefBoundedBy dl.getDef x n
:=
  match expr with
  | .const x =>
    let ⟨bound, depsLt⟩ := dl.isFinBounded x
    let n := max (x + 1) bound
    ⟨n, fun _ yEq =>
      yEq ▸ ⟨
        Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_max_left _ _),
        fun depOn =>
          Nat.lt_of_lt_of_le (depsLt depOn) (Nat.le_max_right _ _)
      ⟩
    ⟩
  | .var _ => ⟨0, nofun⟩
  | .null => ⟨0, nofun⟩
  | .pair left rite
  | .ir left rite =>
    let ⟨nL, hL⟩ := dl.ex_expr_uses_bound left
    let ⟨nR, hR⟩ := dl.ex_expr_uses_bound rite
    let n := max nL nR
    ⟨n, fun x xIn =>
      match xIn with
      | Or.inl xInL =>
        let ⟨xLt, depsLt⟩ := hL x xInL
        ⟨
          Nat.lt_of_lt_of_le xLt (Nat.le_max_left _ _),
          fun depOn =>
            Nat.lt_of_lt_of_le (depsLt depOn) (Nat.le_max_left _ _)
        ⟩
      | Or.inr xInR =>
        let ⟨xLt, depsLt⟩ := hR x xInR
        ⟨
          Nat.lt_of_lt_of_le xLt (Nat.le_max_right _ _),
          fun depOn =>
            Nat.lt_of_lt_of_le (depsLt depOn) (Nat.le_max_right _ _)
        ⟩
    ⟩
  | .full body
  | .compl body
  | .arbIr body => dl.ex_expr_uses_bound body


def FinBoundedDL.prefix_wfm_eq_of_lt
  (dl: FinBoundedDL)
  {x n: Nat}
  (xLtN: x < n)
  (depsLtN: ∀ {dep}, DefList.DependsOn dl.getDef x dep → dep < n)
:
  (dl.prefix n).wfm x = dl.wfm x
:=
  let names y := y = x ∨ DefList.DependsOn dl.getDef x y
  let defsEq:
    DefListEq.EqDefsOn dl.toDefList (dl.prefix n) id names
  :=
    fun y yIn =>
      let yLtN: y < n :=
        match yIn with
        | Or.inl yEq => yEq ▸ xLtN
        | Or.inr depOn => depsLtN depOn
      (Expr.mapConst_eq_id _).trans (dl.prefix_eq_at yLtN).symm
  let closed _ yIn _ zUsed :=
      match yIn with
      | Or.inl yEq =>
        Or.inr <| yEq ▸ DefList.DependsOn.Base zUsed
      | Or.inr depOn =>
        Or.inr <| depOn.push zUsed
  let eqAtN := DefList.eq_defs_eq_vals defsEq closed x (Or.inl rfl)
  eqAtN.symm

def FinBoundedDL.ex_prefix_wfm_eq
  (dl: FinBoundedDL)
  (x: Nat)
:
  ∃ n, (dl.prefix n).wfm x = dl.wfm x
:=
  let ⟨bound, depsLt⟩ := dl.isFinBounded x
  let n := max (x + 1) bound
  let xLtN: x < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_max_left _ _)
  let depsLtN {dep} (depOn: DefList.DependsOn dl.getDef x dep):
    dep < n
  :=
    Nat.lt_of_lt_of_le (depsLt depOn) (Nat.le_max_right _ _)
  ⟨n, dl.prefix_wfm_eq_of_lt xLtN depsLtN⟩

def FinBoundedDL.ex_prefix_wfm_eq_expr
  (dl: FinBoundedDL)
  (fv: List Pair)
  (expr: BasicExpr)
:
  ∃ n, expr.triIntp fv (dl.prefix n).wfm = expr.triIntp fv dl.wfm
:=
  let ⟨n, isBounded⟩ := dl.ex_expr_uses_bound expr
  let eqAtN x xIn :=
    let ⟨xLtN, depsLtN⟩ := isBounded x xIn
    dl.prefix_wfm_eq_of_lt xLtN depsLtN
  ⟨n, by
    simpa [BasicExpr.triIntp, Expr.mapConst_eq_id] using
      (BasicExpr.mapConst_triIntp2
        (map := id)
        (expr := expr)
        (fv := fv)
        (bSrc := (dl.prefix n).wfm)
        (bDst := dl.wfm)
        (cSrc := (dl.prefix n).wfm)
        (cDst := dl.wfm)
        eqAtN
        eqAtN).symm
  ⟩
