import Etst.WFC.Ch3_WellFoundedModel
import Etst.WFC.Utils.Expr.ConstRenaming
import Etst.WFC.Utils.Expr.ConstsVarsSat

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

def DefList.eq {dlSrc dlDst: DefList}
  (getDefEq: dlSrc.getDef = dlDst.getDef)
:
  dlSrc = dlDst
:=
  match dlSrc, dlDst, getDefEq with
  | ⟨_, _⟩, _, rfl => rfl


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
    conv => rhs; rw [←Expr.mapConst_eq_id expr]
    exact (BasicExpr.mapConst_triIntp2 (map := id) eqAtN eqAtN).symm
  ⟩


def Expr.noneLtSize {E: Type*}
  (size: Nat)
:
  (none (E := E)).ConstsLt size
:=
  nofun

def DefList.DependsOn.toUsesConst {getDef a b}
  (depOn: DependsOn getDef a b)
:
  ∃ x, (getDef x).UsesConst b
:=
  match depOn with
  | Base usesVar => ⟨_, usesVar⟩
  | Rec _ depOn => depOn.toUsesConst

def DefList.IsExprBoundedBy
  (dl: DefList)
  (expr: BasicExpr)
  (ub: Nat)
:
  Prop
:=
  ∀ x ∈ expr.UsesConst, DefList.IsDefBoundedBy dl.getDef x ub


namespace FiniteDefList
  def ConstsLt
    (getDef: DefList.GetDef)
    (size: Nat)
  :=
    ∀ x, (getDef x).ConstsLt size
  
  def isFinBounded_of_constsLt {getDef size}
    (constsLt: ConstsLt getDef size)
  :
    DefList.IsFinBounded getDef
  :=
    fun _ => ⟨
      size,
      fun depOn =>
        let ⟨x, usesVar⟩ := depOn.toUsesConst
        constsLt x _ usesVar,
    ⟩
end FiniteDefList

structure FiniteDefList extends FinBoundedDL where
  constNames: List String
  constsLt: FiniteDefList.ConstsLt getDef constNames.length
  noneAboveSize: ∀ {x}, constNames.length ≤ x → getDef x = .none
  isFinBounded := FiniteDefList.isFinBounded_of_constsLt constsLt

namespace FiniteDefList
  def size
    (dl: FiniteDefList)
  :=
    dl.constNames.length
  
  def empty: FiniteDefList := {
    getDef _ := Expr.none
    constNames := []
    constsLt _ := Expr.noneLtSize _
    noneAboveSize _ := rfl
    isClean _ := by decide
  }
  
  def emptySizeZero: empty.size = 0 := rfl
  
  structure Def (size: Nat) where
    name: String
    expr: BasicExpr
    constsLt: expr.ConstsLt size
    isClean: expr.IsClean
  
  def defsGetNth {ub} 
    (defs: List (Def ub))
    (n: Nat)
  :
    Def ub
  :=
    defs[n]?.getD {
      name := "«empty»"
      expr := Expr.none
      constsLt := Expr.noneLtSize ub
      isClean := by decide
    }
  
  def defsToGetDef {ub}
    (defs: List (Def ub))
  :
    DefList.GetDef
  :=
    fun x => (defsGetNth defs x).expr

  def defsToGetDef_gt_none {ub}
    (defs: List (Def ub))
    {x: Nat}
    (xGe: defs.length ≤ x)
  :
    defsToGetDef defs x = .none
  := by
    unfold defsToGetDef defsGetNth
    rw [List.getElem?_eq_none_iff.mpr xGe]
    rfl
  
  def extend {ub}
    (dl: FiniteDefList)
    (defs: List (Def ub))
    (ubEq: ub = dl.size + defs.length)
  :
    FiniteDefList
  :=
    let getDef :=
      fun x =>
        if x < dl.size
        then dl.getDef x
        else defsToGetDef defs (x - dl.size)
    {
      getDef
      constNames := dl.constNames ++ defs.map Def.name
      constsLt :=
        fun x y (usesVar: (getDef x).UsesConst y) => by
          unfold getDef at usesVar
          rw [List.length_append]
          if h: x < dl.size then
            rw [if_pos h] at usesVar
            apply Nat.lt_add_right
            exact dl.constsLt x y usesVar
          else
            rw [if_neg h] at usesVar
            unfold size at ubEq
            rw [List.length_map, ←ubEq]
            exact (defsGetNth defs (x - dl.size)).constsLt _ usesVar
      noneAboveSize {x} xGe :=
        if h: x < dl.size then
          let le := List.length_le_append_rite _ _
          False.elim (Nat.not_lt_of_ge xGe (Nat.lt_of_lt_of_le h le))
        else by
          unfold getDef
          rw [if_neg h]
          apply defsToGetDef_gt_none
          exact Nat.le_sub_of_add_le (by
            simpa [size, Nat.add_comm] using xGe)
      isClean x := by
        unfold getDef
        if h: x < dl.size then
          rw [if_pos h]
          exact dl.isClean x
        else
          rw [if_neg h]
          exact (defsGetNth defs (x - dl.size)).isClean
    }
  
  def ofDefs {ub}
    (defs: List (Def ub))
    (ubEq: ub = defs.length)
  :
    FiniteDefList
  :=
    empty.extend defs (by
      rw [emptySizeZero, Nat.zero_add];
      exact ubEq)

  def Prelude: FiniteDefList :=
    FiniteDefList.ofDefs (ub := 2) [
      {
        name := "Any"
        expr := Expr.arbUn (Expr.var 0)
        constsLt _ h := nomatch h
        isClean := by decide
      },
      {
        name := "None"
        expr := Expr.arbIr (Expr.var 0)
        constsLt _ h := nomatch h
        isClean := by decide
      }
    ] rfl
  
  def isExprBoundedBy
    (dl: FiniteDefList)
    (expr: BasicExpr)
  :
    dl.IsExprBoundedBy expr dl.size
  :=
    fun _ _ {dep} depOn =>
      let ⟨y, usesConst⟩ := depOn.toUsesConst
      dl.constsLt y dep usesConst


  def prefix_size_eq
    (dl: FiniteDefList)
  :
    dl.toDefList = dl.toDefList.prefix dl.size
  :=
    DefList.eq <|
    funext fun x =>
    if h: x < dl.size then
      (DefList.prefix_eq_at h).symm
    else
      DefList.prefix_none_at h ▸
      dl.noneAboveSize (le_of_not_gt h)

  def prefix_size_wfm_eq
    (dl: FiniteDefList)
  :
    (dl.toDefList.prefix dl.size).wfm = dl.wfm
  :=
    dl.prefix_size_eq ▸ rfl
  
  
  def extend_wfm_eq_of_lt {ub}
    (dlParent dlChild: FiniteDefList)
    {defs: List (Def ub)}
    (ubEq: ub = dlParent.size + defs.length)
    (childEq: dlChild = dlParent.extend defs ubEq)
    {x: Nat}
    (xLt: x < dlParent.size)
  :
    dlParent.wfm x = dlChild.wfm x
  :=
    let names y := y = x ∨ DefList.DependsOn dlParent.getDef x y
    let defsEq:
      DefListEq.EqDefsOn
        dlParent.toDefList
        (dlParent.extend defs ubEq).toDefList
        id
        names
    :=
      fun y yIn =>
        let yLt :=
          match yIn with
          | Or.inl yEq => yEq ▸ xLt
          | Or.inr depOn =>
            let ⟨z, usesConst⟩ := depOn.toUsesConst
            dlParent.constsLt z y usesConst
        let eqAtY:
          (dlParent.extend defs ubEq).getDef y = dlParent.getDef y
        := by
          show (if y < dlParent.size then _ else _) = dlParent.getDef y
          rw [if_pos yLt]
        (Expr.mapConst_eq_id _).trans eqAtY.symm
    let closed _ yIn _ zUsed :=
      match yIn with
      | Or.inl yEq =>
        Or.inr <| yEq ▸ DefList.DependsOn.Base zUsed
      | Or.inr depOn =>
        Or.inr <| depOn.push zUsed
    let eqAtX := DefList.eq_defs_eq_vals defsEq closed x (Or.inl rfl)
    childEq ▸ eqAtX
  
end FiniteDefList
