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
      operatorC_lfp_eqOn
        defsEq
        closed
        (fun x xIn => ih ⟨_, predLt⟩ x xIn))
