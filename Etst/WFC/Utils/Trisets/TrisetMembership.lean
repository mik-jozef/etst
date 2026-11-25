/-
  Here we define WFC's notion of membership for the "sets" of WFC
  (ie. indices of uniSetMap quotiented by bisimilarity), and show
  the relation is well-defined on the quotient.
  
  This notion of membership is not the same as `Triset.DirectMem`
  from `Triset.lean`. The direct membership treats the empty triset
  and the undetermined triset as fully distinct trisets.
  The membership defined here is "fuzzy" in that a set containing
  one of these two trisets is considered to possibly contain the
  other as well (since settling the membership of possible elements
  of the undetermined set could produce the empty set).
  
  The underlying bisimilarity is defined in
  `TrisetBisimilarity.lean`.
-/
module
public import Etst.WFC.Utils.Trisets.TrisetBisimilarity

public section
namespace Etst

open Expr


exposed pairDefList isInDl extends bisimDl
  p3 IsIn :=
    Ex set elem,
    × set
    × elem
    × (Ex elemX,
      & IsBisim elem elemX
      & (?some elemX & uniSetMap set))
pairDefList.

/-
  A Lean-native definition of `IsIn`: `elem` is (a bisimilar copy of)
  an element of `set` in the given lane.
-/
exposed def isInDl.IsIn (lane: Set3.Lane) (set elem: Pair): Prop :=
  ∃ elemX,
    And
      (bisimDl.IsBisimAt lane elem elemX)
      (Pair.PreTriset.Has set lane elemX)

-- The definite-membership lane of `IsIn`.
exposed abbrev isInDl.IsInDef (set elem: Pair): Prop :=
  isInDl.IsIn .defLane set elem

-- The possible-membership lane of `IsIn`.
exposed abbrev isInDl.IsInPos (set elem: Pair): Prop :=
  isInDl.IsIn .posLane set elem


/-
  ## Section: inherited constants are unaffected by `isInDl`
-/

theorem isInDl.wfm_uniSetMap_eq:
  isInDl.val "uniSetMap" = uniSetMap
:=
  (isInDl.extend_wfm_eq bisimDl "uniSetMap").trans
    bisimDl.wfm_uniSetMap_eq

theorem isInDl.wfm_isBisim_eq:
  isInDl.val "IsBisim" = bisimDl.val "IsBisim"
:=
  isInDl.extend_wfm_eq bisimDl "IsBisim"


/-
  ## Section: WFM characterization of `IsIn`
-/

theorem isInDl.IsIn_of_mem {lane: Set3.Lane} {set elem w}
  -- TODO restore when Set3 has mem: Lane → Set D and call is lane uniform?
  -- (h: w ∈ (((isInDl.val "IsIn").call set).call elem).getLane lane)
  (h: .pair set (.pair elem w) ∈ (isInDl.val "IsIn").getLane lane)
:
  isInDl.IsIn lane set elem
:=
  let h := DefList.in_def_body_no_fv h
  let ⟨setA, h⟩ := inArbUnElim h
  let ⟨elemA, h⟩ := inArbUnElim h
  let ⟨hSet, h⟩ := inProdElim h
  let ⟨hElem, h⟩ := inProdElim h
  let setEq: setA = set := (inVarElim hSet rfl).symm
  let elemEq: elemA = elem := (inVarElim hElem rfl).symm
  let ⟨elemX, hIr⟩ := inArbUnElim h
  let ⟨hIsB, hSome⟩ := inIrElim hIr
  let ⟨pA1, hFn, hArg⟩ := inCallElim hIsB
  let pA1Eq: pA1 = elemX := inVarElim hArg rfl
  let ⟨pA2, hFn2, hArg2⟩ := inCallElim (pA1Eq ▸ hFn)
  let pA2Eq: pA2 = elemA := inVarElim hArg2 rfl
  let hIsBW: _ ∈ (isInDl.val "IsBisim").getLane lane :=
    elemEq ▸ pA2Eq ▸ hFn2
  let isB: bisimDl.IsBisimAt lane elem elemX :=
    bisimDl.IsBisimAt_of_pair_mem (wfm_isBisim_eq ▸ hIsBW)
  let ⟨w', hP⟩ := inSomeElim hSome
  let ⟨hVarX, hCall⟩ := inIrElim hP
  let w'Eq: w' = elemX := inVarElim hVarX rfl
  let ⟨pA3, hFn3, hArg3⟩ := inCallElim hCall
  let pA3Eq: pA3 = setA := inVarElim hArg3 rfl
  let hU := w'Eq ▸ pA3Eq ▸ hFn3
  let ins: elemX ∈ (uniSetMap.call set).getLane lane :=
    setEq ▸ wfm_uniSetMap_eq ▸ Set3.inCall (lane := lane) hU
  ⟨elemX, isB, ins⟩

theorem isInDl.IsIn.toMem {lane: Set3.Lane} {set elem w}
  (isIn: isInDl.IsIn lane set elem)
:
  -- TODO restore when Set3 has mem: Lane → Set D and call is lane uniform?
  -- w ∈ (((isInDl.val "IsIn").call set).call elem).getLane lane
  .pair set (.pair elem w) ∈ (isInDl.val "IsIn").getLane lane
:=
  let ⟨elemX, isB, ins⟩ := isIn
  let hIsB: .pair elem (.pair elemX w) ∈ (isInDl.val "IsBisim").getLane lane :=
    wfm_isBisim_eq.symm ▸ isB.toPairMem
  let hUni: .pair set elemX ∈ (isInDl.val "uniSetMap").getLane lane :=
    wfm_uniSetMap_eq.symm ▸ Set3.inCallElim ins
  DefList.in_def_no_fv <|
  inArbUn set
    (inArbUn elem
      (inProd (inVar rfl)
        (inProd (inVar rfl)
          (inArbUn elemX
            (inIr
              (inCall (inCall hIsB (inVar rfl)) (inVar rfl))
              (inSome w
                (inIr (inVar rfl)
                  (inCall hUni (inVar rfl)))))))))


/-
  ## Section: the `IsIn` lanes

  `IsIn set elem` says `elem` bisimulates some element of `set`.
-/

theorem isInDl.IsIn.respectsBisim {lane: Set3.Lane} {set elem set' elem': Pair}
  (isIn: isInDl.IsIn lane set elem)
  (setBisim: Pair.PreTriset.IsBisim set set')
  (elemBisim: Pair.PreTriset.IsBisim elem elem')
:
  isInDl.IsIn lane set' elem'
:=
  let ⟨_elemX, isB, ins⟩ := isIn
  let ⟨elemX', ins', elemXBisim⟩ := setBisim.has ins
  ⟨elemX', isB.respectsBisim elemBisim elemXBisim, ins'⟩


exposed def Triset.IsIn (lane: Set3.Lane): Pair.Triset → Pair.Triset → Prop :=
  Triset.liftBisim (isInDl.IsIn lane)
    (fun sBisim eBisim isIn => isIn.respectsBisim sBisim eBisim)

-- The definite-membership lane of `Triset.IsIn`.
exposed abbrev Triset.IsInDef (set elem: Pair.Triset): Prop :=
  Triset.IsIn .defLane set elem

-- The possible-membership lane of `Triset.IsIn`.
exposed abbrev Triset.IsInPos (set elem: Pair.Triset): Prop :=
  Triset.IsIn .posLane set elem


/-
  ## Section: the lanes coincide on hereditarily classical trisets
-/

theorem Triset.isInPos_iff_isInDef_of_hc {ts x: Pair.Triset}
  (hcTs: Pair.Triset.Hc ts)
  (hcX: Pair.Triset.Hc x)
:
  Triset.IsInPos ts x ↔ Triset.IsInDef ts x
:=
  Quotient.inductionOn₂
    (motive := fun t0 t1 =>
      Pair.Triset.Hc t0 →
      Pair.Triset.Hc t1 →
      (Triset.IsInPos t0 t1 ↔ Triset.IsInDef t0 t1))
    ts x
    (fun _a p hcTs hcX =>
      Iff.intro
        (fun ⟨x', isBP, inw⟩ =>
          let hcX': Pair.Triset.Hc ⟦x'⟧ := Pair.Triset.hc_hered hcTs inw
          let isBD: bisimDl.IsBisimDef p x' :=
            bisimDl.IsBisimPos.toIsBisimDef hcX hcX' isBP
          let ⟨x'', ins'', bisimX''⟩ := Pair.Triset.hc_ins_of_inw hcTs inw
          let isBD'': bisimDl.IsBisimDef p x'' :=
            fun nbp =>
              isBD
                (nbp.respectsBisim
                  (Pair.PreTriset.setoid.iseqv.refl p)
                  bisimX''.symm)
          ⟨x'', isBD'', ins''⟩)
        (fun ⟨x', isBD, ins⟩ => ⟨
          x',
          isBD.toIsBisimPos,
          Set3.defToPos ins,
        ⟩))
    hcTs hcX
