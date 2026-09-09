/-
  Here we define WFC's notion of membership for the "sets" of WFC
  (ie. indices of uniSetMap quotiented by bisimilarity), and show
  the relation is well-defined on the quotient.
  
  This notion of membership is not the same as `Triset.ExactMem`
  from `Triset.lean`. The exact membership treats the empty triset
  and the undetermined triset as fully distinct trisets.
  The membership defined here is "fuzzy" in that a set containing
  one of these two trisets is considered to possibly contain the
  other as well (since settling the membership of possible elements
  of the undetermined set could produce the empty set).
  
  The underlying bisimilarity is defined in
  `TrisetBisimilarity.lean`.
-/

import Etst.WFC.Utils.Trisets.TrisetBisimilarity

namespace Etst

open SingleLaneExpr


pairDefList isInDl extends bisimDl
  s3 IsIn :=
    Ex set elem,
    × set
    × elem
    × (Ex elemX,
      & IsBisim elem elemX
      & (?some elemX & uniSetMap set))
pairDefList.

-- A Lean-native definition of `IsIn`'s definite-membership lane:
-- `elem` is (a bisimilar copy of) a definite element of `set`.
def isInDl.IsInDef (set elem: Pair): Prop :=
  ∃ elemX, bisimDl.IsBisimDef elem elemX ∧ Pair.PreTriset.Ins set elemX

-- A Lean-native definition of `IsIn`'s possible-membership lane:
-- `elem` is (a bisimilar copy of) a possible element of `set`.
def isInDl.IsInPos (set elem: Pair): Prop :=
  ∃ elemX, bisimDl.IsBisimPos elem elemX ∧ Pair.PreTriset.Inw set elemX


/-
  ## Section: inherited constants are unaffected by `isInDl`
-/

def isInDl.wfm_uniSetMap_eq:
  isInDl.wfm isInDl.consts.uniSetMap = uniSetMap
:=
  (FiniteDefList.extend_wfm_eq_of_lt
    bisimDl isInDl rfl rfl (by decide)).symm.trans
    bisimDl.wfm_uniSetMap_eq

def isInDl.wfm_isBisim_eq:
  isInDl.wfm isInDl.consts.IsBisim = bisimDl.wfm bisimDl.consts.IsBisim
:=
  (FiniteDefList.extend_wfm_eq_of_lt
    bisimDl isInDl rfl rfl (by decide)).symm


/-
  ## Section: WFM characterization of `IsIn`
-/

def isInDl.IsInDef_of_defMem {set elem w}
  (h: ((isInDl.vals.IsIn.call set).call elem).defMem w)
:
  isInDl.IsInDef set elem
:=
  let h2 :=
    DefList.InWfm.in_def_no_fv (lane := .defLane)
      (Set3.inCallElim (lane := .defLane)
        (Set3.inCallElim (lane := .defLane) h))
  let ⟨setA, h2⟩ := inArbUnElim h2
  let ⟨elemA, h2⟩ := inArbUnElim h2
  let ⟨hSet, h2⟩ := inProdElim h2
  let ⟨hElem, h2⟩ := inProdElim h2
  let setEq: setA = set := (inVarElim hSet rfl).symm
  let elemEq: elemA = elem := (inVarElim hElem rfl).symm
  let ⟨elemX, hIr⟩ := inArbUnElim h2
  let ⟨hIsB, hSome⟩ := inIrElim hIr
  let ⟨pA1, hFn, hArg⟩ := inCallElim hIsB
  let pA1Eq: pA1 = elemX := inVarElim hArg rfl
  let ⟨pA2, hFn2, hArg2⟩ := inCallElim (pA1Eq ▸ hFn)
  let pA2Eq: pA2 = elemA := inVarElim hArg2 rfl
  let hIsBW: (isInDl.wfm isInDl.consts.IsBisim).defMem _ :=
    elemEq ▸ pA2Eq ▸ hFn2
  let isB: bisimDl.IsBisimDef elem elemX :=
    bisimDl.IsBisimDef_of_defMem (wfm_isBisim_eq ▸ hIsBW)
  let ⟨w', hP⟩ := inSomeElim hSome
  let ⟨hVarX, hCall⟩ := inIrElim hP
  let w'Eq: w' = elemX := inVarElim hVarX rfl
  let ⟨pA3, hFn3, hArg3⟩ := inCallElim hCall
  let pA3Eq: pA3 = setA := inVarElim hArg3 rfl
  let hU := w'Eq ▸ pA3Eq ▸ hFn3
  let ins: uniSetMap.defMem (.pair set elemX) :=
    setEq ▸ wfm_uniSetMap_eq ▸ hU
  ⟨elemX, isB, ins⟩

def isInDl.IsInDef.toDefMem {set elem w}
  (isIn: isInDl.IsInDef set elem)
:
  ((isInDl.vals.IsIn.call set).call elem).defMem w
:=
  let ⟨elemX, isB, ins⟩ := isIn
  let hIsB: (isInDl.wfm isInDl.consts.IsBisim).defMem _ :=
    wfm_isBisim_eq ▸ isB.toDefMem
  let hUni: (isInDl.wfm isInDl.consts.uniSetMap).defMem _ :=
    wfm_uniSetMap_eq ▸ ins
  DefList.InWfm.of_in_def_no_fv (lane := .defLane)
    (inArbUn set
      (inArbUn elem
        (inProd (inVar rfl)
          (inProd (inVar rfl)
            (inArbUn elemX
              (inIr
                (inCall (inCall hIsB (inVar rfl)) (inVar rfl))
                (inSome w
                  (inIr (inVar rfl)
                    (inCall hUni (inVar rfl))))))))))

def isInDl.IsInPos_of_posMem {set elem w}
  (h: ((isInDl.vals.IsIn.call set).call elem).posMem w)
:
  isInDl.IsInPos set elem
:=
  let h2 :=
    DefList.InWfm.in_def_no_fv (lane := .posLane)
      (Set3.inCallElim (lane := .posLane)
        (Set3.inCallElim (lane := .posLane) h))
  let ⟨setA, h2⟩ := inArbUnElim h2
  let ⟨elemA, h2⟩ := inArbUnElim h2
  let ⟨hSet, h2⟩ := inProdElim h2
  let ⟨hElem, h2⟩ := inProdElim h2
  let setEq: setA = set := (inVarElim hSet rfl).symm
  let elemEq: elemA = elem := (inVarElim hElem rfl).symm
  let ⟨elemX, hIr⟩ := inArbUnElim h2
  let ⟨hIsB, hSome⟩ := inIrElim hIr
  let ⟨pA1, hFn, hArg⟩ := inCallElim hIsB
  let pA1Eq: pA1 = elemX := inVarElim hArg rfl
  let ⟨pA2, hFn2, hArg2⟩ := inCallElim (pA1Eq ▸ hFn)
  let pA2Eq: pA2 = elemA := inVarElim hArg2 rfl
  let hIsBW: (isInDl.wfm isInDl.consts.IsBisim).posMem _ :=
    elemEq ▸ pA2Eq ▸ hFn2
  let isB: bisimDl.IsBisimPos elem elemX :=
    bisimDl.IsBisimPos_of_posMem (wfm_isBisim_eq ▸ hIsBW)
  let ⟨w', hP⟩ := inSomeElim hSome
  let ⟨hVarX, hCall⟩ := inIrElim hP
  let w'Eq: w' = elemX := inVarElim hVarX rfl
  let ⟨pA3, hFn3, hArg3⟩ := inCallElim hCall
  let pA3Eq: pA3 = setA := inVarElim hArg3 rfl
  let hU := w'Eq ▸ pA3Eq ▸ hFn3
  let inw: uniSetMap.posMem (.pair set elemX) :=
    setEq ▸ wfm_uniSetMap_eq ▸ hU
  ⟨elemX, isB, inw⟩

def isInDl.IsInPos.toPosMem {set elem w}
  (isIn: isInDl.IsInPos set elem)
:
  ((isInDl.vals.IsIn.call set).call elem).posMem w
:=
  let ⟨elemX, isB, inw⟩ := isIn
  let hIsB: (isInDl.wfm isInDl.consts.IsBisim).posMem _ :=
    wfm_isBisim_eq ▸ isB.toPosMem
  let hUni: (isInDl.wfm isInDl.consts.uniSetMap).posMem _ :=
    wfm_uniSetMap_eq ▸ inw
  DefList.InWfm.of_in_def_no_fv (lane := .posLane)
    (inArbUn set
      (inArbUn elem
        (inProd (inVar rfl)
          (inProd (inVar rfl)
            (inArbUn elemX
              (inIr
                (inCall (inCall hIsB (inVar rfl)) (inVar rfl))
                (inSome w
                  (inIr (inVar rfl)
                    (inCall hUni (inVar rfl))))))))))


/-
  ## Section: the `IsIn` lanes

  `IsIn set elem` says `elem` bisimulates some element of `set`.
-/

def isInDl.IsInDef.respectsBisim {set elem set' elem': Pair}
  (isIn: IsInDef set elem)
  (setBisim: Pair.PreTriset.IsBisim set set')
  (elemBisim: Pair.PreTriset.IsBisim elem elem')
:
  IsInDef set' elem'
:=
  let ⟨elemX, isB, ins⟩ := isIn
  let ⟨R, isBisimSet, Rss'⟩ := setBisim
  let ⟨elemX', ins', RxX'⟩ := isBisimSet.left .ins _ _ elemX Rss' ins
  ⟨elemX', isB.respectsBisim elemBisim ⟨R, isBisimSet, RxX'⟩, ins'⟩

def isInDl.IsInPos.respectsBisim {set elem set' elem': Pair}
  (isIn: IsInPos set elem)
  (setBisim: Pair.PreTriset.IsBisim set set')
  (elemBisim: Pair.PreTriset.IsBisim elem elem')
:
  IsInPos set' elem'
:=
  let ⟨elemX, isB, inw⟩ := isIn
  let ⟨R, isBisimSet, Rss'⟩ := setBisim
  let ⟨elemX', inw', RxX'⟩ := isBisimSet.left .inw _ _ elemX Rss' inw
  ⟨elemX', isB.respectsBisim elemBisim ⟨R, isBisimSet, RxX'⟩, inw'⟩


def Triset.IsInDef (set elem: Pair.Triset) :=
  let respects
    s0 e0 s1 e1
    (sBisim: Pair.PreTriset.setoid.r s0 s1)
    (eBisim: Pair.PreTriset.setoid.r e0 e1)
  :
    isInDl.IsInDef s0 e0 = isInDl.IsInDef s1 e1
  :=
    propext (Iff.intro
      (fun isIn => isIn.respectsBisim sBisim eBisim)
      (fun isIn =>
        isIn.respectsBisim
          (Pair.PreTriset.setoid.iseqv.symm sBisim)
          (Pair.PreTriset.setoid.iseqv.symm eBisim)))
  Quotient.lift₂ isInDl.IsInDef respects set elem

def Triset.IsInPos (set elem: Pair.Triset) :=
  let respects
    s0 e0 s1 e1
    (sBisim: Pair.PreTriset.setoid.r s0 s1)
    (eBisim: Pair.PreTriset.setoid.r e0 e1)
  :
    isInDl.IsInPos s0 e0 = isInDl.IsInPos s1 e1
  :=
    propext (Iff.intro
      (fun isIn => isIn.respectsBisim sBisim eBisim)
      (fun isIn =>
        isIn.respectsBisim
          (Pair.PreTriset.setoid.iseqv.symm sBisim)
          (Pair.PreTriset.setoid.iseqv.symm eBisim)))
  Quotient.lift₂ isInDl.IsInPos respects set elem


/-
  ## Section: the lanes coincide on hereditarily classical trisets
-/

def Triset.isInPos_iff_isInDef_of_hc {ts x: Pair.Triset}
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
        (fun ⟨x', isBD, ins⟩ => ⟨x', isBD.toIsBisimPos, ins.toPos⟩))
    hcTs hcX
