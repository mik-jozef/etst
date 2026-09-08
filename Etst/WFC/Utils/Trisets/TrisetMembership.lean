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
