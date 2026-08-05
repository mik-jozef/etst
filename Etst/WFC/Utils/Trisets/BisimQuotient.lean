/-
  Here we quotient indices of uniSetMap bisimilarity to define the "sets"
  of WFC.
  
  This quotient is based on the actual ("exact") bisimilarity defined
  as a Lean property, and is not WFC-definable (as WFC cannot treat the
  definite and possible membership separately). Contrast with the "fuzzy"
  bisimilarity of `Etst/WFC/Utils/Trisets/TrisetMembership.lean`, which
  is WFC-definable, and coincides with exact bisimilarity for classical
  trisets.
  
  The main purpose of quotienting the sets is to get an assurance that
  the operations on them respect their intended semantics, so that we
  don't, for example, treat two pairs coding empty sets differently just
  because they are different pairs.
-/

import Etst.WFC.Ch7_Polymorphism
import Etst.WFC.Utils.General.Bisimilarity

namespace Etst


structure TriRelation (T: Type*) where
  RelDef: T → T → Prop
  RelPos: T → T → Prop
  def_le_pos: ∀ {a b: T}, RelDef a b → RelPos a b

structure TriRelation.Sat {T: Type*}
  (rel: TriRelation T)
  (P: Set (T → T → Prop))
where
  satDef: P rel.RelDef
  satPos: P rel.RelPos


namespace Set3Pair
  def PreTriset := Pair
  
  -- Strong (a la "definite") membership, `a ∈ b`.
  def PreTriset.Ins (ts elem: PreTriset): Prop :=
    (uniSetMap.call ts).defMem elem
  
  -- Weak (a la "possible") membership, `a ∈? b`.
  def PreTriset.Inw (ts elem: PreTriset): Prop :=
    (uniSetMap.call ts).posMem elem
  
  open PreTriset
  
  inductive TransitionLabels where
  | ins
  | inw
  
  -- One can transition sets to their elements.
  def transitionSystem:
    LabeledTransitionSystem TransitionLabels PreTriset
  := fun
    | .ins, a, b => a.Ins b
    | .inw, a, b => a.Inw b
  
  def Bisim := transitionSystem.IsBisimilar
  
  def trisetSetoid: Setoid PreTriset where
    r := Bisim
    iseqv := transitionSystem.IsBisimilar_is_equivalence
  
  def Triset := Quotient trisetSetoid
  
  structure TrisetIns
    (ts elem: Triset)
    (preTs preElem: PreTriset)
  :
    Prop
  where
    tsEq: ts = ⟦preTs⟧
    elemEq: elem = ⟦preElem⟧
    ins: preTs.Ins preElem
  
  structure TrisetInw
    (ts elem: Triset)
    (preTs preElem: PreTriset)
  :
    Prop
  where
    tsEq: ts = ⟦preTs⟧
    elemEq: elem = ⟦preElem⟧
    inw: preTs.Inw preElem
  
  def Triset.ExactIns (ts elem: Triset): Prop :=
    ∃ preTs preElem, TrisetIns ts elem preTs preElem
  
  def Triset.ExactInw (ts elem: Triset): Prop :=
    ∃ preTs preElem, TrisetInw ts elem preTs preElem
  
  def Triset.ExactMem: TriRelation Triset where
    RelDef := Triset.ExactIns
    RelPos := Triset.ExactInw
    def_le_pos
    | ⟨preTs, preElem, ⟨tsEq, elemEq, ins⟩⟩ =>
      ⟨preTs, preElem, ⟨tsEq, elemEq, ins.toPos⟩⟩
  
  
  -- Not hereditarily classical.
  inductive Triset.Nhc: Triset → Prop
  | notClassical {ts elem: Triset}
      (isPos: ts.ExactInw elem)
      (notDef: ¬ ts.ExactIns elem)
    :
      Triset.Nhc ts
  | containsNhc {ts elem: Triset}
      (isPos: ts.ExactInw elem)
      (isNhc: Triset.Nhc elem)
    :
      Triset.Nhc ts
  
  -- Hereditarily classical.
  def Triset.Hc (ts: Triset): Prop := ¬ Triset.Nhc ts
  
end Set3Pair
