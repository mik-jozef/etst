import Etst.WFC.Utils.Valuation

namespace Etst


def LubPreservesOtherOrder
  (ord: PartialOrder T)
  (ordOther: PartialOrder T)
:
  Prop
:=
  {s: Set T} →
  {lub ub: T} →
  @IsLUB _ ord.toLE s lub →
  (∀ t ∈ s, ordOther.le t ub) →
  Nonempty s →
  ordOther.le lub ub

def LubsPreserveOtherOrder
  (ord: PartialOrder T)
  (ordOther: PartialOrder T)
:
  Prop
:=
  {a b: Set T} →
  {lubA lubB: T} →
  @IsLUB _ ord.toLE a lubA →
  @IsLUB _ ord.toLE b lubB →
  (∀ tA ∈ a, ∃ tB ∈ b, ordOther.le tA tB) →
  (∀ tB ∈ b, ∃ tA ∈ a, ordOther.le tA tB) →
  ordOther.le lubA lubB


def Valuation.ordStd.lubPreservesLeApxLub:
  LubsPreserveOtherOrder
    (Valuation.ordStd T)
    (Valuation.ordApx T)
:=
  fun isLubA isLubB ab ba x => {
    defLe :=
      fun _d dInSupA =>
        let ⟨valA, valAInA, dInAtX⟩ :=
          Valuation.ordStd.in_some_set_of_in_sup_defMem
            isLubA dInSupA
        
        let ⟨_tB, tbInB, valALe⟩ := ab valA valAInA
        
        (isLubB.left tbInB x).defLe
          ((valALe x).defLe dInAtX)
    posLe :=
      fun _d dInSupB =>
        let ⟨valB, valBInB, dInAtX⟩ :=
          Valuation.ordStd.in_some_set_of_in_sup_posMem
            isLubB dInSupB

        let ⟨_tA, taInA, valBLe⟩ := ba valB valBInB
        
        (isLubA.left taInA x).posLe
          ((valBLe x).posLe dInAtX)
  }

def Valuation.ordStd.lubPreservesLeApx:
  LubPreservesOtherOrder
    (Valuation.ordStd T)
    (Valuation.ordApx T)
:=
  fun {_s _lub ub} isLub le ⟨t, tInS⟩ =>
    lubPreservesLeApxLub
      isLub
      (@isLUB_singleton _ (ordStd T).toPreorder ub)
      (fun v vIn => ⟨ub, rfl, le v vIn⟩)
      (fun _ eq => ⟨t, tInS, eq ▸ le t tInS⟩)
