/-
  Defines `lfp.leOfOpLeMapped` and its special case,
  `lfp.leOfOpLeMappedSameOrd`.
-/

import Utils.Set3
import Utils.Valuation


/-
  If for all `t`, `opA t ≤ opB t`, then `lfp opA ≤ lfp opB`.
  
  Except generalized such that:
  * the operators may operate on different types, which are
    connected through a `mapping: Ta → Tb`.
  * the result order is not necessarily the same either of the
    orders with respect to which the operators are monotonic.
-/
def lfp.leOfOpLeMapped
  {ordA: PartialOrder Ta}
  {ordB: PartialOrder Tb}
  (isCcA: IsChainComplete ordA)
  (isCcB: IsChainComplete ordB)
  (opA: Ta → Ta)
  (opB: Tb → Tb)
  (isMonoA: IsMonotonic ordA ordA opA)
  (isMonoB: IsMonotonic ordB ordB opB)
  (mapping: Ta → Tb)
  {ordRes: PartialOrder Tb}
  (isMonoOrd: IsMonotonic ordRes ordRes opB)
  (le:
    ∀ {a lfpA},
      IsLfp ordA opA lfpA →
      ordA.le a lfpA →
      ordRes.le (mapping (opA a)) (opB (mapping a)))
  (mappingPreservesSuprema:
    (chA: Chain ordA) →
    IsSupremum
      ordB
      (mapping '' chA.set)
      (mapping (chA.sup isCcA).val))
  (supPreservesLe:
    ∀ {s0 s1 sup0 sup1}
      (_isSup0: IsSupremum ordB s0 sup0)
      (_isSup1: IsSupremum ordB s1 sup1)
      (_chLe0: ∀ e0: s0, ∃ e1: s1, ordRes.le e0 e1)
      (_chLe1: ∀ e1: s1, ∃ e0: s0, ordRes.le e0 e1)
    ,
      ordRes.le sup0 sup1)
:
  ordRes.le
    (mapping (lfp isCcA opA isMonoA).val)
    (lfp isCcB opB isMonoB).val
:=
  let ⟨lfpI, ⟨eqLfpA, eqLfpB⟩⟩ :=
    lfp.lfpIndex2 isCcA isCcB opA opB isMonoA isMonoB
  
  let lfpA := lfp isCcA opA isMonoA
  
  eqLfpA ▸ eqLfpB ▸
  lfpI.induction
    (fun n ih =>
      show
        mapping (stage isCcA opA isMonoA n)
          ≤
        stage isCcB opB isMonoB n
      from
        if h: n.IsActualLimit then
          let prevChainA :=
            lfp.stage.previousChain isCcA opA isMonoA n
          
          let isSupOfMapped := mappingPreservesSuprema prevChainA
          
          let isSupB := lfp.stage.limit isCcB opB isMonoB h
          
          let eqPrev :=
            lfp.stage.limitEq isCcA opA isMonoA h
              (prevChainA.sup isCcA).property
          
          eqPrev ▸
          supPreservesLe
            isSupOfMapped
            isSupB
            (fun ⟨_e0, e0In⟩ =>
              let ⟨_preE0, ⟨inPrev, isPre⟩⟩ := e0In.unwrap
              let ⟨⟨i, iLt⟩, eqAt⟩ := inPrev.unwrap
              
              ⟨
                ⟨
                  lfp.stage isCcB opB isMonoB i,
                  ⟨⟨i, iLt⟩, rfl⟩,
                ⟩,
                isPre ▸ eqAt ▸ ih i iLt,
              ⟩)
            (fun ⟨_e1, e1In⟩ =>
              let ⟨⟨i, iLt⟩, eqAt⟩ := e1In.unwrap
              
              ⟨
                ⟨
                  mapping (lfp.stage isCcA opA isMonoA i),
                  ⟨_, And.intro ⟨⟨i, iLt⟩, rfl⟩ rfl⟩
                ⟩,
                eqAt ▸ ih i iLt,
              ⟩)
        else
          let eqPredA := lfp.stage.predEq isCcA opA isMonoA h
          let eqPredB := lfp.stage.predEq isCcB opB isMonoB h
          
          let leLfpA := lfp.stage.leFP isCcA opA isMonoA n.pred
            ⟨lfpA.val, lfpA.property.isMember⟩
          
          let lePredStage := ih n.pred (Ordinal.predLtOfNotLimit h)
          
          let leL := le lfpA.property leLfpA
          let leR := isMonoOrd lePredStage
          
          eqPredA ▸ eqPredB ▸
          (leL.trans leR))


/-
  A special case of `lfp.leOfOpLeMapped` when the result order is
  the same as `ordB`.
-/
def lfp.leOfOpLeMappedSameOrd
  {ordA: PartialOrder Ta}
  {ordB: PartialOrder Tb}
  (isCcA: IsChainComplete ordA)
  (isCcB: IsChainComplete ordB)
  (opA: Ta → Ta)
  (opB: Tb → Tb)
  (isMonoA: IsMonotonic ordA ordA opA)
  (isMonoB: IsMonotonic ordB ordB opB)
  (mapping: Ta → Tb)
  (le:
    ∀ {a lfpA},
      IsLfp ordA opA lfpA →
      a ≤ lfpA →
      mapping (opA a) ≤ opB (mapping a))
  (mappingPreservesSuprema:
    (chA: Chain ordA) →
    IsSupremum
      ordB
      (mapping '' chA.set)
      (mapping (chA.sup isCcA).val))
:
  mapping (lfp isCcA opA isMonoA).val
    ≤
  (lfp isCcB opB isMonoB).val
:=
  lfp.leOfOpLeMapped
    isCcA
    isCcB
    opA
    opB
    isMonoA
    isMonoB
    mapping
    isMonoB
    le
    mappingPreservesSuprema
    fun isSup0 isSup1 setLe _ =>
      Supremum.leIfSetLeSet ⟨_, isSup0⟩ ⟨_, isSup1⟩ setLe
