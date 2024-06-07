/-
  Contains helper defs about operators B and C.
-/

import WFC.Ch4_Operators


structure operatorC.FixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
  (bA: Valuation salg.D)
  (bB: Valuation salg.D)
  (n: Ordinal): Prop
where
  eqLfpA: operatorC.stage salg dlA bA n = (operatorC.lfp salg dlA bA).val
  eqLfpB: operatorC.stage salg dlB bB n = (operatorC.lfp salg dlB bB).val

noncomputable def operatorC.fixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
  (bA: Valuation salg.D)
  (bB: Valuation salg.D)
:
  { n // operatorC.FixedIndex2 salg dlA dlB bA bB n }
:=
  let fixedA := operatorC.fixedIndex salg dlA bA
  let fixedB := operatorC.fixedIndex salg dlB bB
  
  if h: fixedA.val ≤ fixedB.val then
    ⟨
      fixedB.val,
      ⟨
        let isLfpAtB := lfp.stage.gtLfpEqLfp
          (Valuation.ord.standard.isChainComplete salg.D)
          (operatorC salg dlA bA)
          (operatorC.isMonotonic salg dlA bA)
          h
          ((operatorC.lfp salg dlA bA).property)
        
        iIsLeast.isUnique
          (Valuation.ord.standard salg.D)
          isLfpAtB
          (lfp salg dlA bA).property,
        fixedB.property,
      ⟩
    ⟩
  else
    ⟨
      fixedA.val,
      ⟨
        fixedA.property,
        let isLfpAtA := lfp.stage.gtLfpEqLfp
          (Valuation.ord.standard.isChainComplete salg.D)
          (operatorC salg dlB bB)
          (operatorC.isMonotonic salg dlB bB)
          (le_of_not_le h)
          ((operatorC.lfp salg dlB bB).property)
        
        iIsLeast.isUnique
          (Valuation.ord.standard salg.D)
          isLfpAtA
          (lfp salg dlB bB).property,
      ⟩
    ⟩


structure operatorB.FixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
  (n: Ordinal): Prop
where
  eqLfpA: operatorB.stage salg dlA n = (operatorB.lfp salg dlA).val
  eqLfpB: operatorB.stage salg dlB n = (operatorB.lfp salg dlB).val

noncomputable def operatorB.fixedIndex2
  (salg: Salgebra sig)
  (dlA: DefList sig)
  (dlB: DefList sig)
:
  { n // operatorB.FixedIndex2 salg dlA dlB n }
:=
  let fixedA := operatorB.fixedIndex salg dlA
  let fixedB := operatorB.fixedIndex salg dlB
  
  if h: fixedA.val ≤ fixedB.val then
    ⟨
      fixedB.val,
      ⟨
        let isLfpAtB := lfp.stage.gtLfpEqLfp
          (Valuation.ord.approximation.isChainComplete salg.D)
          (operatorB salg dlA)
          (operatorB.isMonotonic salg dlA)
          h
          ((operatorB.lfp salg dlA).property)
        
        iIsLeast.isUnique
          (Valuation.ord.approximation salg.D)
          isLfpAtB
          (lfp salg dlA).property,
        fixedB.property,
      ⟩
    ⟩
  else
    ⟨
      fixedA.val,
      ⟨
        fixedA.property,
        let isLfpAtA := lfp.stage.gtLfpEqLfp
          (Valuation.ord.approximation.isChainComplete salg.D)
          (operatorB salg dlB)
          (operatorB.isMonotonic salg dlB)
          (le_of_not_le h)
          ((operatorB.lfp salg dlB).property)
        
        iIsLeast.isUnique
          (Valuation.ord.approximation salg.D)
          isLfpAtA
          (lfp salg dlB).property,
      ⟩
    ⟩
