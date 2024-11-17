/-
  `Pair.uniSet3.isUniversal` is the main result of this volume.
  It states that any definable triset of pairs is in a sense
  "contained" in the triset `uniSet3`. See chapter 7 for more
  info.
-/

import UniSet3.Ch9_S1_InternalGe


namespace Pair
  open Expr
  open PairExpr
  
  namespace uniSet3
    def theInternalWfmEncoding.eqWfm:
      uniDefList.theInternalWfmEncoding = theInternalWfm
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ isLeWfm isGeWfm
    
    def isUniversalNat
      {s3: Set3 Pair}
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨x, s3EqWfm⟩ := theInternalDefList.hasAllDefinable s3 isDef
      
      ⟨
        x,
        s3EqWfm ▸ theInternalWfmEncoding.eqWfm ▸ rfl
      ⟩
    
    def isUniversal
      {s3: Set3 Pair}
      (isDef: pairSalgebra.IsDefinable s3)
    :
      s3 ∈ uniSet3
    :=
      let ⟨x, s3EqWfm⟩ := theInternalDefList.hasAllDefinable s3 isDef
      
      ⟨
        fromNat x,
        s3EqWfm ▸ theInternalWfmEncoding.eqWfm ▸ rfl
      ⟩
    
    def isDefinable: pairSalgebra.IsDefinable uniSet3 := ⟨
      uniDefList.theExternalDefList,
      ⟨uniDefList.theSet, rfl⟩,
    ⟩
    
    def containsItself: uniSet3 ∈ uniSet3 := isUniversal isDefinable
    
    -- TODO:
    -- 0. finish this volume
    -- 1. make monotonic Exprs part of Salgebra
    -- 2. Make variables `T: Type*` instead of Nat
    -- 3. clean up the `HM` folder
    -- 4. Trisets
    
  end uniSet3
end Pair
