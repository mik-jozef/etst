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
  
  def nthSet3 (n: Nat): Set3 Pair :=
    uniSet3.pairCallJust (fromNat n)
  
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
      ∃ n: Nat, nthSet3 n = s3
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
    
  end uniSet3
end Pair
