/-
  `Pair.uniSet3.isUniversal` is the main result of this volume.
  It states that any definable triset of pairs is in a sense
  "contained" in the triset `uniSet3`. See chapter 7 for more
  info.
  
  TODO summarize informally the proof strategy here.
-/

import UniSet3.Ch9_TheSet3


namespace Pair
  open Expr
  open PairExpr
  
  namespace uniSet3
    def theExternalDefList := uniDefList.theExternalDefList
    
    
    def decodeValuation
      (s3: Set3 Pair)
    :
      Valuation Pair
    :=
      fun n => Set3.pairCallJust s3 (fromNat n)
    
    def internalOfExternal
      (v: Valuation Pair)
    :
      Valuation Pair
    :=
      decodeValuation (v uniDefList.theSet)
    
    def theInternalWfmEncoding: Valuation Pair :=
      internalOfExternal uniDefList.theExternalWfm
    
    
    def insExternalToInsInternal
      (ins:
        Ins
          pairSalgebra
          theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Ins pairSalgebra theInternalDefList d x
    :=
      sorry
    
    def outExternalToOutInternal
      (out:
        Out
          pairSalgebra
          theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Out pairSalgebra theInternalDefList d x
    :=
      sorry
    
    
    def theInternalWfmEncoding.isGeWfm:
      theInternalWfm ⊑ theInternalWfmEncoding
    :=
      fun _ => {
        defLe :=
          fun _ insValInternal =>
            let ins := Ins.isComplete _ _ insValInternal
            (insInternalToInsExternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraAB
              fun outValInternal =>
                let out := Out.isComplete _ _ outValInternal
                (outInternalToOutExternal out).isSound
      }
    
    def theInternalWfmEncoding.isLeWfm:
      theInternalWfmEncoding ⊑ theInternalWfm
    :=
      fun _ => {
        defLe :=
          fun _ insValExternal =>
            let ins := Ins.isComplete _ _ insValExternal
            (insExternalToInsInternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraAB
              fun outValExternal =>
                let out := Out.isComplete _ _ outValExternal
                (outExternalToOutInternal out).isSound
      }
    
    def theInternalWfmEncoding.eqWfm:
      theInternalWfmEncoding = theInternalWfm
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ isLeWfm isGeWfm
    
    def isUniversal
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
    
    def isDefinable: pairSalgebra.IsDefinable uniSet3 := ⟨
      uniDefList.theExternalDefList,
      ⟨uniDefList.theSet, rfl⟩,
    ⟩
    
    def containsItself: uniSet3 ∈ uniSet3 :=
      let ⟨x, eq⟩ := isUniversal isDefinable
      ⟨fromNat x, eq⟩
    
    -- TODO:
    -- 0. finish this volume
    -- 1. make monotonic Exprs part of Salgebra
    -- 2. Make variables `T: Type*` instead of Nat
    -- 3. clean up the `HM` folder
    -- 4. Trisets
    
  end uniSet3
end Pair
