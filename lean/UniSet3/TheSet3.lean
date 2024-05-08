import UniSet3.DefListToEncoding

def Set3.pairCall (fn arg: Set3 Pair): Set3 Pair := {
  defMem := fun p => ∃ (a: arg.defMem), fn.defMem (Pair.pair a p)
  posMem := fun p => ∃ (a: arg.posMem), fn.posMem (Pair.pair a p)
  defLePos :=
    fun _p pInDef =>
      let ⟨⟨a, aInArgDef⟩, apInFnDef⟩ := pInDef
      
      ⟨
        ⟨a, (arg.defLePos aInArgDef)⟩,
        fn.defLePos apInFnDef
      ⟩
}

def Set3.pairCallJust
  (fn: Set3 Pair)
  (arg: Pair)
:=
  Set3.pairCall fn (Set3.just arg)


noncomputable def theDefListExternal.getDef
  (n: Nat)
:
  Expr pairSignature
:=
  Pair.encodingToExpr
    (Pair.uniSet3.IsTheDefListExprPair.getNthExpr n).expr

noncomputable def theDefListExternal:
  DefList pairSignature
:= {
  getDef := theDefListExternal.getDef
}


namespace Pair
  noncomputable def uniSet3 := uniDefList.wfModel uniDefList.theSet
  
  namespace uniSet3
    def isUniversal
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨dl, x, sEq⟩ := isDef
      
      let ⟨finBounds, _⟩ := dl.isFinBounded
      
      let ⟨dlSliceEnd, gtBounds⟩ := finBounds.boundsFinite x
      
      let dlSliceEncoding :=
        defListToEncoding dl.toDefList 0 dlSliceEnd
      
      sorry
  end uniSet3
end Pair
