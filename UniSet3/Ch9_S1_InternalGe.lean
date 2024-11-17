/-
  The first section of Chapter 9. See the zeroth section.
-/

import UniSet3.Ch9_S0_InternalLe


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    
    def insExternalToInsInternal
      (ins:
        Ins
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
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
          uniDefList.theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Out pairSalgebra theInternalDefList d x
    :=
      sorry
    
    
    def theInternalWfmEncoding.isLeWfm:
      uniDefList.theInternalWfmEncoding ⊑ theInternalWfm
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
    
  end uniSet3
end Pair
