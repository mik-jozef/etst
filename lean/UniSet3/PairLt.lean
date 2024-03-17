import UniSet3.PairOfDepth


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insSameDepth (isSameDepth: IsSameDepth p):
      Ins sameDepth p
    :=
      match p with
      | zero => isSameDepth.elim
      | pair a b =>
        let isPodB: IsPairOfDepth (pair (fromNat a.depth) b) := {
          isNat := fromNat.isNatEncoding _
          eqDepth := (fromNat.depthEq _).trans isSameDepth
        }
        
        insWfmDef.toInsWfm
          (insUnDom
            (insNatEncoding (fromNat.isNatEncoding a.depth))
            (insPair
              (insCall
                (insPairOfDepth (IsPairOfDepth.ofDepth a))
                (insFree insBound nat501Neq500))
              (insCall
                (insPairOfDepth isPodB)
                (insFree insBound nat501Neq500))))
    
    def Inw.toIsSameDepth (inw: Inw sameDepth p):
      IsSameDepth p
    :=
      let ⟨depthEncoding, ⟨_inwDomain, inwBody⟩⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair a b =>
        let ⟨l, r⟩ := inwPairElim inwBody
        
        let ⟨_argL, ⟨inwFnL, inwArgL⟩⟩ := inwCallElim l
        let ⟨_argR, ⟨inwFnR, inwArgR⟩⟩ := inwCallElim r
        
        let argEqL := inwBoundElim (inwFreeElim inwArgL nat501Neq500)
        let argEqR := inwBoundElim (inwFreeElim inwArgR nat501Neq500)
        
        let isPodA: IsPairOfDepth (pair depthEncoding a) :=
          Inw.toIsPairOfDepth
            (inwFreeElim (argEqL ▸ inwFnL) nat501NeqPairOfDepth)
        
        let isPodB: IsPairOfDepth (pair depthEncoding b) :=
          Inw.toIsPairOfDepth
            (inwFreeElim (argEqR ▸ inwFnR) nat501NeqPairOfDepth)
        
        isPodA.eqDepth.symm.trans isPodB.eqDepth
  end uniSet3
end Pair
