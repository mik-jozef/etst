import UniSet3.Append
import UniSet3.NthDefList


namespace Pair
  
  protected def depthA: Pair → Nat
  | zero => 0
  | pair a _ => a.depth
  
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insEnumUpTo (isEnumUpTo: IsEnumUpTo p):
      Ins enumUpTo p
    :=
      match p with
      | zero => isEnumUpTo.elim
      | pair _ _ =>
        insWfmDef.toInsWfm
          (isEnumUpTo.rec
            (insUnL (insPair insZero insZero) _)
            (fun isEnumUpToSoFar isNthDl isAppend insSoFar =>
              (insUnR _
                (insUnDom
                  (insNatEncoding
                    isEnumUpToSoFar.isNatA)
                  (insPair
                    (insPair
                      insBound
                      insZero)
                    (insCall
                      (insCall
                        (insAppend
                          isAppend)
                        (insCall
                          (insWfmDef.toInsWfm
                            insSoFar)
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat501Neq500)
                              nat502Neq500)
                            nat503Neq500)))
                      (insCall
                        (insNthDefList
                          isNthDl)
                        (insFree
                          (insFree
                            insBound
                            nat501Neq500)
                          nat502Neq500))))))))
    
    def Inw.toIsEnumUpTo (inw: Inw enumUpTo p):
      IsEnumUpTo p
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          match p with
          | zero => inwPairElim.nope inw
          | pair a b =>
            let ⟨inwL, inwR⟩ := inwPairElim inw
            
            (inwZeroElim inwL) ▸
            (inwZeroElim inwR) ▸
            IsEnumUpToPair.Base)
        (fun inw =>
          let ⟨n, ⟨_inwDomain, inw⟩⟩ := inwUnDomElim inw
          match p with
          | zero => inwPairElim.nope inw
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair (pair aPred z) b =>
            let ⟨inwN, inwDl⟩ := inwPairElim inw
            let ⟨inwAPred, inwZ⟩ := inwPairElim inwN
            
            let eqAPred := inwBoundElim inwAPred
            let eqZ := inwZeroElim inwZ
            
            let ⟨nthDl, inwFnNthDl, inwArgNthDl⟩ := inwCallElim inwDl
            let ⟨dlSoFar, inwFnDlSoFar, inwArgDlSoFar⟩ :=
              inwCallElim inwFnNthDl
            
            let isAppend := toIsAppend inwFnDlSoFar
            
            let inwNth := inwCallElimBound inwArgNthDl rfl nat502Neq500
            let isNth := toIsNthDefList inwNth
            
            have: n.depth < (pair aPred z).depth :=
              eqAPred ▸ eqZ ▸ depthLtL _ _
            
            let inwUpTo := inwCallElimBound inwArgDlSoFar rfl nat503Neq500
            let isUpTo := toIsEnumUpTo inwUpTo
            
            eqZ ▸
            eqAPred ▸
            IsEnumUpToPair.Step isUpTo isNth isAppend)
    termination_by Inw.toIsEnumUpTo inw => p.depthA
    
  end uniSet3
end Pair
