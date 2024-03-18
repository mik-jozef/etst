import UniSet3.NextDef


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insNthDefList (isNthDef: IsNthDefList p):
      Ins nthDefList p
    :=
      match p with
      | zero => isNthDef.elim
      | pair _ _ =>
        insWfmDef.toInsWfm
          -- Using a match expression would require manually proving
          -- termination. Curious that using `rec` is easier :D
          (isNthDef.rec
            (insUnL (insPair insZero insZero) _)
            (fun _isNthPredPair isNextPair insNthPredPair =>
              insUnR _
                (insUnDom
                  (insWfmDef.toInsWfm insNthPredPair)
                  (insPair
                    (insPair
                      (insZthMember
                        (insFree insBound nat501Neq500))
                      insZero)
                    (insCall
                      (insNextDef isNextPair)
                      (insFstMember
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)))))))
    
    def Inw.toIsNthDefList.ab a (inw: Inw nthDefList (pair a b)):
      IsNthDefList (pair a b)
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          let ⟨inwL, inwR⟩ := inwPairElim inw
          let eqL := inwZeroElim inwL
          let eqR := inwZeroElim inwR
          
          eqL ▸ eqR ▸ IsNthDefListPair.IsZeroA)
        (fun inw =>
          let ⟨bound, ⟨inwDomain, inwBody⟩⟩ := inwUnDomElim inw
          let ⟨inwA, inwB⟩ := inwPairElim inwBody
          
          match a with
          | zero => inwPairElim.nope inwA
          | pair aPred z =>
            let ⟨inwAPred, inwZ⟩ := inwPairElim inwA
            let ⟨bPred, ⟨inwFn, inwArg⟩⟩ := inwCallElim inwB
            
            let boundEq := inwBoundElim
              (inwZthFstElim inwAPred inwArg nat501Neq500 rfl)
            let zEq := inwZeroElim inwZ
            
            have: aPred.depth < (pair aPred z).depth := depthLtL _ _
            
            let isNthPred := ab aPred (boundEq.symm ▸ inwDomain)
            
            let isNextDef := Inw.toIsNextDef inwFn
            
            zEq ▸ IsNthDefListPair.IsPairA isNthPred isNextDef)
    termination_by Inw.toIsNthDefList.ab a inw => a.depth
    
    def Inw.toIsNthDefList (inw: Inw nthDefList p):
      IsNthDefList p
    :=
      match p with
      | zero =>
        (inwUnElim (inwWfm.toInwWfmDef inw)).elim
          inwPairElim.nope
          (fun inw =>
            inwPairElim.nope
              (inwUnDomElim inw).unwrap.property.inwBody)
      | pair a _ => toIsNthDefList.ab a inw
    
  end uniSet3
end Pair
