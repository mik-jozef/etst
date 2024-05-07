import UniSet3.Append
import UniSet3.NthDefList


namespace Pair
  
  protected def depthBA: Pair → Nat
  | zero => 0
  | pair _ zero => 0
  | pair _ (pair bA _) => bA.depth
  
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
                    (insCallExpr
                      (insCallExpr
                        (insAppend
                          isAppend)
                        (insCallExpr
                          (insWfmDef.toInsWfm
                            insSoFar)
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat501Neq500)
                              nat502Neq500)
                            nat503Neq500)))
                      (insCallExpr
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
            
            let ⟨nthDl, inwFnNthDl, inwArgNthDl⟩ := inwCallExprElim inwDl
            let ⟨dlSoFar, inwFnDlSoFar, inwArgDlSoFar⟩ :=
              inwCallExprElim inwFnNthDl
            
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
    
    
    def insDefListToSet (isDefToSet: IsDefListToSet p):
      Ins defListToSet p
    :=
      insWfmDef.toInsWfm
        (match p with
        | zero => isDefToSet.elim
        | pair _ zero => isDefToSet.elim
        | pair zero (pair _ _) => isDefToSet.defNonempty
        
        | pair (pair dlHead dlTail) (pair zero expr) =>
          let eq: dlHead = expr :=
            Option.noConfusion isDefToSet.eq id
          
          eq ▸ insUnDom
            (insExprEncoding isDefToSet.isDef.left)
            (insUnDom
              (insDefEncoding
                isDefToSet.isDef.right)
              (insUnL
                (insPair
                  (insPair
                    (insFree
                      insBound
                      nat501Neq500)
                    insBound)
                  (insPair
                    insZero
                    (insFree
                      insBound
                      nat501Neq500)))
                _))
        
        | pair (pair dlHead dlTail) (pair (pair iPred z) expr) =>
          let atTailEq:
            dlTail.arrayAt iPred.depth = some expr
          :=
            arrayAt.tailEq
              (isDefToSet.isNat.right ▸
              depth.nat.eqSuccDepthPred isDefToSet.isNat ▸
              isDefToSet.eq)
          
          isDefToSet.isNat.right ▸
          insUnDom
            (insExprEncoding
              isDefToSet.isDef.left)
            (insUnDom
              (insDefEncoding
                isDefToSet.isDef.right)
              (insUnR _
                (insUnDom
                  (insNatEncoding
                    isDefToSet.isNat.left)
                  (insPair
                    (insPair
                      (insFree
                        (insFree
                          insBound
                          nat501Neq500)
                        nat502Neq500)
                      (insFree
                        insBound
                        nat502Neq501))
                    (insPair
                      (insPair
                        insBound
                        insZero)
                      (insCallExpr
                        (insCallExpr
                          (insDefListToSet {
                            isDef := isDefToSet.isDef.right
                            isNat := isDefToSet.isNat.left
                            eq := atTailEq
                          })
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat502Neq501)
                              nat503Neq501)
                            nat504Neq501))
                        (insFree
                          insBound
                          nat503Neq502))))))))
    
    def Inw.toIsDefListToSet (inw: Inw defListToSet p):
      IsDefListToSet p
    :=
      let inw := inwWfm.toInwWfmDef inw
      
      let ⟨head, ⟨inwDomainHead, inw⟩⟩ := inwUnDomElim inw
      let ⟨tail, ⟨inwDomainTail, inw⟩⟩ := inwUnDomElim inw
      
      (inwUnElim inw).elim
        (fun inw =>
          match p with
          | zero => inwPairElim.nope inw
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair (pair head tail) (pair n expr) =>
            let ⟨inw500501, inwZero500⟩ := inwPairElim inw
            let ⟨inw500Head, inw501⟩ := inwPairElim inw500501
            let ⟨inwZero, inw500Expr⟩ := inwPairElim inwZero500
            
            let eqHead := inwBoundElim
              (inwFreeElim inw500Head nat501Neq500)
            
            let eqExpr := inwBoundElim
              (inwFreeElim inw500Expr nat501Neq500)
            
            let eqTail := inwBoundElim inw501
            let eqZero := inwZeroElim inwZero
            
            let isHeadExpr :=
              toIsExprEncoding
                (inwFreeElim inwDomainHead nat500NeqExprEncoding)
            
            let isTailDef :=
              toIsDefEncoding
                (inwFreeElim inwDomainTail nat501NeqDefEncoding)
            
            eqHead ▸
            eqTail ▸
            eqZero ▸
            eqExpr.symm ▸
            {
              isDef := And.intro isHeadExpr isTailDef
              isNat := trivial
              eq := rfl
            })
        (fun inw =>
          let ⟨n, ⟨inwDomainN, inw⟩⟩ := inwUnDomElim inw
          
          match p with
          | zero => inwPairElim.nope inw
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair (pair head tail) (pair zero expr) =>
            inwPairElim.nope (inwPairElim (inwPairElim inw).inwR).inwL
          | pair (pair head tail) (pair (pair nAlias z) expr) =>
            let ⟨inwDl, inwAt⟩ := inwPairElim inw
            let ⟨inwHead, inwTail⟩ := inwPairElim inwDl
            let ⟨inwSucc, inw⟩ := inwPairElim inwAt
            let ⟨inwN, inwZ⟩ := inwPairElim inwSucc
            
            let eqHead :=
              inwBoundElim
                (inwFreeElim
                  (inwFreeElim
                    inwHead
                    nat502Neq500)
                  nat501Neq500)
            
            let eqTail := inwBoundElim (inwFreeElim inwTail nat502Neq501)
            
            let eqN := inwBoundElim inwN
            let eqZ := inwZeroElim inwZ
            
            let isHeadExpr :=
              toIsExprEncoding
                (inwFreeElim inwDomainHead nat500NeqExprEncoding)
            
            let isTailDef :=
              toIsDefEncoding
                (inwFreeElim inwDomainTail nat501NeqDefEncoding)
            
            let isNatN := toIsNatEncoding inwDomainN
            
            let inw := inwCallElimBound inw rfl nat503Neq502
            let inw := inwCallElimBound inw rfl nat504Neq501
            
            have:
              n.depth < (pair nAlias z).depth
            :=
              eqN ▸ eqZ ▸ depthLtL _ _
            
            eqHead ▸
            eqTail ▸
            eqZ ▸
            eqN ▸ 
            {
              isDef := And.intro isHeadExpr isTailDef
              isNat := And.intro isNatN rfl
              eq :=
                depth.nat.eqSuccDepthPred (And.intro isNatN rfl) ▸
                arrayAt.consEq (toIsDefListToSet inw).eq _
            })
    termination_by Inw.toIsDefListToSet inw => p.depthBA
    
  end uniSet3
end Pair