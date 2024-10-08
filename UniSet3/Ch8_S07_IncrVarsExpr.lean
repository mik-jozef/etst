-- The seventh section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S06_NthDefList


namespace Pair
  
  protected def depthB: Pair → Nat
  | zero => 0
  | pair _ b => b.depth
  
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insIncrVarsExpr (isShiftEnc: IsIncrVarsExpr p):
      InsEdl incrVarsExpr p
    :=
      match p with
      | zero => isShiftEnc.elim
      | pair a b =>
        insWfmDefToIns
          (match isShiftEnc with
          | IsIncrVarsExprPair.IsVar isNatX =>
            let inList:
              Expr.var incrVarsExpr.var ∈ incrVarsExpr.exprList
            :=
              by unfold incrVarsExpr.exprList; simp
            
            insFinUn
              inList
              (insWfmDefToIns
                (insUnDom
                  (insNatEncoding isNatX)
                  (insPair
                    (insPair insZero insBound)
                    (insPair insZero (insPair insBound insZero)))))
          
          | IsIncrVarsExprPair.IsZero =>
            let inList:
              incrVarsExpr.opZero ∈ incrVarsExpr.exprList
            :=
              by unfold incrVarsExpr.exprList; simp
            
            insFinUn
              inList
              (insPair insExprEncoding.zero insExprEncoding.zero)
          
          | IsIncrVarsExprPair.IsBin isBin isShiftExprA isShiftExprB =>
            let inList:
              incrVarsExpr.binExpr ∈ incrVarsExpr.exprList
            :=
              by unfold incrVarsExpr.exprList; simp
            
            insFinUn
              inList
              (insUnDom
                (insExprEncoding.binary isBin)
                (insUnDom
                  (insExprEncoding isShiftExprA.isExprA)
                  (insUnDom
                    (insExprEncoding isShiftExprB.isExprA)
                    (insPair
                      (insPair
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)
                        (insPair
                          (insFree insBound nat502Neq501)
                          insBound))
                      (insPair
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)
                        (insPair
                          (insCallExpr
                            (insIncrVarsExpr isShiftExprA)
                            (insFree
                              (insFree insBound nat502Neq501)
                              nat503Neq501))
                          (insCallExpr
                            (insIncrVarsExpr isShiftExprB)
                            (insFree insBound nat503Neq502))))))))
          
          | IsIncrVarsExprPair.IsCpl isShift =>
            let inList:
              incrVarsExpr.cplExpr ∈ incrVarsExpr.exprList
            :=
              by unfold incrVarsExpr.exprList; simp
            
            insFinUn
              inList
              (insUnDom
                (insExprEncoding isShift.isExprA)
                (insPair
                  (insPair (insNatExpr _ _ _) insBound)
                  (insPair
                    (insNatExpr _ _ _)
                    (insCallExpr
                      (insIncrVarsExpr isShift)
                      (insFree insBound nat503Neq501)))))
          
          | IsIncrVarsExprPair.IsQuantifier isQ isNat isShift =>
            let inList:
              incrVarsExpr.quantifierExpr ∈ incrVarsExpr.exprList
            :=
              by unfold incrVarsExpr.exprList; simp
            
            insFinUn
              inList
              (insUnDom
                (insExprEncoding.quantifier isQ)
                (insUnDom
                  (insExprEncoding isShift.isExprA)
                  (insUnDom
                    (insNatEncoding isNat)
                    (insPair
                      (insPair
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)
                        (insPair
                          insBound
                          (insFree insBound nat502Neq501)))
                      (insPair
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)
                        (insPair
                          (insPair
                            insBound
                            insZero)
                          (insCallExpr
                            (insIncrVarsExpr isShift)
                            (insFree
                              (insFree insBound nat502Neq501)
                              nat503Neq501)))))))))
    
    def Inw.toIsIncrVarsExpr (w: InwEdl incrVarsExpr p):
      IsIncrVarsExpr p
    :=
      inwFinUnElim (inwWfmToInwDef w)
        (fun inw =>
          let ⟨bound, ⟨inwDomain, inwBody⟩⟩ :=
            inwUnDomElim (inwWfmToInwDef inw)
          
          match p with
          | Pair.zero => inwPairElim.nope inwBody
          
          | Pair.pair zero _ =>
            inwPairElim.nope (inwPairElim inwBody).inwL
          
          | Pair.pair _ zero =>
            inwPairElim.nope (inwPairElim inwBody).inwR
          
          | Pair.pair (pair zA xA) (pair zB zero) =>
            inwPairElim.nope
              (inwPairElim (inwPairElim inwBody).inwR).inwR
          
          | Pair.pair (pair zA xA) (pair zB (pair xBA xBB)) =>
            let ⟨inwA, inwB⟩ := inwPairElim inwBody
            let ⟨inwZA, inwXA⟩ := inwPairElim inwA
            let ⟨inwZB, inwXB⟩ := inwPairElim inwB
            let ⟨inwXBA, inwXBB⟩ := inwPairElim inwXB
            
            let eqZA := inwZeroElim inwZA
            let eqZB := inwZeroElim inwZB
            let eqXA := inwBoundElim inwXA
            let eqXBA := inwBoundElim inwXBA
            let eqXBB := inwZeroElim inwXBB
            
            eqZA ▸
            eqZB.symm ▸
            eqXA ▸
            eqXBA.symm ▸
            eqXBB.symm ▸
            IsIncrVarsExprPair.IsVar (Inw.toIsNatEncoding inwDomain))
        (fun inw =>
          match p with
          | Pair.zero => inwPairElim.nope inw
          | Pair.pair a b =>
            let ⟨inwL, inwR⟩ := inwPairElim inw
            
            Inw.toIsExprEncodinng.zero inwL ▸
            Inw.toIsExprEncodinng.zero inwR ▸
            IsIncrVarsExprPair.IsZero)
        (fun inw =>
          let ⟨boundBin, ⟨inwDomain500, inwBody⟩⟩ :=
            inwUnDomElim inw
          let ⟨boundA, ⟨_inwDomain501, inwBody⟩⟩ :=
            inwUnDomElim inwBody
          let ⟨boundB, ⟨_inwDomain502, inwBody⟩⟩ :=
            inwUnDomElim inwBody
          
          match p with
          | Pair.zero => inwPairElim.nope inwBody
          
          | Pair.pair Pair.zero _ =>
            inwPairElim.nope (inwPairElim inwBody).inwL
          
          | Pair.pair _ Pair.zero =>
            inwPairElim.nope (inwPairElim inwBody).inwR
          
          | Pair.pair (pair aA aB) (pair bA bB) =>
            let ⟨inwL, inwR⟩ := inwPairElim inwBody
            let ⟨inwBinA, inwBoundPair⟩ := inwPairElim inwL
            let ⟨inwBinB, inwPairCall⟩ := inwPairElim inwR
            
            let eqAA :=
              inwBoundElim
                (inwFreeElim
                  (inwFreeElim inwBinA nat502Neq500)
                  nat501Neq500)
            
            let eqBA :=
              inwBoundElim
                (inwFreeElim
                  (inwFreeElim inwBinB nat502Neq500)
                  nat501Neq500)
            
            match aB, bB with
            | zero, _ => inwPairElim.nope inwBoundPair
            | _, zero => inwPairElim.nope inwPairCall
            | pair aBA aBB, pair bBA bBB =>
              let isBinBound := Inw.toIsExprEncoding.binary inwDomain500
              
              let ⟨inwABA, inwABB⟩ := inwPairElim inwBoundPair
              let eqABA := inwBoundElim (inwFreeElim inwABA nat502Neq501)
              let eqABB := inwBoundElim inwABB
              
              let ⟨inwCallBBA, inwCallBBB⟩ := inwPairElim inwPairCall
              
              let ⟨bBAPred, ⟨inwShiftA, inw501⟩⟩ := inwCallExprElim inwCallBBA
              let ⟨bBBPred, ⟨inwShiftB, inw502⟩⟩ := inwCallExprElim inwCallBBB
              
              let eqBBAPred :=
                inwBoundElim
                  (inwFreeElim
                    (inwFreeElim inw501 nat503Neq501)
                    nat502Neq501)
              
              let eqBBBPred :=
                inwBoundElim (inwFreeElim inw502 nat503Neq502)
              
              have:
                bBA.depth < (pair bA (pair bBA bBB)).depth
              :=
                (Pair.depthLtL _ _).trans (Pair.depthLtR _ _)
              
              let isShiftBA := toIsIncrVarsExpr inwShiftA
              
              have:
                (pair bBBPred bBB).depthB
                  <
                (pair (pair aA (pair aBA aBB)) (pair bA (pair bBA bBB))).depthB
              :=
                (Pair.depthLtR _ _).trans (Pair.depthLtR _ _)
              
              let isShiftBB := toIsIncrVarsExpr inwShiftB
              
              eqAA ▸
              eqBA.symm ▸
              eqABA ▸
              eqBBAPred ▸
              eqABB ▸
              eqBBBPred ▸
              IsIncrVarsExprPair.IsBin isBinBound isShiftBA isShiftBB)
        (fun inw =>
          let ⟨expr, ⟨_inwExpr, inwBody⟩⟩ := inwUnDomElim inw
          
          match p with
          | zero => inwPairElim.nope inwBody
          | pair zero _ => inwPairElim.nope (inwPairElim inwBody).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inwBody).inwR
          | pair (pair aA aB) (pair bA bB) =>
            let ⟨inwA, inwB⟩ := inwPairElim inwBody
            let ⟨inwNat5A, inwAB⟩ := inwPairElim inwA
            let ⟨inwNat5B, inwBB⟩ := inwPairElim inwB
            
            let eqAA := inwNatExprElim inwNat5A
            let eqBA := inwNatExprElim inwNat5B
            let eqAB := inwBoundElim inwAB
            
            let ⟨exprAlias, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim inwBB
            
            let eqExpr := inwBoundElim (inwFreeElim inwArg nat503Neq501)
            
            have: bB.depth < (pair bA bB).depth := depthLtR _ _
            
            eqAA ▸
            (eqAB.trans eqExpr.symm) ▸
            eqBA ▸
            IsIncrVarsExprPair.IsCpl (toIsIncrVarsExpr inwFn))
        (fun inw =>
          let ⟨q, ⟨inwQ, inwBody⟩⟩ := inwUnDomElim inw
          let ⟨expr, ⟨_inwExpr, inwBody⟩⟩ := inwUnDomElim inwBody
          let ⟨nat, ⟨inwNat, inwBody⟩⟩ := inwUnDomElim inwBody
          
          match p with
          | zero => inwPairElim.nope inwBody
          | pair zero _ => inwPairElim.nope (inwPairElim inwBody).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inwBody).inwR
          | pair (pair aA aB) (pair bA bB) =>
            let ⟨inwL, inwR⟩ := inwPairElim inwBody
            let ⟨inwQA, inwAB⟩ := inwPairElim inwL
            let ⟨inwQB, inwBB⟩ := inwPairElim inwR
            
            match aB, bB with
            | zero, _ => inwPairElim.nope inwAB
            | _, zero => inwPairElim.nope inwBB
            | pair aBA aBB, pair zero bBB =>
              inwPairElim.nope (inwPairElim inwBB).inwL
            | pair aBA aBB, pair (pair bBAA bBAB) bBB =>
              let isQ := Inw.toIsExprEncoding.quantifier inwQ
              let isNat := Inw.toIsNatEncoding inwNat
              
              let eqAA :=
                inwBoundElim
                  (inwFreeElim
                    (inwFreeElim inwQA nat502Neq500)
                    nat501Neq500)
              
              let eqAB :=
                inwBoundElim
                  (inwFreeElim
                    (inwFreeElim inwQB nat502Neq500)
                    nat501Neq500)
              
              let ⟨inwABA, inwABB⟩ := inwPairElim inwAB
              let ⟨inwBBA, inwCallBBB⟩ := inwPairElim inwBB
              
              let ⟨inwBBAA, innwBBAB⟩ := inwPairElim inwBBA
              
              let ⟨exprAlias, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim inwCallBBB
              
              let eqABA := inwBoundElim inwABA
              let eqBBAA := inwBoundElim inwBBAA
              let eqBBAB := inwZeroElim innwBBAB
              
              let eqExprAlias :=
                inwBoundElim
                  (inwFreeElim
                    (inwFreeElim inwArg nat503Neq501)
                    nat502Neq501)
              
              let eqABB :=
                inwBoundElim (inwFreeElim inwABB nat502Neq501)
              
              have:
                bBB.depth < (pair bA (pair (pair bBAA bBAB) bBB)).depth
              :=
                (depthLtR _ _).trans (depthLtR _ _)
              
              let isShift := toIsIncrVarsExpr inwFn
              
              eqAA ▸
              eqAB.symm ▸
              eqABA ▸
              eqBBAA.symm ▸
              eqBBAB ▸
              (eqABB.trans eqExprAlias.symm) ▸
              IsIncrVarsExprPair.IsQuantifier isQ isNat isShift)
    termination_by p.depthB
    
  end uniSet3
end Pair
