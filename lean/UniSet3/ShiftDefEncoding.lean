import UniSet3.ShiftExprEncoding
import UniSet3.DefEncoding


namespace Pair
  
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insIncrementExprs (isShiftEnc: IsIncrementExprs p):
      Ins shiftDefEncoding.incrementExprs p
    :=
      insWfmDef.toInsWfm
        (match p with
        | zero => isShiftEnc.elim
        | pair _ _ =>
          isShiftEnc.rec
            (insUnL (insPair insZero insZero) _)
            (fun isShiftExpr isIncRest insIncRest =>
              let ⟨isExprA, _isExprB⟩ := isShiftExpr.toIsExpr
              
              insUnR _
                (insUnDom
                  (insExprEncoding isExprA)
                  (insUnDom
                    (insDefEncoding isIncRest.toIsDef.isDef)
                    (insPair
                      (insPair
                        (insFree insBound nat501Neq500)
                        insBound)
                      (insPair
                        (insCall
                          (insShiftExprEncoding isShiftExpr)
                          (insFree
                            (insFree insBound nat501Neq500)
                            nat502Neq500))
                        (insCall
                          (insWfmDef.toInsWfm insIncRest)
                          (insFree insBound nat502Neq501))))))))
    
    def Inw.toIsIncrementExprs (w: Inw shiftDefEncoding.incrementExprs p):
      IsIncrementExprs p
    :=
      open IsIncrementExprsPair in
      (inwUnElim (inwWfm.toInwWfmDef w)).elim
        (fun inw =>
          match p with
          | zero => inwPairElim.nope inw
          | pair _ _ =>
            let ⟨l, r⟩ := inwPairElim inw
            
            (inwZeroElim l) ▸ (inwZeroElim r) ▸ EmptyDefList)
        (fun inw =>
          let ⟨expr, _inwDomainExpr, inwBody⟩ := inwUnDomElim inw
          let ⟨dl, _inwDomainDl, inwBody⟩ := inwUnDomElim inwBody
          
          match p with
          | zero => inwPairElim.nope inwBody
          | pair zero _ => inwPairElim.nope (inwPairElim inwBody).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inwBody).inwR
          | pair (pair aA aB) (pair bA bB) =>
            let ⟨inw500501, inwCallPair⟩ := inwPairElim inwBody
            
            let ⟨inw500, inw501⟩ := inwPairElim inw500501
            
            let eqAA := inwBoundElim (inwFreeElim inw500 nat501Neq500)
            let eqAB := inwBoundElim inw501
            
            let ⟨inwCallL, inwCallR⟩ := inwPairElim inwCallPair
            let ⟨exprAlias, ⟨inwFnExpr, inwArgExpr⟩⟩ := inwCallElim inwCallL
            let ⟨dlAlias, ⟨inwFnDl, inwArgDl⟩⟩ := inwCallElim inwCallR
            
            let eqExpr :=
              inwBoundElim
                (inwFreeElim
                  (inwFreeElim inwArgExpr nat502Neq500)
                  nat501Neq500)
            
            let eqDl :=
              inwBoundElim (inwFreeElim inwArgDl nat502Neq501)
            
            have:
              Nat.succ bB.arrayLength
                <
              Nat.succ (pair bA bB).arrayLength
            :=
              Nat.succ_lt_succ (arrayLength.ltTail _ _)
            
            (eqAA.trans eqExpr.symm) ▸
            (eqAB.trans eqDl.symm) ▸
            NonemptyDefList
              (Inw.toIsShiftExprEncoding inwFnExpr)
              (Inw.toIsIncrementExprs (inwFnDl)))
    termination_by Inw.toIsIncrementExprs w => p.arrayLength
    
    
    def insShiftDefEncoding (isShiftDef: IsShiftDefEncoding p):
      Ins shiftDefEncoding p
    :=
      match p with
      | zero => isShiftDef.elim
      | pair _a zero => isShiftDef.elim
      | pair _a (pair _b zero) => isShiftDef.elim
      | pair _a (pair _b (pair _cA _cB)) =>
        insWfmDef.toInsWfm
          (insUnDom
            (insExprEncoding isShiftDef.isExprA)
            (insUnDom
              (insDefEncoding isShiftDef.isDefB)
              (insPair
                (insFree insBound nat501Neq500)
                (insPair
                  insBound
                  (insPair
                    (insFree (isShiftDef.eqA ▸ insBound) nat501Neq500)
                    (insCall
                      (insIncrementExprs isShiftDef.isShiftedB)
                      (insFree insBound nat502Neq501)))))))
    
    def Inw.toIsShiftDefEncoding (inw: Inw shiftDefEncoding p):
      IsShiftDefEncoding p
    :=
      let ⟨_expr, inwDomainExpr, inwBody⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      let ⟨_dl, inwDomainDl, inwBody⟩ := inwUnDomElim inwBody
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair _a zero => inwPairElim.nope (inwPairElim inwBody).inwR
      | pair _a (pair _bA zero) =>
        inwPairElim.nope (inwPairElim (inwPairElim inwBody).inwR).inwR
      | pair _a (pair _b (pair _cA _cB)) =>
        let ⟨inw500A, inw⟩ := inwPairElim inwBody
        let ⟨inw501, inw⟩ := inwPairElim inw
        let ⟨inw501CA, inw⟩ := inwPairElim inw
        
        let eqA :=
          inwBoundElim (inwFreeElim inw500A nat501Neq500)
        
        let eqDl := inwBoundElim inw501
        
        let eqCA :=
          inwBoundElim (inwFreeElim inw501CA nat501Neq500)
        
        let ⟨_dlAlias, ⟨inwFn, inwArg⟩⟩ := inwCallElim inw
        
        let eqDlAlias := inwBoundElim (inwFreeElim inwArg nat502Neq501)
        
        {
          isExprA := eqA ▸ Inw.toIsExprEncoding inwDomainExpr
          isDefB := eqDl ▸ Inw.toIsDefEncoding inwDomainDl
          eqA := eqA.trans eqCA.symm
          isShiftedB := eqDl ▸ eqDlAlias ▸ Inw.toIsIncrementExprs inwFn
        }
    
  end uniSet3
end Pair
