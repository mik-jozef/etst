import UniSet3.DefEncoding
import UniSet3.ShiftDefEncoding


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insLastExprBase (isLastExprBase: IsLastExprBase p):
      Ins lastExpr.base p
    :=
      match p with
      | zero => isLastExprBase.elim
      | pair zero _ => isLastExprBase.elim
      | pair (pair _ (pair _ _)) _ => isLastExprBase.elim
      | pair (pair _ zero) _ =>
        insWfmDef.toInsWfm
          (insUnDom
            (insExprEncoding isLastExprBase.isExprA)
            (insPair
              (insPair insBound insZero)
              (isLastExprBase.eq ▸ insBound)))
    
    def Inw.toIsLastExprBase (inw: Inw lastExpr.base p):
      IsLastExprBase p
    :=
      let ⟨_epxr, ⟨inwDomain, inwBody⟩⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair zero _ => inwPairElim.nope (inwPairElim inwBody).inwL
      | pair (pair _a _z) _b =>
        let ⟨inwPair, inw500B⟩ := inwPairElim inwBody
        let ⟨inw500A, inwZ⟩ := inwPairElim inwPair
        
        let eqA := inwBoundElim inw500A
        let eqB := inwBoundElim inw500B
        
        let eqZ := inwZeroElim inwZ
        
        eqA ▸ eqB.symm ▸ eqZ ▸ {
          eq := rfl
          isExprA := Inw.toIsExprEncoding inwDomain
        }
    
    
    def insLastExpr (isLastExprBase: IsLastExpr p):
      Ins lastExpr p
    :=
      match p with
      | zero => isLastExprBase.elim
      | pair zero b => isLastExprBase.nopeZeroDef
      | pair (pair aA aB) b =>
        
        insWfmDef.toInsWfm
          (match isLastExprBase with
          | IsLastExprPair.LengthOne isExprAA =>
            let isLastBase:
              IsLastExprBase (pair (pair aA zero) aA)
            := {
              eq := rfl
              isExprA := isExprAA
            }
            
            (insUnL
              (insLastExprBase isLastBase)
              _)
          | IsLastExprPair.LengthMore
            isExprAA
            isDefAB
            (isLast: IsLastExpr (pair _ _))
          =>
            (insUnR _
              (insUnDom
                (insLastExpr isLast)
                (insPair
                  (insPair
                    (insExprEncoding isExprAA)
                    (insZthMember (insFree insBound nat501Neq500)))
                  (insFstMember
                    (insFree insBound nat501Neq500))))))
    
    def arrayLengthA: Pair → Nat
    | zero => 0
    | pair a _ => a.arrayLength
    
    def Inw.toIsLastExpr (inw: Inw lastExpr p):
      IsLastExpr p
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw => (toIsLastExprBase inw).toIsLastExpr)
        (fun inw =>
          let ⟨lastTail, ⟨inwDomain, inwBody⟩⟩ := inwUnDomElim inw
          
          match h: p with
          | zero => inwPairElim.nope inwBody
          | pair zero _ => inwPairElim.nope (inwPairElim inwBody).inwL
          | pair (pair aA aB) b =>
            let ⟨inwDl, inwExpr⟩ := inwPairElim inwBody
            let ⟨inwDlHead, inwDlTail⟩ := inwPairElim inwDl
            
            let isExprAA := toIsExprEncoding inwDlHead
            
            let inw500 := inwZthFstElim inwDlTail inwExpr nat501Neq500 rfl
            let eqLastTail := inwBoundElim inw500
            
            have := arrayLength.ltTail aA aB
            
            let isLastTail: IsLastExpr (pair aB b) :=
              toIsLastExpr (eqLastTail.symm ▸ inwDomain)
            
            IsLastExprPair.LengthMore isExprAA isLastTail.isDefA isLastTail)
    termination_by Inw.toIsLastExpr inw => arrayLengthA p
    
    
    def insUpToLast (isUpToLast: IsUpToLast p):
      Ins upToLast p
    :=
      match p with
      | zero => isUpToLast.elim
      | pair _ _ =>
        insWfmDef.toInsWfm
          (isUpToLast.rec
            (fun isExpr =>
              insUnL
                (insPair
                  (insPair (insExprEncoding isExpr) insZero)
                  insZero)
                _)
            (fun
              isExprHead
              _isUpToLastTail
              insUpToLastTail
            =>
              insUnR _
                (insUnDom
                  (insWfmDef.toInsWfm insUpToLastTail)
                  (insUnDom
                    (insExprEncoding isExprHead)
                    (insPair
                      (insPair
                        insBound
                        (insZthMember
                          (insFree
                            (insFree insBound nat501Neq500)
                            nat502Neq500)))
                      (insPair
                        insBound
                        (insFstMember
                          (insFree
                            (insFree insBound nat501Neq500)
                            nat502Neq500))))))))
    
    def Inw.toIsUpToLast (inw: Inw upToLast p):
      IsUpToLast p
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          match p with
          | zero => inwPairElim.nope inw
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair (pair aA aB) b =>
            let ⟨inwL, inwR⟩ := inwPairElim inw
            let ⟨inwExprAA, inwZeroAB⟩ := inwPairElim inwL
            
            let eqZB := inwZeroElim inwR
            let eqZAB := inwZeroElim inwZeroAB
            let isExprAA := toIsExprEncoding inwExprAA
            
            eqZB ▸
            eqZAB ▸
            IsUpToLastPair.LengthOne isExprAA)
        (fun inw =>
          let ⟨upToLastTail, ⟨inwDomainUTL, inw⟩⟩ := inwUnDomElim inw
          let ⟨expr, ⟨inwDomainExpr, inw⟩⟩ := inwUnDomElim inw
          
          match p with
          | zero => inwPairElim.nope inw
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair (pair aA aB) (pair bA bB) =>
            let ⟨inwL, inwR⟩ := inwPairElim inw
            let ⟨inw501AA, inwZth⟩ := inwPairElim inwL
            let ⟨inw501BA, inwFst⟩ := inwPairElim inwR
            
            let eqAA := inwBoundElim inw501AA
            let eqBA := inwBoundElim inw501BA
            
            let eqUpToLastTail :=
              inwBoundElim
                (inwFreeElim
                  (inwZthFstElim inwZth inwFst nat502Neq500 rfl)
                  nat501Neq500)
            
            have := arrayLength.ltTail aA aB
            
            let isUTLB: IsUpToLast (pair aB bB) :=
              toIsUpToLast (eqUpToLastTail ▸ inwDomainUTL)
            
            let isExpr := eqBA ▸ toIsExprEncoding inwDomainExpr
            
            eqAA ▸
            eqBA ▸
            IsUpToLastPair.LengthMore isExpr isUTLB)
    termination_by Inw.toIsUpToLast inw => arrayLengthA p
    
    
    def insAppendBase (isDef: IsDefEncoding dl):
      Ins append.base (pair zero (pair dl dl))
    :=
      insWfmDef.toInsWfm
        (insPair
          insZero
          (insUnDom
            (insDefEncoding isDef)
            (insPair insBound insBound)))
    
    def Inw.toIsAppendOfBase (inw: Inw append.base p):
      IsAppend p
    :=
      match p with
      | zero => inwPairElim.nope (inwWfm.toInwWfmDef inw)
      | pair _a b =>
        let ⟨inwZ, inwUn⟩ := inwPairElim (inwWfm.toInwWfmDef inw)
        let ⟨_dl, ⟨inwDomain, inwBody⟩⟩ := inwUnDomElim inwUn
        
        match b with
        | zero => inwPairElim.nope inwBody
        | pair _bA _bB =>
          let ⟨inwBA, inwBB⟩ := inwPairElim inwBody
          
          let eqZ := inwZeroElim inwZ
          let eqBA := inwBoundElim inwBA
          let eqBB := inwBoundElim inwBB
          
          eqZ ▸
          eqBA ▸
          eqBB.symm ▸
          IsAppendABC.Base (toIsDefEncoding inwDomain)
    
    
    def insAppend (isAppend: IsAppend p):
      Ins append p
    :=
      match p with
      | zero => isAppend.elim
      | pair _a zero => isAppend.elim
      | pair _a (pair _b _c) =>
        insWfmDef.toInsWfm
          (isAppend.rec
            (fun isDef =>
              insUnL (insAppendBase isDef) _)
            (fun
              isUpTo
              isLastExpr
              isShiftDef
              _isAppend
              insAppendDef
            =>
              insUnR _
                (insUnDom
                  (insDefEncoding
                    isUpTo.isDefA)
                  (insUnDom
                    (insDefEncoding
                      isShiftDef.isDefB)
                    (insPair
                      (insFree
                        insBound
                        nat501Neq500)
                      (insPair
                        insBound
                        (insCallExpr
                          (insCallExpr
                            (insWfmDef.toInsWfm
                              insAppendDef)
                            (insCallExpr
                              (insUpToLast
                                isUpTo)
                              (insFree
                                (insFree
                                  (insFree
                                    (insFree
                                      insBound
                                      nat501Neq500)
                                    nat502Neq500)
                                  nat503Neq500)
                                nat504Neq500)))
                          (insCallExpr
                            (insCallExpr
                              (insShiftDefEncoding
                                isShiftDef)
                              (insCallExpr
                                (insLastExpr
                                  isLastExpr)
                                (insFree
                                  (insFree
                                    (insFree
                                      (insFree
                                        (insFree
                                          insBound
                                          nat501Neq500)
                                        nat502Neq500)
                                      nat503Neq500)
                                    nat504Neq500)
                                  nat505Neq500)))
                            (insFree
                              (insFree
                                insBound
                                nat502Neq501)
                              nat503Neq501)))))))))
    
    def Inw.toIsAppend (inw: Inw append p):
      IsAppend p
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        toIsAppendOfBase
        (fun inw =>
          let ⟨dlA, ⟨_inwDomainDlA, inw⟩⟩ := inwUnDomElim inw
          let ⟨dlB, ⟨_inwDomainDlB, inw⟩⟩ := inwUnDomElim inw
          
          match p with
          | zero => inwPairElim.nope inw
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair a (pair b c) =>
            let ⟨inw500A, inw⟩ := inwPairElim inw
            let ⟨inw501B, inw⟩ := inwPairElim inw
            
            let eqA := inwBoundElim (inwFreeElim inw500A nat501Neq500)
            let eqB := inwBoundElim inw501B
            
            let ⟨dlShifted, ⟨inwFnDlShifted, inwArgDlShifted⟩⟩ :=
              inwCallExprElim inw
            
            let inwCallDlDl :=
              inwCallElimBound inwArgDlShifted rfl nat503Neq501
            
            let ⟨dlALast, inwFnLast, inwArgLast⟩ :=
              inwCallExprElim inwCallDlDl
            
            let inwLast := inwCallElimBound inwArgLast rfl nat505Neq500
            
            let ⟨dlAUpToLast, ⟨inwFnAppend, inwArgAppend⟩⟩ :=
              inwCallExprElim inwFnDlShifted
            
            let inwUpToLast :=
              inwCallElimBound inwArgAppend rfl nat504Neq500
            
            match dlShifted with
            | zero =>
              (toIsShiftDefEncoding inwFnLast).elim
            | pair sA sB =>
              let isShift := toIsShiftDefEncoding inwFnLast
              
              have: dlAUpToLast.arrayLength < a.arrayLength :=
                eqA ▸ (toIsUpToLast inwUpToLast).arrayLengthLt
              
              let isAppendUTL:
                IsAppendABC dlAUpToLast (pair dlALast sB) c
              :=
                isShift.eqA ▸ toIsAppend inwFnAppend
              
              eqA ▸
              eqB ▸
              IsAppendABC.Step
                (toIsUpToLast inwUpToLast)
                (toIsLastExpr inwLast)
                (isShift.eqA ▸ isShift)
                isAppendUTL)
    termination_by Inw.toIsAppend inw => arrayLengthA p
    
  end uniSet3
end Pair
