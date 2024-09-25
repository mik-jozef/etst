-- The ninth section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S08_ShiftDefEncoding


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insLastExprBase (isLastExprBase: IsLastExprBase p):
      InsEdl lastExpr.base p
    :=
      match p with
      | zero => isLastExprBase.elim
      | pair zero _ => isLastExprBase.elim
      | pair (pair _ (pair _ _)) _ => isLastExprBase.elim
      | pair (pair _ zero) _ =>
        insWfmDefToIns
          (insUnDom
            (insExprEncoding isLastExprBase.isExprA)
            (insPair
              (insPair insBound insZero)
              (isLastExprBase.eq ▸ insBound)))
    
    def Inw.toIsLastExprBase (inw: InwEdl lastExpr.base p):
      IsLastExprBase p
    :=
      let ⟨_epxr, ⟨inwDomain, inwBody⟩⟩ :=
        inwUnDomElim (inwWfmToInwDef inw)
      
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
      InsEdl lastExpr p
    :=
      match p with
      | zero => isLastExprBase.elim
      | pair zero b => isLastExprBase.nopeZeroDef
      | pair (pair aA aB) b =>
        
        insWfmDefToIns
          (match isLastExprBase with
          | IsLastExprPair.LengthOne isExprAA =>
            let isLastBase:
              IsLastExprBase (pair (pair aA zero) aA)
            := {
              eq := rfl
              isExprA := isExprAA
            }
            
            (insUnL _
              (insLastExprBase isLastBase))
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
    
    def Inw.toIsLastExpr (inw: InwEdl lastExpr p):
      IsLastExpr p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw => (toIsLastExprBase inw).toIsLastExpr)
        (fun inw =>
          let ⟨lastTail, ⟨inwDomain, inwBody⟩⟩ := inwUnDomElim inw
          
          match p with
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
    termination_by arrayLengthA p
    
    
    def insUpToLast (isUpToLast: IsUpToLast p):
      InsEdl upToLast p
    :=
      match p with
      | zero => isUpToLast.elim
      | pair _ _ =>
        insWfmDefToIns
          (isUpToLast.rec
            (fun isExpr =>
              insUnL _
                (insPair
                  (insPair (insExprEncoding isExpr) insZero)
                  insZero))
            (fun
              isExprHead
              _isUpToLastTail
              insUpToLastTail
            =>
              insUnR _
                (insUnDom
                  (insWfmDefToIns insUpToLastTail)
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
    
    def Inw.toIsUpToLast (inw: InwEdl upToLast p):
      IsUpToLast p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
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
    termination_by arrayLengthA p
    
    
    def insArrayAppend (isArrayAppend: IsArrayAppend p):
      InsEdl arrayAppend p
    :=
      match p with
      | zero => isArrayAppend.elim
      | pair _ zero => isArrayAppend.elim
      | pair a (pair b c) =>
        insWfmDefToIns
          (match isArrayAppend with
          | IsArrayAppendABC.Base isDefB =>
            insUnL _
              (insPair
                insZero
                (insUnDom
                  (insFree
                    (insDefEncoding isDefB)
                    nat500NeqDefEncoding)
                  (insPair
                    insBound
                    insBound)))
          | IsArrayAppendABC.Step
            isUpToLast
            isLastExpr
            isAppendPrev
          =>
            have := isUpToLast.arrayLengthLt
            
            insUnR _
              (insUnDom
                (insDefEncoding
                  isUpToLast.isDefA)
                (insUnDom
                  (insDefEncoding
                    isAppendPrev.isDefB.right)
                  (insPair
                    (insFree
                      insBound
                      nat501Neq500)
                    (insPair
                      insBound
                      (insCallExpr
                        (insCallExpr
                          (insArrayAppend
                            isAppendPrev)
                          (insCallExpr
                            (insUpToLast
                              isUpToLast)
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    insBound
                                    nat501Neq500)
                                  nat502Neq500)
                                nat503Neq500)
                              nat504Neq500)))
                        (insPair
                          (insCallExpr
                            (insLastExpr
                              isLastExpr)
                            (insFree
                              (insFree
                                (insFree
                                  insBound
                                  nat501Neq500)
                                nat502Neq500)
                              nat503Neq500))
                          (insFree
                            insBound
                            nat502Neq501))))))))
    termination_by arrayLengthA p
    
    def Inw.toIsArrayAppend (inw: InwEdl arrayAppend p):
      IsArrayAppend p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw =>
          match p with
          | zero => inwPairElim.nope inw
          | pair a bc =>
            let ⟨inwZ, inw⟩ := inwPairElim inw
            let ⟨dl, ⟨inwDomain, inw⟩⟩ := inwUnDomElim inw
            
            match bc with
            | zero => inwPairElim.nope inw
            | pair b c =>
              let ⟨inwB, inwC⟩ := inwPairElim inw
              
              inwZeroElim inwZ ▸
              inwBoundElim inwB ▸
              (inwBoundElim inwC).symm ▸
              IsArrayAppendABC.Base
                (Inw.toIsDefEncoding inwDomain))
        (fun inw =>
          let ⟨dl500, ⟨_inwDomainA, inw⟩⟩ := inwUnDomElim inw
          let ⟨dl501, ⟨_inwDomainB, inw⟩⟩ := inwUnDomElim inw
          
          match p with
          | zero => inwPairElim.nope inw
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair a (pair b c) =>
            let ⟨inw500, inw⟩ := inwPairElim inw
            let ⟨inw501, inw⟩ := inwPairElim inw
            
            let eq500 := inwBoundElim (inwFreeElim inw500 nat501Neq500)
            let eq501 := inwBoundElim inw501
            
            let ⟨argOuter, ⟨inwFnOuter, inwArgOuter⟩⟩ :=
              inwCallExprElim inw
            
            match argOuter with
            | zero => inwPairElim.nope inwArgOuter
            | pair def500Last def501Alias =>
              let ⟨inwCallLast, inw501Alias⟩ := inwPairElim inwArgOuter
              
              let inwLast := inwCallElimBound inwCallLast rfl nat503Neq500
              let isLast := Inw.toIsLastExpr inwLast
              let eq501Alias :=
                inwBoundElim (inwFreeElim inw501Alias nat502Neq501)
              
              let ⟨argMidLeft, ⟨inwFnMidLeft, inwArgMidLeft⟩⟩ :=
                inwCallExprElim inwFnOuter
              
              let inwUtl := inwCallElimBound inwArgMidLeft rfl nat504Neq500
              let isUtl := Inw.toIsUpToLast inwUtl
              
              have: argMidLeft.arrayLength < a.arrayLength :=
                eq500 ▸ isUtl.arrayLengthLt
              
              let isAppendPrev :=
                eq501Alias ▸ toIsArrayAppend inwFnMidLeft
              
              eq500 ▸
              eq501 ▸
              IsArrayAppendABC.Step isUtl isLast isAppendPrev)
    termination_by arrayLengthA p
    
    
    def insArrayLength (isArrayLength: IsArrayLength p):
      InsEdl uniDefList.arrayLength p
    :=
      match p, isArrayLength with
      | zero, isArrL => isArrL.elim
      | pair zero zero, IsArrayLengthPair.Zero =>
        insWfmDefToIns
          (insUnL _ (insPair insZero insZero))
      | pair _ _, IsArrayLengthPair.Succ isArrLengthPrev head =>
        insWfmDefToIns
          (insUnR _
            (insArbUn _
              (insPair
                (insPair
                  insAny
                  insBound)
                (insPair
                  (insCallExpr
                    (insArrayLength
                      isArrLengthPrev)
                    (insFree
                      insBound
                      nat501Neq500))
                  insZero))))
    
    def Inw.toIsArrayLength (inw: InwEdl uniDefList.arrayLength p):
      IsArrayLength p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw =>
          match p with
          | zero => inwPairElim.nope inw
          | pair _ _ =>
            let ⟨inwL, inwR⟩ := inwPairElim inw
            
            inwZeroElim inwL ▸
            (inwZeroElim inwR).symm ▸
            IsArrayLengthPair.Zero)
        (fun inw =>
          let ⟨argTail, inw⟩ := inwArbUnElim inw
          
          match p with
          | zero => inwPairElim.nope inw
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair (pair head tail) (pair nPred z) =>
            let ⟨inwArr, inwLength⟩ := inwPairElim inw
            let ⟨_inwHead, inwTail⟩ := inwPairElim inwArr
            let ⟨inwPred, inwZ⟩ := inwPairElim inwLength
            
            let inwArrLengthPred :=
              (inwBoundElim inwTail).symm ▸
              inwCallElimBound inwPred rfl nat501Neq500
            
            have := arrayLength.ltTail head tail
            
            let isArrLengthPrev:
              -- Lean, why is this not inferred?
              IsArrayLength (pair tail nPred)
            :=
              toIsArrayLength inwArrLengthPred
            
            inwZeroElim inwZ ▸
            IsArrayLengthPair.Succ isArrLengthPrev head)
    termination_by arrayLengthA p
    
    
    def insAppend (isAppend: IsAppend p):
      InsEdl append p
    :=
      match p with
      | zero => isAppend.elim
      | pair _ zero => isAppend.elim
      | pair a (pair _b _c) =>
        insWfmDefToIns
          (insUnDom
            (insDefEncoding
              isAppend.isDefA)
            (insUnDom
              (insDefEncoding
                isAppend.isDefB)
              (insPair
                (insFree
                  insBound
                  nat501Neq500)
                (insPair
                  insBound
                  (insCallExpr
                    (insCallExpr
                      (insArrayAppend isAppend)
                      (insFree
                        (insFree
                          (insFree
                            insBound
                            nat501Neq500)
                          nat502Neq500)
                        nat503Neq500))
                    (insCallExpr
                      (insCallExpr
                        (insShiftDefEncoding
                          (IsShiftDefEncodingABC.fn
                            (fromNat.isNatEncoding _)
                            isAppend.isDefB))
                        (insCallExpr
                          (insArrayLength
                            (IsArrayLength.lengthIslength a))
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
                        nat503Neq501)))))))
    
    def Inw.toIsAppend (inw: InwEdl append p):
      IsAppend p
    :=
      let inw := inwWfmToInwDef inw
      let ⟨dlA, ⟨_inwDomainA, inw⟩⟩ := inwUnDomElim inw
      let ⟨_dlB, ⟨_inwDomainB, inw⟩⟩ := inwUnDomElim inw
      
      match p with
      | zero => inwPairElim.nope inw
      | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
      | pair _a (pair _b c) =>
        let ⟨inwA, inw⟩ := inwPairElim inw
        let ⟨inwB, inw⟩ := inwPairElim inw
        
        let eqA := inwBoundElim (inwFreeElim inwA nat501Neq500)
        let eqB := inwBoundElim inwB
        
        let ⟨argOuter, ⟨inwFnOuter, inwArgOuter⟩⟩ :=
          inwCallExprElim inw
        
        let ⟨_aliasDlA, ⟨inwFnMidLeft, inwArgMidLeft⟩⟩ :=
          inwCallExprElim inwFnOuter
        
        let aliasDlAEq :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim
                (inwFreeElim
                  inwArgMidLeft
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
        
        let inwShiftCall :=
          inwCallElimBound inwArgOuter rfl nat503Neq501
        
        let ⟨_n, ⟨inwShift, inwArrayLengthCall⟩⟩ :=
          inwCallExprElim inwShiftCall
        
        let inwArrayLength :=
          inwCallElimBound inwArrayLengthCall rfl nat505Neq500
        
        let isShift := toIsShiftDefEncoding inwShift
        let isLength := toIsArrayLength inwArrayLength
        
        let isAppend: IsArrayAppendABC dlA argOuter c :=
          aliasDlAEq ▸ toIsArrayAppend inwFnMidLeft
        
        eqA ▸
        eqB ▸
        IsAppendABC.fromArrayAppend isAppend isShift isLength
    
  end uniSet3
end Pair
