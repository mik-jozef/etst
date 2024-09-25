-- The eighth section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S07_IncrVarsExpr

namespace Pair
  
  protected def depthA: Pair → Nat
  | zero => 0
  | pair a _ => a.depth
  
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insIncrVarsDefEncoding (isShiftEnc: IsIncrVarsDefEncoding p):
      InsEdl incrVarsDefEncoding p
    :=
      insWfmDefToIns
        (match p with
        | zero => isShiftEnc.elim
        | pair _ _ =>
          isShiftEnc.rec
            (insUnL _ (insPair insZero insZero))
            (fun isShiftExpr isIncRest insIncRest =>
              insUnR _
                (insUnDom
                  (insExprEncoding isShiftExpr.isExprA)
                  (insUnDom
                    (insDefEncoding isIncRest.isDefA)
                    (insPair
                      (insPair
                        (insFree insBound nat501Neq500)
                        insBound)
                      (insPair
                        (insCallExpr
                          (insIncrVarsExpr isShiftExpr)
                          (insFree
                            (insFree insBound nat501Neq500)
                            nat502Neq500))
                        (insCallExpr
                          (insWfmDefToIns insIncRest)
                          (insFree insBound nat502Neq501))))))))
    
    def Inw.toIsIncrVarsDefEncoding (w: InwEdl incrVarsDefEncoding p):
      IsIncrVarsDefEncoding p
    :=
      open IsIncrVarsDefEncodingPair in
      (inwUnElim (inwWfmToInwDef w)).elim
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
            let ⟨exprAlias, ⟨inwFnExpr, inwArgExpr⟩⟩ := inwCallExprElim inwCallL
            let ⟨dlAlias, ⟨inwFnDl, inwArgDl⟩⟩ := inwCallExprElim inwCallR
            
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
              (Inw.toIsIncrVarsExpr inwFnExpr)
              (Inw.toIsIncrVarsDefEncoding (inwFnDl)))
    termination_by p.arrayLength
    
    
    def insShiftDefEncoding (isShiftDef: IsShiftDefEncoding p):
      InsEdl shiftDefEncoding p
    :=
      match p with
      | zero => isShiftDef.elim
      | pair _a zero => isShiftDef.elim
      | pair a (pair b c) =>
        insWfmDefToIns
          (match isShiftDef with
          | IsShiftDefEncodingABC.ZeroShift isDefB =>
            insUnL _
              (insUnDom
                (insFree
                  (insDefEncoding isDefB)
                  nat500NeqDefEncoding)
                (insPair
                  insZero
                  (insPair
                    insBound
                    insBound)))
          | IsShiftDefEncodingABC.SuccShift isShiftPrev isInc =>
            insUnR _
              (insUnDom
                (insFree
                  (insNatEncoding
                    isShiftPrev.isNatA)
                  nat500NeqNat)
                (insUnDom
                  (insFree
                    (insFree
                      (insDefEncoding
                        isShiftDef.isDefB)
                      nat500NeqDefEncoding)
                    nat501NeqDefEncoding)
                  (insPair
                    (insPair
                      (insFree
                        insBound
                        nat501Neq500)
                      insZero)
                    (insPair
                      insBound
                      (insCallExpr
                        (insIncrVarsDefEncoding isInc)
                        (insCallExpr
                          (insCallExpr
                            (insShiftDefEncoding isShiftPrev)
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    insBound
                                    nat501Neq500)
                                  nat502Neq500)
                                nat503Neq500)
                              nat504Neq500))
                          (insFree
                            (insFree
                              insBound
                              nat502Neq501)
                            nat503Neq501))))))))
    termination_by p.depthA
    decreasing_by exact depthLtL _ zero
    
    def Inw.toIsShiftDefEncoding (inw: InwEdl shiftDefEncoding p):
      IsShiftDefEncoding p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw =>
          let ⟨dl, ⟨inwDomain, inw⟩⟩ := inwUnDomElim inw
          let isDefDl := Inw.toIsDefEncoding inwDomain
          
          match p with
          | zero => inwPairElim.nope inw
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair a (pair b c) =>
            let ⟨inwA, inw⟩ := inwPairElim inw
            let ⟨inwB, inwC⟩ := inwPairElim inw
            
            inwZeroElim inwA ▸
            inwBoundElim inwB ▸
            (inwBoundElim inwC).symm ▸
            IsShiftDefEncodingABC.ZeroShift isDefDl)
        (fun inw =>
          let ⟨n, ⟨inwDomainN, inw⟩⟩ := inwUnDomElim inw
          let ⟨dl, ⟨inwDomainDl, inw⟩⟩ := inwUnDomElim inw
          
          match p with
          | zero => inwPairElim.nope inw
          | pair _ zero => inwPairElim.nope (inwPairElim inw).inwR
          | pair zero _ => inwPairElim.nope (inwPairElim inw).inwL
          | pair (pair aA aB) (pair b c) =>
            let ⟨inwA, inw⟩ := inwPairElim inw
            let ⟨inwAA, inwAB⟩ := inwPairElim inwA
            let ⟨inw501, inwCallOuter⟩ := inwPairElim inw
            
            let eqAA := inwBoundElim (inwFreeElim inwAA nat501Neq500)
            let eqAB := inwZeroElim inwAB
            let eqDl := inwBoundElim inw501
            
            let ⟨argOuter, ⟨inwFnOuter, inwArgOuter⟩⟩ :=
              inwCallExprElim inwCallOuter
            
            let inwCallMiddle :=
              inwCallElimBound inwArgOuter rfl nat503Neq501
            
            let inw :=
              inwCallElimBound inwCallMiddle rfl nat504Neq500
            
            have := eqAA ▸ depthLtL aA aB
            
            eqAA ▸
            eqAB ▸
            eqDl.symm ▸
            IsShiftDefEncodingABC.SuccShift
              (toIsShiftDefEncoding inw)
              (Inw.toIsIncrVarsDefEncoding inwFnOuter))
    termination_by p.depthA
  end uniSet3
end Pair
