import UniSet3.ExprEncoding


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
    
  end uniSet3
end Pair
