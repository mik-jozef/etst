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
    
  end uniSet3
end Pair
