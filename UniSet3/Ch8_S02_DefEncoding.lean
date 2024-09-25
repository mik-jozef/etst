-- The second section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S01_Nat


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insExprEncoding.zero:
      InsEdl exprEncoding.zero (pair (fromNat 1) zero)
    :=
      (insWfmDefToIns
        (insPair (insNatExpr _ _) insZero))
    
    def Inw.toIsExprEncodinng.zero
      (w: InwEdl exprEncoding.zero p)
    :
      p = (pair (fromNat 1) zero)
    :=
      match p with
      | Pair.zero => inwPairElim.nope (inwWfmToInwDef w)
      | Pair.pair Pair.zero _ =>
        inwPairElim.nope (inwPairElim (inwWfmToInwDef w)).inwL
      | Pair.pair _ _ =>
        let ⟨inwL, inwR⟩ := inwPairElim (inwWfmToInwDef w)
        
        (inwNatExprElim inwL) ▸ (inwZeroElim inwR) ▸ rfl
    
    
    def insExprEncoding.binary (isEEB: IsExprEncoding.Bin p):
      InsEdl exprEncoding.binary p
    :=
      open IsExprEncoding.Bin in
      insWfmDefToIns
        (match isEEB with
        | Is2 eq => eq ▸ insUnL _ (insNatExpr _ _)
        | Is3 eq => eq ▸ insUnR _ (insUnL _ (insNatExpr _ _))
        | Is4 eq => eq ▸ insUnR _ (insUnR _ (insUnL _ (insNatExpr _ _)))
        | Is6 eq => eq ▸ insUnR _ (insUnR _ (insUnR _ (insNatExpr _ _))))
    
    def Inw.toIsExprEncoding.binary
      (w: InwEdl exprEncoding.binary p)
    :
      IsExprEncoding.Bin p
    :=
      open IsExprEncoding.Bin in
      (inwWfmToInwDef w).elim
        (fun inwNatExpr2 => Is2 (inwNatExprElim inwNatExpr2))
        (fun un => un.elim
          (fun inwNatExpr3 => Is3 (inwNatExprElim inwNatExpr3))
          (fun un => un.elim
            (fun inwNatExpr4 => Is4 (inwNatExprElim inwNatExpr4))
            (fun inwNatExpr6 => Is6 (inwNatExprElim inwNatExpr6))))
    
    
    def insExprEncoding.quantifier (isEEB: IsExprEncoding.Quantifier p):
      InsEdl exprEncoding.quantifier p
    :=
      open IsExprEncoding.Quantifier in
      insWfmDefToIns
        (match isEEB with
        | Is7 eq => eq ▸ insUnL _ (insNatExpr _ _)
        | Is8 eq => eq ▸ insUnR _ (insNatExpr _ _))
    
    def Inw.toIsExprEncoding.quantifier
      (w: InwEdl exprEncoding.quantifier p)
    :
      IsExprEncoding.Quantifier p
    :=
      open IsExprEncoding.Quantifier in
      (inwWfmToInwDef w).elim
        (fun inwNatExpr7 => Is7 (inwNatExprElim inwNatExpr7))
        (fun inwNatExpr8 => Is8 (inwNatExprElim inwNatExpr8))
    
    
    def insExprEncoding (isEE: IsExprEncoding p):
      InsEdl exprEncoding p
    :=
      insWfmDefToIns
        (match isEE with
        | IsExprEncoding.IsVar isNatX =>
          let inList:
            Expr.var exprEncoding.var ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insWfmDefToIns
              (insPair insZero (insNatEncoding isNatX)))
        | IsExprEncoding.IsZero =>
          let inList:
            Expr.var exprEncoding.zero ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn inList insExprEncoding.zero
        | IsExprEncoding.IsBin nBin aExpr bExpr =>
          let inList:
            exprEncoding.binExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair
              (insExprEncoding.binary nBin)
              (insPair
                (insExprEncoding aExpr)
                (insExprEncoding bExpr)))
        | IsExprEncoding.IsCpl isExpr =>
          let inList:
            exprEncoding.cplExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair (insNatExpr _ 5) (insExprEncoding isExpr))
        | IsExprEncoding.IsQuantifier isQ isNat isExpr =>
          let inList:
            exprEncoding.quantifierExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair
              (insExprEncoding.quantifier isQ)
              (insPair (insNatEncoding isNat) (insExprEncoding isExpr))))
    
    def Inw.toIsExprEncoding
      (w: InwEdl exprEncoding p)
    :
      IsExprEncoding p
    :=
      open IsExprEncoding in
      inwFinUnElim (inwWfmToInwDef w)
        (fun inwVar =>
          match p with
          | Pair.zero =>
            inwPairElim.nope (inwWfmToInwDef inwVar)
          | Pair.pair (Pair.pair _ _) _ =>
            inwZeroElim.nope
              (inwPairElim (inwWfmToInwDef inwVar)).inwL
          | Pair.pair zero _ =>
            let ⟨_, inwNat⟩ :=
              inwPairElim (inwWfmToInwDef inwVar)
            
            IsVar (Inw.toIsNatEncoding inwNat))
        (fun inwZero =>
          let ⟨_l, _r, ⟨eq, inwL, inwR⟩⟩ :=
            inwPairElim.ex (inwWfmToInwDef inwZero)
          
          eq ▸ (inwNatExprElim inwL) ▸ (inwZeroElim inwR) ▸ IsZero)
        (fun inwBin =>
          match p with
          | Pair.zero => inwPairElim.nope inwBin
          | Pair.pair _l r =>
            let ⟨inwL, inwR⟩ := inwPairElim inwBin
            
            match r with
            | Pair.zero => inwPairElim.nope inwR
            | Pair.pair _ _ =>
              let ⟨rInwL, rInwR⟩ := inwPairElim inwR
              
              IsBin
                (Inw.toIsExprEncoding.binary inwL)
                (Inw.toIsExprEncoding rInwL)
                (Inw.toIsExprEncoding rInwR))
        (fun inwCpl =>
          match p with
          | Pair.zero => inwPairElim.nope inwCpl
          | Pair.pair _ _ =>
            let ⟨l, r⟩ := inwPairElim inwCpl
            (inwNatExprElim l) ▸ IsCpl (toIsExprEncoding r))
        (fun inwQuant =>
          match p with
          | Pair.zero => inwPairElim.nope inwQuant
          | Pair.pair _l r =>
            let ⟨inwL, inwR⟩ := inwPairElim inwQuant
            
            match r with
            | Pair.zero => inwPairElim.nope inwR
            | Pair.pair _ _ =>
              let ⟨rInwL, rInwR⟩ := inwPairElim inwR
              
              IsQuantifier
                (Inw.toIsExprEncoding.quantifier inwL)
                (Inw.toIsNatEncoding rInwL)
                (Inw.toIsExprEncoding rInwR))
    
    
    def insDefEncoding (isDefEnc: IsDefEncoding p):
      InsEdl defEncoding p
    :=
      insWfmDefToIns
        (match p with
        | Pair.zero => insUnL _ insZero
        | Pair.pair _ _ =>
          insUnR
            _
            (insPair
              (insExprEncoding isDefEnc.left)
              (insDefEncoding isDefEnc.right)))
    
    def Inw.toIsDefEncoding (w: InwEdl defEncoding p):
      IsDefEncoding p
    :=
      match p with
      | Pair.zero => trivial
      | Pair.pair _ _ =>
        (inwWfmToInwDef w).elim
          (fun inwL => inwZeroElim.nope inwL)
          (fun inwR =>
            let ⟨l, r⟩ := inwPairElim inwR
            
            And.intro
              (Inw.toIsExprEncoding l)
              (Inw.toIsDefEncoding r))
    
  end uniSet3
end Pair
