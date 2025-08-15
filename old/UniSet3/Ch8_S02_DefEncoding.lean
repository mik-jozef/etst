-- The second section of chapter 8. See the zeroth section.

import old.UniSet3.Ch8_S01_Nat


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insExprEncoding.zero:
      InsEdl exprEncoding.zero (pair (fromNat 1) zero)
    :=
      (insWfmDefToIns
        (insPair (insNatExpr _ _ _) insZero))
    
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
      insWfmDefToIns
        (match isEEB with
        | .Pair eq => eq ▸ insUnL _ (insNatExpr _ _ _)
        | .Un eq => eq ▸ insUnR _ (insUnL _ (insNatExpr _ _ _))
        | .Ir eq => eq ▸ insUnR _ (insUnR _ (insNatExpr _ _ _)))
    
    def insExprEncoding.unary (isEEU: IsExprEncoding.Unary p):
      InsEdl exprEncoding.unary p
    :=
      insWfmDefToIns
        (match isEEU with
        | .Cpl eq => eq ▸ insUnL _ (insNatExpr _ _ _)
        | .CondSome eq => eq ▸ insUnR _ (insUnL _ (insNatExpr _ _ _))
        | .CondFull eq => eq ▸ insUnR _ (insUnR _ (insNatExpr _ _ _)))
    
    def Inw.toIsExprEncoding.binary
      (w: InwEdl exprEncoding.binary p)
    :
      IsExprEncoding.Bin p
    :=
      (inwWfmToInwDef w).elim
        (fun inwNatExpr2 => .Pair (inwNatExprElim inwNatExpr2))
        (fun un => un.elim
          (fun inwNatExpr3 => .Un (inwNatExprElim inwNatExpr3))
          (fun inwNatExpr4 => .Ir (inwNatExprElim inwNatExpr4)))
    
    def Inw.toIsExprEncoding.unary
      (w: InwEdl exprEncoding.unary p)
    :
      IsExprEncoding.Unary p
    :=
      (inwWfmToInwDef w).elim
        (fun inwNatExpr5 => .Cpl (inwNatExprElim inwNatExpr5))
        (fun inwNatExpr67 =>
          inwNatExpr67.elim
            (fun inw6 => .CondSome (inwNatExprElim inw6))
            (fun inw7 => .CondFull (inwNatExprElim inw7)))
    
    
    def insExprEncoding.quantifier (isEEB: IsExprEncoding.Quantifier p):
      InsEdl exprEncoding.quantifier p
    :=
      insWfmDefToIns
        (match isEEB with
        | .ArbUn eq => eq ▸ insUnL _ (insNatExpr _ _ _)
        | .ArbIr eq => eq ▸ insUnR _ (insNatExpr _ _ _))
    
    def Inw.toIsExprEncoding.quantifier
      (w: InwEdl exprEncoding.quantifier p)
    :
      IsExprEncoding.Quantifier p
    :=
      (inwWfmToInwDef w).elim
        (fun inwNatExpr7 => .ArbUn (inwNatExprElim inwNatExpr7))
        (fun inwNatExpr8 => .ArbIr (inwNatExprElim inwNatExpr8))
    
    
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
        | IsExprEncoding.IsUnary isUnary isExpr =>
          let inList:
            exprEncoding.unaryExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair
              (insExprEncoding.unary isUnary)
              (insExprEncoding isExpr))
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
        (fun inwUnary =>
          match p with
          | Pair.zero => inwPairElim.nope inwUnary
          | Pair.pair _ _ =>
            let ⟨inwL, inwR⟩ := inwPairElim inwUnary
            
            IsUnary
              (Inw.toIsExprEncoding.unary inwL)
              (toIsExprEncoding inwR))
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
        match inwWfmToInwDef w with
        | Or.inr inwR =>
          let ⟨l, r⟩ := inwPairElim inwR
          
          And.intro
            (Inw.toIsExprEncoding l)
            (Inw.toIsDefEncoding r)
    
  end uniSet3
end Pair
