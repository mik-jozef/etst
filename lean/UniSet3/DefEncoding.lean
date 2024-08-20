import UniSet3.ExprEncoding


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insDefEncoding (isDefEnc: IsDefEncoding p):
      InsEdl defEncoding p
    :=
      insWfmDef.toInsWfm
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
        (inwWfm.toInwWfmDef w).elim
          (fun inwL => inwZeroElim.nope inwL)
          (fun inwR =>
            let ⟨l, r⟩ := inwPairElim inwR
            
            And.intro
              (Inw.toIsExprEncoding l)
              (Inw.toIsDefEncoding r))
    
  end uniSet3
end Pair
