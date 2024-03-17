import UniSet3.PairLt
import UniSet3.DefEncoding


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insDefEncodingLt (isDefEncLt: IsDefEncodingLt p):
      Ins defEncodingLt p
    :=
      match p with
      | zero => isDefEncLt.elim
      | pair _ _ =>
        insWfmDef.toInsWfm
          (insIr
            (insPairLt isDefEncLt.isLt)
            (insPair
              (insDefEncoding isDefEncLt.isDefA)
              (insDefEncoding isDefEncLt.isDefB)))
    
    def Inw.toIsDefEncodingLt (inw: Inw defEncodingLt p):
      IsDefEncodingLt p
    :=
      let ⟨l, r⟩ := inwIrElim (inwWfm.toInwWfmDef inw)
      match p with
      | zero => (Inw.toIsPairLt l).elim
      | pair _ _ =>
        let isPairLt := Inw.toIsPairLt l
        let ⟨inwDefA, inwDefB⟩ := inwPairElim r
        
        {
          isDefA := Inw.toIsDefEncoding inwDefA
          isDefB := Inw.toIsDefEncoding inwDefB
          isLt := isPairLt
        }
    
  end uniSet3
end Pair
