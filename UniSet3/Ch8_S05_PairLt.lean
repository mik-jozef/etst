-- The fifth section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S04_PairOfDepth


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insSameDepth (isSameDepth: IsSameDepth p):
      InsEdl sameDepth p
    :=
      match p with
      | zero => isSameDepth.elim
      | pair a b =>
        let isPodB: IsPairOfDepth (pair (fromNat a.depth) b) := {
          isNat := fromNat.isNatEncoding _
          eqDepth := (fromNat.depthEq _).trans isSameDepth
        }
        
        insWfmDefToIns
          (insUnDom
            (insFree
              (insNatEncoding (fromNat.isNatEncoding a.depth))
              nat500NeqNat)
            (insPair
              (insCallExpr
                (insFree
                  (insFree
                    (insPairOfDepth (IsPairOfDepth.ofDepth a))
                    nat500NeqPairOfDepth)
                  nat501NeqPairOfDepth)
                (insFree insBound nat501Neq500))
              (insCallExpr
                (insFree
                  (insFree
                    (insPairOfDepth isPodB)
                    nat500NeqPairOfDepth)
                  nat501NeqPairOfDepth)
                (insFree insBound nat501Neq500))))
    
    def Inw.toIsSameDepth (inw: InwEdl sameDepth p):
      IsSameDepth p
    :=
      let ⟨depthEncoding, ⟨_inwDomain, inwBody⟩⟩ :=
        inwUnDomElim (inwWfmToInwDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair a b =>
        let ⟨l, r⟩ := inwPairElim inwBody
        
        let ⟨_argL, ⟨inwFnL, inwArgL⟩⟩ := inwCallExprElim l
        let ⟨_argR, ⟨inwFnR, inwArgR⟩⟩ := inwCallExprElim r
        
        let argEqL := inwBoundElim (inwFreeElim inwArgL nat501Neq500)
        let argEqR := inwBoundElim (inwFreeElim inwArgR nat501Neq500)
        
        let isPodA: IsPairOfDepth (pair depthEncoding a) :=
          Inw.toIsPairOfDepth
            (inwFreeElim
              (inwFreeElim
                (argEqL ▸ inwFnL)
                nat501NeqPairOfDepth)
              nat500NeqPairOfDepth)
        
        let isPodB: IsPairOfDepth (pair depthEncoding b) :=
          Inw.toIsPairOfDepth
            (inwFreeElim
              (inwFreeElim
                (argEqR ▸ inwFnR)
                nat501NeqPairOfDepth)
              nat500NeqPairOfDepth)
        
        isPodA.eqDepth.symm.trans isPodB.eqDepth
    
    
    def insPairLt (isLt: IsPairLt p):
      InsEdl pairLt p
    :=
      match p with
      | zero => isLt.elim
      | pair a b =>
        insWfmDefToIns
          (isLt.rec
            (fun eqDepth ltDict =>
              let isSameDepth: IsSameDepth (pair a b) := eqDepth
              
              insUnL _
                (insIr
                  (insSameDepth isSameDepth)
                  (insPairDictLt ltDict)))
          (fun depthLt =>
            let isLt:
              IsNatLt (pair (fromNat a.depth) (fromNat b.depth))
            := {
              isNatA := fromNat.isNatEncoding _
              isNatB := fromNat.isNatEncoding _
              isLt :=
                (fromNat.depthEq _) ▸ (fromNat.depthEq _) ▸ depthLt
            }
            
            insUnR _
              (insUnDom
                (insFree
                  (insNatLt isLt)
                  nat500NeqNatLt)
                (insPair
                  (insCallExpr
                    (insFree
                      (insFree
                        (insPairOfDepth {
                          isNat := fromNat.isNatEncoding a.depth
                          eqDepth := fromNat.depthEq a.depth
                        })
                        nat500NeqPairOfDepth)
                      nat501NeqPairOfDepth)
                    (insZthMember
                      (insFree
                        (insFree insBound nat501Neq500)
                      nat502Neq500)))
                  (insCallExpr
                    (insFree
                      (insFree
                        (insPairOfDepth {
                          isNat := fromNat.isNatEncoding b.depth
                          eqDepth := fromNat.depthEq b.depth
                        })
                        nat500NeqPairOfDepth)
                      nat501NeqPairOfDepth)
                    (insFstMember
                      (insFree
                        (insFree insBound nat501Neq500)
                      nat502Neq500)))))))
    
    def Inw.toIsPairLt (inw: InwEdl pairLt p):
      IsPairLt p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw =>
          let ⟨inwSameDepth, inwPairDictLt⟩ := inwIrElim inw
          match p with
          | zero => Inw.toIsSameDepth inwSameDepth
          | pair _ _ =>
            
            depthDictOrder.Lt.EqDepth
              (Inw.toIsSameDepth inwSameDepth)
              (Inw.toIsPairDictLt inwPairDictLt))
        (fun inw =>
          let ⟨bound, ⟨inwDomain, inwBody⟩⟩ := inwUnDomElim inw
          
          match bound with
          | zero =>
            -- Lean issue. Should work outside of match too.
            let insNatLtBound: IsNatLt zero := Inw.toIsNatLt
              (inwFreeElim inwDomain nat500NeqNatLt)
            
            insNatLtBound.elim
          | pair boundA boundB =>
            let insNatLtBound: IsNatLt (pair boundA boundB) :=
              Inw.toIsNatLt (inwFreeElim inwDomain nat500NeqNatLt)
            
            match p with
            | zero => inwPairElim.nope inwBody
            | pair pA pB =>
              let ⟨l, r⟩ := inwPairElim inwBody
              let ⟨_argL, ⟨inwFnL, inwArgL⟩⟩ := inwCallExprElim l
              let ⟨_argR, ⟨inwFnR, inwArgR⟩⟩ := inwCallExprElim r
              
              let ⟨_argRAlias, inwL⟩ := inwZthMemberElim inwArgL
              let ⟨_argLAlias, inwR⟩ := inwFstMemberElim inwArgR
              
              let inwL :=
                inwBoundElim
                  (inwFreeElim
                    (inwFreeElim
                      inwL
                      nat502Neq500)
                    nat501Neq500)
              
              let inwR :=
                inwBoundElim
                  (inwFreeElim
                    (inwFreeElim
                      inwR
                      nat502Neq500)
                    nat501Neq500)
              
              let ⟨eqL, _⟩ := Pair.noConfusion inwL And.intro
              let ⟨_, eqR⟩ := Pair.noConfusion inwR And.intro
              
              let isPodA: IsPairOfDepth (pair boundA pA) :=
                eqL ▸
                Inw.toIsPairOfDepth
                  (inwFreeElim
                    (inwFreeElim inwFnL nat501NeqPairOfDepth)
                    nat500NeqPairOfDepth)
              
              let isPodB: IsPairOfDepth (pair boundB pB) :=
                eqR ▸
                Inw.toIsPairOfDepth
                  (inwFreeElim
                    (inwFreeElim inwFnR nat501NeqPairOfDepth)
                    nat500NeqPairOfDepth)
              
              depthDictOrder.Lt.NeqDepth
                (isPodA.eqDepth ▸ isPodB.eqDepth ▸ insNatLtBound.isLt))
    
  end uniSet3
end Pair
