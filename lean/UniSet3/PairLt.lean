import UniSet3.PairOfDepth
import UniSet3.PairDictLt


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insSameDepth (isSameDepth: IsSameDepth p):
      Ins sameDepth p
    :=
      match p with
      | zero => isSameDepth.elim
      | pair a b =>
        let isPodB: IsPairOfDepth (pair (fromNat a.depth) b) := {
          isNat := fromNat.isNatEncoding _
          eqDepth := (fromNat.depthEq _).trans isSameDepth
        }
        
        insWfmDef.toInsWfm
          (insUnDom
            (insNatEncoding (fromNat.isNatEncoding a.depth))
            (insPair
              (insCall
                (insPairOfDepth (IsPairOfDepth.ofDepth a))
                (insFree insBound nat501Neq500))
              (insCall
                (insPairOfDepth isPodB)
                (insFree insBound nat501Neq500))))
    
    def Inw.toIsSameDepth (inw: Inw sameDepth p):
      IsSameDepth p
    :=
      let ⟨depthEncoding, ⟨_inwDomain, inwBody⟩⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair a b =>
        let ⟨l, r⟩ := inwPairElim inwBody
        
        let ⟨_argL, ⟨inwFnL, inwArgL⟩⟩ := inwCallElim l
        let ⟨_argR, ⟨inwFnR, inwArgR⟩⟩ := inwCallElim r
        
        let argEqL := inwBoundElim (inwFreeElim inwArgL nat501Neq500)
        let argEqR := inwBoundElim (inwFreeElim inwArgR nat501Neq500)
        
        let isPodA: IsPairOfDepth (pair depthEncoding a) :=
          Inw.toIsPairOfDepth
            (inwFreeElim (argEqL ▸ inwFnL) nat501NeqPairOfDepth)
        
        let isPodB: IsPairOfDepth (pair depthEncoding b) :=
          Inw.toIsPairOfDepth
            (inwFreeElim (argEqR ▸ inwFnR) nat501NeqPairOfDepth)
        
        isPodA.eqDepth.symm.trans isPodB.eqDepth
    
    
    def insPairLt (isLt: IsPairLt p):
      Ins pairLt p
    :=
      match p with
      | zero => isLt.elim
      | pair a b =>
        insWfmDef.toInsWfm
          (isLt.rec
            (fun eqDepth ltDict =>
              let isSameDepth: IsSameDepth (pair a b) := eqDepth
              
              insUnL
                (insIr
                  (insSameDepth isSameDepth)
                  (insPairDictLt ltDict))
                _)
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
                (insNatLt isLt)
                (insPair
                  (insCall
                    (insPairOfDepth {
                      isNat := fromNat.isNatEncoding a.depth
                      eqDepth := fromNat.depthEq a.depth
                    })
                    (insZthMember
                      (insFree
                        (insFree insBound nat501Neq500)
                      nat502Neq500)))
                  (insCall
                    (insPairOfDepth {
                      isNat := fromNat.isNatEncoding b.depth
                      eqDepth := fromNat.depthEq b.depth
                    })
                    (insFstMember
                      (insFree
                        (insFree insBound nat501Neq500)
                      nat502Neq500)))))))
    
    def Inw.toIsPairLt (inw: Inw pairLt p):
      IsPairLt p
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
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
            -- Bad Lean. Should work outside of match too.
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
              let ⟨_argL, ⟨inwFnL, inwArgL⟩⟩ := inwCallElim l
              let ⟨_argR, ⟨inwFnR, inwArgR⟩⟩ := inwCallElim r
              
              let ⟨eqL, eqR⟩ :=
                Pair.noConfusion
                  (inwBoundElim
                    (inwFreeElim
                      (inwZthFstElim inwArgL inwArgR nat502Neq500 rfl)
                      nat501Neq500))
                (fun a b => And.intro a b)
              
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
