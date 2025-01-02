-- The sixth section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S05_PairLt


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insDefEncodingLt (isDefEncLt: IsDefEncodingLt p):
      InsEdl defEncodingLt p
    :=
      match p with
      | zero => isDefEncLt.elim
      | pair _ _ =>
        insWfmDefToIns
          (insIr
            (insPairLt isDefEncLt.isLt)
            (insPair
              (insDefEncoding isDefEncLt.isDefA)
              (insDefEncoding isDefEncLt.isDefB)))
    
    def Inw.toIsDefEncodingLt (inw: InwEdl defEncodingLt p):
      IsDefEncodingLt p
    :=
      let ⟨l, r⟩ := inwIrElim (inwWfmToInwDef inw)
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
    
    
    def insDefEncodingMinDist2 (isDefMd2: IsDefEncodingMinDist2 p):
      InsEdl defEncodingMinDist2 p
    :=
      match p with
      | zero => isDefMd2.elim
      | pair a b =>
        let ⟨isDefA, isDefB, ⟨x, ⟨ax, xb, isDefX⟩⟩⟩ := isDefMd2
        
        let isDefAX: IsDefEncodingLt (pair a x) := {
          isDefA,
          isDefB := isDefX,
          isLt := ax
        }
        
        let isDefXB: IsDefEncodingLt (pair x b) := {
          isDefA := isDefX,
          isDefB := isDefB,
          isLt := xb
        }
        
        let iRefuseToBeInferredQuackQuack: InsP _ _ _ _ _ :=
          insBound
        
        insWfmDefToIns
          (insArbUn a
            (insArbUn x
              (insArbUn b
                (insIfThen
                  (insPair
                    (insIr
                      (insFree
                        (insFree
                          (insFree
                            (insDefEncodingLt isDefAX)
                            nat500NeqDefEncodingLt)
                          nat501NeqDefEncodingLt)
                        nat502NeqDefEncodingLt)
                      (insPair
                        (insFree
                          (insFree
                            insBound
                            nat501Neq500)
                          nat502Neq500)
                        (insFree
                          insBound
                          nat502Neq501)))
                    (insIr
                      (insFree
                        (insFree
                          (insFree
                            (insDefEncodingLt isDefXB)
                            nat500NeqDefEncodingLt)
                          nat501NeqDefEncodingLt)
                        nat502NeqDefEncodingLt)
                      (insPair
                        (insFree
                          insBound
                          nat502Neq501)
                        iRefuseToBeInferredQuackQuack)))
                  (insPair
                    (insFree
                      (insFree
                        insBound
                        nat501Neq500)
                      nat502Neq500)
                    iRefuseToBeInferredQuackQuack)))))
    
    def Inw.toIsDefEncodingMinDist2 (inw: InwEdl defEncodingMinDist2 p):
      IsDefEncodingMinDist2 p
    :=
      let ⟨_a, inwBodyA⟩ := inwArbUnElim (inwWfmToInwDef inw)
      let ⟨x, inwBodyX⟩ := inwArbUnElim inwBodyA
      let ⟨_b, inwBodyB⟩ := inwArbUnElim inwBodyX
      
      let ⟨⟨c, inwCond⟩, inwBody⟩ := inwIfThenElim inwBodyB
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair _pA _pB =>
        let ⟨inw500pA, inw502pB⟩ := inwPairElim inwBody
        
        let eqA :=
          inwBoundElim
            (inwFreeElim
              (inwFreeElim inw500pA nat502Neq500)
              nat501Neq500)
        
        let eqB := inwBoundElim inw502pB
        
        match c with
        | zero => inwPairElim.nope inwCond
        | pair zero _ => inwPairElim.nope (inwPairElim inwCond).inwL.right
        | pair _ zero => inwPairElim.nope (inwPairElim inwCond).inwR.right
        | pair (pair _cAA _cAB) (pair _cBA _cBB) =>
          let ⟨inwIrCA, inwIrCB⟩ := inwPairElim inwCond
          
          let ⟨inwDefCA, inw500501A⟩ := inwIrElim inwIrCA
          let ⟨inwDefCB, inw500501B⟩ := inwIrElim inwIrCB
          
          let isDefLtCA :=
            Inw.toIsDefEncodingLt
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    inwDefCA
                    nat502NeqDefEncodingLt)
                  nat501NeqDefEncodingLt)
                nat500NeqDefEncodingLt)
          
          let isDefLtCB :=
            Inw.toIsDefEncodingLt
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    inwDefCB
                    nat502NeqDefEncodingLt)
                  nat501NeqDefEncodingLt)
                nat500NeqDefEncodingLt)
          
          let ⟨inw500cAA, inw501cAB⟩ := inwPairElim inw500501A
          let ⟨inw501cBA, inw502cBB⟩ := inwPairElim inw500501B
          
          let cAAeq :=
            inwBoundElim
              (inwFreeElim
                (inwFreeElim inw500cAA nat502Neq500)
                nat501Neq500)
          
          let cABeq :=
            inwBoundElim (inwFreeElim inw501cAB nat502Neq501)
          
          let cBAeq :=
            inwBoundElim (inwFreeElim inw501cBA nat502Neq501)
          
          let cBBeq := inwBoundElim inw502cBB
          
          eqA ▸ eqB ▸ cAAeq ▸ cBBeq ▸ {
            isDefA := isDefLtCA.isDefA
            isDefB := isDefLtCB.isDefB
            minDist2 := ⟨
              x,
              {
                ax := cABeq ▸ isDefLtCA.isLt
                xb := cBAeq ▸ isDefLtCB.isLt
                isDefX := cABeq ▸ isDefLtCA.isDefB
              }
            ⟩
          }
    
    def insNextDef (isNextDef: IsNextDef p):
      InsEdl nextDef p
    :=
      match p with
      | zero => isNextDef.elim
      | pair a b =>
        let isDefLtAB: IsDefEncodingLt (pair a b) := {
          isDefA := isNextDef.isDefA
          isDefB := isNextDef.isLeast.isMember.left
          isLt := isNextDef.isLeast.isMember.right
        }
        
        insWfmDefToIns
          (insIr
            (insDefEncodingLt isDefLtAB)
            (insCpl _
              (fun inwMinDist2 =>
                let ⟨_, _, ⟨x, ⟨axLt, xbLt, isDefX⟩⟩⟩ :=
                  Inw.toIsDefEncodingMinDist2 inwMinDist2
                
                let bxLe := isNextDef.isLeast.isLeMember
                  (And.intro isDefX axLt)
                
                let ltSelf: depthDictOrder.Lt x x :=
                  @lt_of_lt_of_le
                    _
                    depthDictOrder.toPreorder
                    _ _ _
                    xbLt bxLe
                
                ltSelf.irefl)))
    
    def Inw.toIsNextDef (inw: InwEdl nextDef p):
      IsNextDef p
    :=
      let ⟨inwDefEnc, inwCpl⟩ := inwIrElim (inwWfmToInwDef inw)
      
      match p with
      | zero => Inw.toIsDefEncodingLt inwDefEnc
      | pair _ _ =>
        let ⟨isDefA, isDefB, ab⟩ := Inw.toIsDefEncodingLt inwDefEnc
        
        let isLeast := {
          isMember := And.intro isDefB ab
          isLeMember :=
            fun ub ⟨isDefUB, aLtUb⟩ =>
              byContradiction fun nbub =>
                let ubLtB := (@not_le _ depthDictOrder).mp nbub
                let minDist2 := ⟨ub, {
                  ax := aLtUb
                  xb := ubLtB
                  isDefX := isDefUB
                }⟩
                
                inwCplElim
                  inwCpl
                  (insDefEncodingMinDist2
                    { isDefA, isDefB, minDist2 })
        }
        
        { isDefA, isLeast }
    
    
    def insNthDefList (isNthDef: IsNthDefList p):
      InsEdl nthDefList p
    :=
      match p with
      | zero => isNthDef.elim
      | pair _ _ =>
        insWfmDefToIns
          -- Using a match expression would require manually proving
          -- termination. Curious that using `rec` is easier :D
          (isNthDef.rec
            (insUnL _
              (insPair
                insZero
                insZero))
            (fun
              _isNthPredPair
              isNextPair
              insNthPredPair
            =>
              insUnR _
                (insUnDom
                  (insFree
                    (insWfmDefToIns insNthPredPair)
                    nat500NeqNthDefList)
                  (insPair
                    (insPair
                      (insZthMember
                        (insFree insBound nat501Neq500))
                      insZero)
                    (insCallExpr
                      (insFree
                        (insFree
                          (insNextDef
                            isNextPair)
                          nat500NeqNextDef)
                        nat501NeqNextDef)
                      (insFstMember
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)))))))
    
    def Inw.toIsNthDefList.ab a (inw: InwEdl nthDefList (pair a b)):
      IsNthDefList (pair a b)
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw =>
          let ⟨inwL, inwR⟩ := inwPairElim inw
          let eqL := inwZeroElim inwL
          let eqR := inwZeroElim inwR
          
          eqL ▸ eqR ▸ IsNthDefListPair.Zero)
        (fun inw =>
          let ⟨bound, ⟨inwDomain, inwBody⟩⟩ := inwUnDomElim inw
          let ⟨inwA, inwB⟩ := inwPairElim inwBody
          
          match a with
          | zero => inwPairElim.nope inwA
          | pair aPred z =>
            let ⟨inwAPred, inwZ⟩ := inwPairElim inwA
            let ⟨bPred, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim inwB
            let zEq := inwZeroElim inwZ
            
            let ⟨_bPredAlias, inwAPred⟩ := inwZthMemberElim inwAPred
            let ⟨_aPredAlias, inwArg⟩ := inwFstMemberElim inwArg
            
            let boundEqA :=
              inwBoundElim
                (inwFreeElim
                  inwAPred
                  nat501Neq500)
            
            let boundEqB :=
              inwBoundElim
                (inwFreeElim
                  (inwFreeElim
                    inwArg
                    nat502Neq500)
                  nat501Neq500)
            
            let boundEq :=
              Pair.noConfusion
                (boundEqA.trans boundEqB.symm)
                fun _ eqR => eqR ▸ boundEqA
            
            have: aPred.depth < (pair aPred z).depth := depthLtL _ _
            
            let isNthPred :=
              ab
                aPred
                (inwFreeElim
                  (boundEq ▸ inwDomain)
                  nat500NeqNthDefList)
            
            let isNextDef :=
              Inw.toIsNextDef
                (inwFreeElim
                  (inwFreeElim
                    inwFn
                    nat501NeqNextDef)
                  nat500NeqNextDef)
            
            zEq ▸ IsNthDefListPair.Succ isNthPred isNextDef)
    termination_by a.depth
    
    def Inw.toIsNthDefList (inw: InwEdl nthDefList p):
      IsNthDefList p
    :=
      match p with
      | zero =>
        (inwUnElim (inwWfmToInwDef inw)).elim
          inwPairElim.nope
          (fun inw =>
            inwPairElim.nope
              (inwUnDomElim inw).unwrap.property.inwBody)
      | pair a _ => toIsNthDefList.ab a inw
    
  end uniSet3
end Pair
