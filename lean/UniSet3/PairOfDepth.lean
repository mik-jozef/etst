import UniSet3.Nat


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insPairOfDepth.p p (isPoD: IsPairOfDepth p):
      Ins pairOfDepth p
    :=
      match p with
      | zero => isPoD.elim
      | pair n p =>
        insWfmDef.toInsWfm
          (match n, p with
          | zero, zero =>
            let nEqZero := depth.eqZeroOfEqZero isPoD.eqDepth
            
            (insUnL (insPair (nEqZero ▸ insZero) insZero) _)
          | zero, pair _ _ => Nat.noConfusion isPoD.eqDepth
          | pair _ _, zero => Nat.noConfusion isPoD.eqDepth
          | pair nA nB, pair pA pB =>
            
            insUnR
              _
              ((depth.casesEq pA pB).elim
                (fun ⟨depthEq, depthLe⟩ =>
                  let isPoDA: IsPairOfDepth (pair nA pA) := {
                    isNat := isPoD.isNat.left
                    eqDepth :=
                      let depthEqN :=
                        depth.nat.eqSuccDepthPred isPoD.isNat
                      let succEq := depthEqN.symm.trans
                        (isPoD.eqDepth.trans depthEq)
                      
                      Nat.noConfusion succEq id
                  }
                  
                  let pBAndDepth := pair (fromNat pB.depth) pB
                  
                  let isPoDB: IsPairOfDepth pBAndDepth := {
                    isNat := fromNat.isNatEncoding _
                    eqDepth := fromNat.depthEq _
                  }
                  
                  have := depth.leZth nA nB pA pB
                  have:
                    pBAndDepth.depth
                      <
                    (pair (pair nA nB) (pair pA pB)).depth
                  :=
                    let eq: pBAndDepth.depth = Nat.succ pB.depth :=
                      (depth.casesEq (fromNat pB.depth) pB).elim
                        (fun ⟨eq, _⟩ =>
                          eq ▸ congr rfl (fromNat.depthEq pB.depth))
                        (fun ⟨eq, _⟩ => eq)
                    eq ▸ (Nat.succ_le_succ depthLe).trans_lt
                      ((Nat.succ_le_succ (depthLtL pA pB)).trans
                        (depthLtR (pair nA nB) (pair pA pB)))
                  
                  insUnDom
                    (insNatEncoding isPoD.isNat.left)
                    (insUnDom
                      (insCall
                        (insPairOfDepth.p _ isPoDA)
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500))
                      (insUnDom
                        (insCall
                          (insPairOfDepth.p _ isPoDB)
                          (insCall
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insNatLeFn {
                                      isNatA := isPoD.isNat.left
                                      isNatB := fromNat.isNatEncoding pB.depth
                                      isLe :=
                                        (fromNat.depthEq _) ▸
                                        isPoDA.eqDepth ▸ depthLe
                                    })
                                    nat501NeqNatLeFn)
                                  nat502NeqNatLeFn)
                                nat503NeqNatLeFn)
                              nat504NeqNatLeFn)
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    insBound
                                    nat501Neq500)
                                  nat502Neq500)
                                nat503Neq500)
                              nat504Neq500)))
                        (insUnL
                          (insPair
                            (insPair
                              (insFree
                                (insFree insBound nat501Neq500)
                                nat502Neq500)
                              (isPoD.isNat.right ▸ insZero))
                            (insPair
                              (insFree insBound nat502Neq501)
                              insBound))
                          _))))
                
                (fun ⟨depthEq, depthLt⟩ =>
                  let isPoDB: IsPairOfDepth (pair nA pB) := {
                    isNat := isPoD.isNat.left
                    eqDepth :=
                      let depthEqN :=
                        depth.nat.eqSuccDepthPred isPoD.isNat
                      let succEq := depthEqN.symm.trans
                        (isPoD.eqDepth.trans depthEq)
                      
                      Nat.noConfusion succEq id
                  }
                  
                  let pAAndDepth := pair (fromNat pA.depth) pA
                  
                  let isPoDA: IsPairOfDepth pAAndDepth := {
                    isNat := fromNat.isNatEncoding _
                    eqDepth := fromNat.depthEq _
                  }
                  
                  have := depth.leZthFst nA nB pA pB
                  have:
                    pAAndDepth.depth
                      <
                    (pair (pair nA nB) (pair pA pB)).depth
                  :=
                    let eq: pAAndDepth.depth = Nat.succ pA.depth :=
                      (depth.casesEq (fromNat pA.depth) pA).elim
                        (fun ⟨eq, _⟩ =>
                          eq ▸ congr rfl (fromNat.depthEq pA.depth))
                        (fun ⟨eq, _⟩ => eq)
                    let depthSuccLe := Nat.succ_le_of_lt depthLt
                    eq ▸ depthSuccLe.trans_lt
                      ((depthLtR pA pB).trans (depthLtR _ _))
                  
                  insUnDom
                    (insNatEncoding isPoD.isNat.left)
                    (insUnDom
                      (insCall
                        (insPairOfDepth.p _ isPoDB)
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500))
                      (insUnDom
                        (insCall
                          (insPairOfDepth.p _ isPoDA)
                          (insCall
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insNatLeFn {
                                      isNatA := isPoD.isNat.left
                                      isNatB := fromNat.isNatEncoding pA.depth
                                      isLe :=
                                        (fromNat.depthEq _) ▸
                                        isPoDB.eqDepth ▸
                                        Nat.le_of_lt depthLt
                                    })
                                    nat501NeqNatLeFn)
                                  nat502NeqNatLeFn)
                                nat503NeqNatLeFn)
                              nat504NeqNatLeFn)
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    insBound
                                    nat501Neq500)
                                  nat502Neq500)
                                nat503Neq500)
                              nat504Neq500)))
                        (insUnR
                          _
                          (insPair
                            (insPair
                              (insFree
                                (insFree insBound nat501Neq500)
                                nat502Neq500)
                              (isPoD.isNat.right ▸ insZero))
                            (insPair
                              insBound
                              (insFree insBound nat502Neq501)))))))))
    termination_by insPairOfDepth.p p isPoD => p.depth
    
    def insPairOfDepth (isPoD: IsPairOfDepth p):
      Ins pairOfDepth p
    :=
      insPairOfDepth.p p isPoD
    
    
    def Inw.toIsPairOfDepthAB n p (inw: Inw pairOfDepth (pair n p)):
      IsPairOfDepth (pair n p)
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          let ⟨l, r⟩ := inwPairElim inw
          let aEq := inwZeroElim l
          let bEq := inwZeroElim r
          
          let isZ: IsPairOfDepth (pair zero zero) := {
            isNat := trivial
            eqDepth := rfl
          }
          
          aEq ▸ bEq ▸ isZ)
        (fun inw =>
          let ⟨bound500, ___inwDomain, inwBody⟩ := inwUnDomElim inw
          let ⟨bound501, inwDomain501, inwBody⟩ := inwUnDomElim inwBody
          let ⟨bound502, inwDomain502, inwBody⟩ := inwUnDomElim inwBody
          
          let ⟨arg, ⟨inwFn, inwArg⟩⟩ := inwCallElim inwDomain501
          
          let argEq500 := inwBoundElim
            (inwFreeElim (inwFreeElim inwArg nat502Neq500) nat501Neq500)
          
          let inwPoD500501 := argEq500 ▸
            inwFreeElim
              (inwFreeElim
                (inwFreeElim inwFn nat502NeqPairOfDepth)
                nat501NeqPairOfDepth)
              nat500NeqPairOfDepth
          
          let ⟨argOuter, ⟨inwFnOuter, inwArgOuter⟩⟩ :=
            inwCallElim inwDomain502
          let ⟨argInner, ⟨inwFnInner, inwArgInner⟩⟩ :=
            inwCallElim inwArgOuter
          
          let argInnerIs500 :=
            inwBoundElim
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    (inwFreeElim inwArgInner nat504Neq500)
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
          
          let ⟨isNat500, _isNatOuter, outerLe500⟩ :=
            argInnerIs500 ▸
            Inw.toIsNatLeFn
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    (inwFreeElim
                      (inwFreeElim inwFnInner nat504NeqNatLeFn)
                    nat503NeqNatLeFn)
                  nat502NeqNatLeFn)
                nat501NeqNatLeFn)
              nat500NeqNatLeFn)
          
          (inwUnElim inwBody).elim
            (fun inw =>
              match h: n, p with
              | zero, _ => inwPairElim.nope (inwPairElim inw).inwL
              | _, zero => inwPairElim.nope (inwPairElim inw).inwR
              | pair nPred z, pair bA bB =>
                let ⟨inwSucc, inwPair⟩ := inwPairElim inw
                let ⟨inwPred, inwZ⟩ := inwPairElim inwSucc
                let ⟨inwA, inwB⟩ := inwPairElim inwPair
                
                let nPredEq500 :=
                  inwBoundElim
                    (inwFreeElim
                      (inwFreeElim inwPred nat502Neq500)
                      nat501Neq500)
                
                let aEq501 := inwBoundElim (inwFreeElim inwA nat502Neq501)
                let bEq502 := inwBoundElim inwB
                
                let zEq := inwZeroElim inwZ
                
                have: depth argOuter < depth n :=
                  h ▸
                  nPredEq500 ▸
                  outerLe500.trans_lt (depthLtL bound500 z)
                
                have: depth bound500 < depth n :=
                  h ▸ nPredEq500 ▸ (depthLtL nPred z)
                
                let isPodArgOuter502 := Inw.toIsPairOfDepthAB _ _
                  (inwFreeElim inwFnOuter nat503NeqPairOfDepth)
                
                let isPod500501 := Inw.toIsPairOfDepthAB _ _ inwPoD500501
                
                {
                  isNat :=
                    And.intro (nPredEq500 ▸ isNat500) zEq
                  eqDepth :=
                    let eqL: (pair nPred z).depth = Nat.succ nPred.depth :=
                      depth.eqL (zEq ▸ Nat.zero_le nPred.depth)
                    
                    let eqR: (pair bA bB).depth = Nat.succ bA.depth :=
                      depth.eqL
                        (aEq501 ▸
                        bEq502 ▸
                        isPod500501.eqDepth ▸
                        isPodArgOuter502.eqDepth ▸
                        outerLe500)
                    let eqMid: Nat.succ nPred.depth = Nat.succ bA.depth :=
                      aEq501 ▸
                      nPredEq500 ▸
                      congr rfl isPod500501.eqDepth
                    
                    (eqL.trans eqMid).trans eqR.symm
                })
            (fun inw =>
              match h: n, p with
              | zero, _ => inwPairElim.nope (inwPairElim inw).inwL
              | _, zero => inwPairElim.nope (inwPairElim inw).inwR
              | pair nPred z, pair bA bB =>
                let ⟨inwSucc, inwPair⟩ := inwPairElim inw
                let ⟨inwPred, inwZ⟩ := inwPairElim inwSucc
                let ⟨inwA, inwB⟩ := inwPairElim inwPair
                
                let nPredEq500 :=
                  inwBoundElim
                    (inwFreeElim
                      (inwFreeElim inwPred nat502Neq500)
                      nat501Neq500)
                
                let aEq502 := inwBoundElim inwA
                let bEq501 := inwBoundElim (inwFreeElim inwB nat502Neq501)
                
                let zEq := inwZeroElim inwZ
                
                have: depth argOuter < depth n :=
                  h ▸
                  nPredEq500 ▸
                  outerLe500.trans_lt (depthLtL bound500 z)
                
                have: depth bound500 < depth n :=
                  h ▸ nPredEq500 ▸ (depthLtL nPred z)
                
                let isPodArgOuter502 := Inw.toIsPairOfDepthAB _ _
                  (inwFreeElim inwFnOuter nat503NeqPairOfDepth)
                
                let isPod500501 := Inw.toIsPairOfDepthAB _ _ inwPoD500501
                
                {
                  isNat :=
                    And.intro (nPredEq500 ▸ isNat500) zEq
                  eqDepth :=
                    let eqL: (pair nPred z).depth = Nat.succ nPred.depth :=
                      depth.eqL (zEq ▸ Nat.zero_le nPred.depth)
                    
                    let eqR: (pair bA bB).depth = Nat.succ bB.depth :=
                      depth.eqR
                        (aEq502 ▸
                        bEq501 ▸
                        isPod500501.eqDepth ▸
                        isPodArgOuter502.eqDepth ▸
                        outerLe500)
                    let eqMid: Nat.succ nPred.depth = Nat.succ bB.depth :=
                      bEq501 ▸
                      nPredEq500 ▸
                      congr rfl isPod500501.eqDepth
                    
                    (eqL.trans eqMid).trans eqR.symm
                }))
    termination_by Inw.toIsPairOfDepthAB n p inw => n.depth
    
    def Inw.toIsPairOfDepth (inw: Inw pairOfDepth p):
      IsPairOfDepth p
    :=
      match p with
      | zero =>
          (inwUnElim (inwWfm.toInwWfmDef inw)).elim
            (fun l => inwPairElim.nope l)
            (fun r =>
              let ⟨_, ⟨_, inwBody⟩⟩ := inwUnDomElim r
              let ⟨_, ⟨_, inwBody⟩⟩ := inwUnDomElim inwBody
              let ⟨_, ⟨_, inwBody⟩⟩ := inwUnDomElim inwBody
              
              (inwUnElim inwBody).elim
                (fun l => inwPairElim.nope l)
                (fun r => inwPairElim.nope r))
      | pair a b => toIsPairOfDepthAB a b inw
    
  end uniSet3
end Pair
