/-
  This whole chapter is dedicated to proving that the interpretation
  as defined in the external definition list works as intended.
  
  The four main results,
  
      `inDefNthOfInsTheSet` \,,
      `inPosNthOfInwTheSet` \,,
      `insTheSetOfInDefNth` \,, and
      `inwTheSetOfInPosNth` \,,
  
  are used in Chapter 10 to prove
  
      `uniSet3.isModelOfInternalDefList` \,.
  
  TODO rewrite the chapter description
  
  TODO go through the chapter and make sure there is no unused code.
-/

import UniSet3.Ch8_S12_DefListToEncoding
import Utils.IsStrongCause


/-
  `fn.pairCallJust arg` is the triset of pairs `b` such that
  `(arg, b)` is in `fn`.
  
  You can think of `fn` as a set of input-output pairs representing
  a function `f: Pair → Set3 Pair`.
-/
def Set3.pairCallJust
  (fn: Set3 Pair)
  (arg: Pair)
:
  Set3 Pair
:= {
  defMem := fun p => fn.defMem (Pair.pair arg p)
  posMem := fun p => fn.posMem (Pair.pair arg p)
  defLePos := fun _ pInDef => fn.defLePos pInDef
}

namespace Pair
  noncomputable def uniSet3 :=
    uniDefList.theExternalWfm uniDefList.theSet
  
  namespace uniSet3
    open Expr
    open PairExpr
    
    
    def decodeValuation
      (s3: Set3 Pair)
    :
      Valuation Pair
    :=
      fun n => Set3.pairCallJust s3 (fromNat n)
    
    def internalOfExternal
      (v: Valuation Pair)
    :
      Valuation Pair
    :=
      decodeValuation (v uniDefList.theSet)
    
    def theInternalValuation: Valuation Pair :=
      internalOfExternal uniDefList.theExternalWfm
    
    
    def interpretationInExprList.exprVar:
      uniDefList.interpretation.exprVar
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.exprZero:
      uniDefList.interpretation.exprZero
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.exprPair:
      uniDefList.interpretation.exprPair
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.exprUn:
      uniDefList.interpretation.exprUnion
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.exprIr:
      uniDefList.interpretation.exprIntersection
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.exprCpl:
      uniDefList.interpretation.exprCpl
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.exprIfThen:
      uniDefList.interpretation.exprIfThen
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.arbUn:
      uniDefList.interpretation.exprArbUnion
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    def interpretationInExprList.arbIr:
      uniDefList.interpretation.exprArbIntersection
        ∈
      uniDefList.interpretation.exprList
    :=
      by unfold uniDefList.interpretation.exprList; simp
    
    
    def boundVarsEncoding:
      List (ValVar Pair)
    →
      Pair
    
    | [] => zero
    | ⟨d, x⟩ :: rest => pair (pair x d) (boundVarsEncoding rest)
    
    def IsBound
      (boundVars: List (ValVar Pair))
      (x: Nat)
    :
      Prop
    :=
      ∃ d, IsGetBound (boundVarsEncoding boundVars) x d
    
    def IsBound.Not.xNotBoundHeadNotEq
      (notBound: ¬ IsBound (⟨dB, xB⟩ :: boundVars) x)
    :
      x ≠ xB
    :=
      fun xEq =>
        notBound ⟨
          dB,
          xEq ▸
          IsGetBound.InHead
            (fromNat.isNatEncoding x)
            dB
            (boundVarsEncoding boundVars)
        ⟩
    
    def IsBound.Not.notBoundTail
      (notBound: ¬ IsBound (⟨dB, xB⟩ :: boundVars) x)
      (xNeq: x ≠ xB)
    :
      ¬ IsBound boundVars x
    :=
      let encNeq := fromNat.injNeq xNeq.symm
      fun ⟨d, isGetBound⟩ =>
        notBound ⟨d, IsGetBound.InTail isGetBound dB encNeq⟩
    
    
    def _root_.Cause.SatisfiesBoundVars
      (cause: Cause Pair)
      (boundVars: List (ValVar Pair))
    :=
      ∀ {x xEnc d},
        xEnc = fromNat x →
        IsGetBound (boundVarsEncoding boundVars) xEnc d →
        cause.SatisfiesBoundVar x d
    
    def _root_.Cause.SatisfiesBoundVars.withBoundSat
      {cause: Cause Pair}
      (boundVarsSat: cause.SatisfiesBoundVars boundVars)
      (xEncEq: xEnc = fromNat x)
      (isGetBound:
        IsGetBound
          (boundVarsEncoding (⟨dB, xB⟩ :: boundVars))
          xEnc
          d)
    :
      (cause.withBound xB dB).SatisfiesBoundVar x d
    :=
      match isGetBound with
      | IsGetBound.InHead _ _ _ =>
        fromNat.injEq xEncEq ▸ {
          cinsSat :=
            fun _ inCinsWith xEq =>
              inCinsWith.elim (absurd xEq ∘ And.right) And.left
          binsSat :=
            fun _ inBinsWith xEq =>
              inBinsWith.elim (absurd xEq ∘ And.right) And.left
          boutSat :=
            fun _ inBoutWith xEq =>
              inBoutWith.elim (absurd xEq ∘ And.right) And.left
        }
      | IsGetBound.InTail isGetTail _ xEncNeq =>
        {
          cinsSat :=
            fun _ inCinsWith xEqX =>
              inCinsWith.elim
                (fun ⟨inCins, _⟩ =>
                  let isBoundSat :=
                    boundVarsSat xEncEq isGetTail
                  isBoundSat.cinsSat _ inCins xEqX)
                (fun ⟨_, xEqXb⟩ =>
                  absurd (xEqXb ▸ xEqX ▸ xEncEq.symm) xEncNeq)
          binsSat :=
            fun _ inBinsWith xEqX =>
              inBinsWith.elim
                (fun ⟨inBins, _⟩ =>
                  let isBoundSat :=
                    boundVarsSat xEncEq isGetTail
                  isBoundSat.binsSat _ inBins xEqX)
                (fun ⟨_, xEqXb⟩ =>
                  absurd (xEqXb ▸ xEqX ▸ xEncEq.symm) xEncNeq)
          boutSat :=
            fun _ inBoutWith xEqX =>
              inBoutWith.elim
                (fun ⟨inBout, _⟩ =>
                  let isBoundSat :=
                    boundVarsSat xEncEq isGetTail
                  isBoundSat.boutSat _ inBout xEqX)
                (fun ⟨_, xEqXb⟩ =>
                  absurd (xEqXb ▸ xEqX ▸ xEncEq.symm) xEncNeq)
        }
    
    
    def CinsInsExternal
      (internalCause: Cause Pair)
      (boundVars: List (ValVar Pair))
    :=
      ∀ {d} {x: Nat},
        ⟨d, x⟩ ∈ internalCause.contextIns →
        ¬IsBound boundVars x →
        Ins
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          (Pair.pair x d)
          uniDefList.theSet
    
    def BinsInsExternal
      (internalCause: Cause Pair)
      (boundVars: List (ValVar Pair))
    :=
      ∀ {d} {x: Nat},
        ⟨d, x⟩ ∈ internalCause.backgroundIns →
        ¬IsBound boundVars x →
        Ins
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          (Pair.pair x d)
          uniDefList.theSet
    
    def BoutOutExternal
      (internalCause: Cause Pair)
      (boundVars: List (ValVar Pair))
    :=
      ∀ {d} {x: Nat},
        ⟨d, x⟩ ∈ internalCause.backgroundOut →
        ¬IsBound boundVars x →
        Out
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          (Pair.pair x d)
          uniDefList.theSet
    
    
    def InsInterp
      (boundVarsEnc: Pair)
      (d: Pair)
      (exprEnc: Pair)
    :=
      Ins
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (pair boundVarsEnc (pair exprEnc d))
        uniDefList.interpretation
    
    
    def isCauseToInsInterp.var
      (isInternalCause:
        IsStrongCause pairSalgebra internalCause d (Expr.var x))
      (isConsistent: internalCause.IsConsistent)
      (boundVars: List (ValVar Pair))
      (boundVarsSat: internalCause.SatisfiesBoundVars boundVars)
      (cinsIns: CinsInsExternal internalCause boundVars)
    :
      InsInterp
        (boundVarsEncoding boundVars)
        d
        (exprToEncoding (var x))
    :=
      let insUn:
        Expr.Ins
          pairSalgebra
          (Valuation.update
            (uniDefList.theExternalWfm.update 500 (fromNat x))
            501
            (boundVarsEncoding boundVars))
          uniDefList.interpretation.exprVarBoundOrFree
          d
      :=
        let inCins := isInternalCause.elimVar isConsistent
        
        if h: IsBound boundVars x then
          let ⟨dAlias, isGetBound⟩ := h
          let boundVarSat := boundVarsSat rfl isGetBound
          let dEq: d = dAlias := boundVarSat.cinsSat _ inCins rfl
          
          dEq ▸ 
          insUnL _
            (insCallExpr
              (insCallExpr
                (insFree
                  (insFree
                    (insFree
                      (insFree
                        (insGetBound
                          isGetBound)
                        nat500NeqGetBounds)
                      nat501NeqGetBounds)
                    nat502NeqGetBounds)
                  nat503NeqGetBounds)
                (insFree
                  (insFree
                    insBound
                    nat502Neq501)
                  nat503Neq501))
              (insFree
                (insFree
                  insBound
                  nat501Neq500)
                nat502Neq500))
        else
          let ins := cinsIns inCins h
          let ninw inw :=
            let ⟨⟨boundVal, inw⟩, inwAny⟩ :=
                inwIfThenElim inw
              have: Expr.Inw pairSalgebra _ anyExpr zero := inwAny
              let inw := inwCallElimBound inw rfl nat502Neq500
              let inw := inwCallElimBound inw rfl nat503Neq501
            let insGetBound := Inw.toInsGetBound inw
            h ⟨boundVal, Inw.toIsGetBound insGetBound.toInw⟩
          
          insUnR _
            (insIfThen
              (insCpl ninw)
              (insCallExpr
                ins.isSound
                (insFree
                  (insFree
                    insBound
                    nat501Neq500)
                  nat502Neq500)))
      
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.exprVar
            (insUnDom
              (insNatEncoding
                (fromNat.isNatEncoding
                  x))
              (insArbUn
                (boundVarsEncoding
                  boundVars)
                (insPair
                  insBound
                  (insPair
                    (insPair
                      insZero
                      (insFree
                        insBound
                        nat501Neq500))
                    insUn))))))
    
    def isCauseToInsInterp.exprZero
      (isInternalCause:
        IsStrongCause pairSalgebra internalCause d zeroExpr)
      (isConsistent: internalCause.IsConsistent)
    :
      InsInterp
        (boundVarsEncoding boundVars)
        d
        (exprToEncoding zeroExpr)
    :=
      let ⟨_, (dEq: d = zero), _⟩ :=
        isInternalCause.elimOp (Or.inl isConsistent)
      
      Ins.isComplete _ _
        (insWfmDefToIns
        (insFinUn
          interpretationInExprList.exprZero
          (insArbUn
            (boundVarsEncoding
              boundVars)
            (insPair
              insBound
              (insPair
                (insPair
                  (insNatExpr _ _)
                  insZero)
                (dEq ▸ insZero))))))
    
    def isCauseToInsInterp.exprPair
      (insLeft: InsInterp boundVarsEnc dLeft (exprToEncoding left))
      (insRite: InsInterp boundVarsEnc dRite (exprToEncoding rite))
    :
      InsInterp
        boundVarsEnc
        (pair dLeft dRite)
        (exprToEncoding (pairExpr left rite))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.exprPair
            (insUnDom
              (insExprEncoding
                (exprToEncoding left).property)
              (insUnDom
                (insExprEncoding
                  (exprToEncoding rite).property)
                (insArbUn
                  boundVarsEnc
                  (insPair
                    insBound
                    (insPair
                      (insPair
                        (insNatExpr _ _)
                        (insPair
                          (insFree
                            (insFree
                              insBound
                              nat501Neq500)
                            nat502Neq500)
                          (insFree
                            insBound
                            nat502Neq501)))
                      (insPair
                        (insCallExpr
                          (insCallExpr
                            insLeft.isSound
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat501Neq500)
                              nat502Neq500)
                            nat503Neq500))
                        (insCallExpr
                          (insCallExpr
                            insRite.isSound
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              insBound
                              nat502Neq501)
                            nat503Neq501))))))))))
    
    def isCauseToInsInterp.exprUnLeft
      (insLeft: InsInterp boundVarsEnc d (exprToEncoding left))
    :
      InsInterp boundVarsEnc d (exprToEncoding (un left rite))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.exprUn
            (insUnDom
              (insExprEncoding
                (exprToEncoding left).property)
              (insUnDom
                (insExprEncoding
                  (exprToEncoding rite).property)
                (insArbUn
                  boundVarsEnc
                  (insPair
                    insBound
                    (insPair
                      (insPair
                        (insNatExpr _ _)
                        (insPair
                          (insFree
                            (insFree
                              insBound
                              nat501Neq500)
                            nat502Neq500)
                          (insFree
                            insBound
                            nat502Neq501)))
                      (insUnL _
                        (insCallExpr
                          (insCallExpr
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insFree
                                      insLeft.isSound
                                      nat500NeqInterpretation)
                                    nat501NeqInterpretation)
                                  nat502NeqInterpretation)
                                nat503NeqInterpretation)
                              nat504NeqInterpretation)
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat501Neq500)
                              nat502Neq500)
                            nat503Neq500))))))))))
    
    def isCauseToInsInterp.exprUnRite
      (insRite: InsInterp boundVarsEnc d (exprToEncoding rite))
    :
      InsInterp boundVarsEnc d (exprToEncoding (un left rite))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.exprUn
            (insUnDom
              (insExprEncoding
                (exprToEncoding left).property)
              (insUnDom
                (insExprEncoding
                  (exprToEncoding rite).property)
                (insArbUn
                  boundVarsEnc
                  (insPair
                    insBound
                    (insPair
                      (insPair
                        (insNatExpr _ _)
                        (insPair
                          (insFree
                            (insFree
                              insBound
                              nat501Neq500)
                            nat502Neq500)
                          (insFree
                            insBound
                            nat502Neq501)))
                      (insUnR _
                        (insCallExpr
                          (insCallExpr
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insFree
                                      insRite.isSound
                                      nat500NeqInterpretation)
                                    nat501NeqInterpretation)
                                  nat502NeqInterpretation)
                                nat503NeqInterpretation)
                              nat504NeqInterpretation)
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              insBound
                              nat502Neq501)
                            nat503Neq501))))))))))
    
    def isCauseToInsInterp.exprIr
      (insLeft: InsInterp boundVarsEnc d (exprToEncoding left))
      (insRite: InsInterp boundVarsEnc d (exprToEncoding rite))
    :
      InsInterp boundVarsEnc d (exprToEncoding (ir left rite))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
        (insFinUn
          interpretationInExprList.exprIr
            (insUnDom
              (insExprEncoding
                (exprToEncoding left).property)
              (insUnDom
                (insExprEncoding
                  (exprToEncoding rite).property)
                (insArbUn
                  boundVarsEnc
                  (insPair
                    insBound
                    (insPair
                      (insPair
                        (insNatExpr _ _)
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
                        (insCallExpr
                          (insCallExpr
                            insLeft.isSound
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat501Neq500)
                              nat502Neq500)
                            nat503Neq500))
                        (insCallExpr
                          (insCallExpr
                            insRite.isSound
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              insBound
                              nat502Neq501)
                            nat503Neq501))))))))))
    
    def isCauseToInsInterp.exprIfThen
      {cond}
      (insCond: InsInterp boundVarsEnc dC (exprToEncoding cond))
      (insBody: InsInterp boundVarsEnc d (exprToEncoding body))
    :
      InsInterp boundVarsEnc d (exprToEncoding (ifThen cond body))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.exprIfThen
            (insUnDom
              (insExprEncoding
                (exprToEncoding cond).property)
              (insUnDom
                (insExprEncoding
                  (exprToEncoding body).property)
                (insArbUn
                  boundVarsEnc
                  (insPair
                    insBound
                    (insPair
                      (insPair
                        (insNatExpr _ _)
                        (insPair
                          (insFree
                            (insFree
                              insBound
                              nat501Neq500)
                            nat502Neq500)
                          (insFree
                            insBound
                            nat502Neq501)))
                      (insIfThen
                        (insCallExpr
                          (insCallExpr
                            insCond.isSound
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              (insFree
                                insBound
                                nat501Neq500)
                              nat502Neq500)
                            nat503Neq500))
                        (insCallExpr
                          (insCallExpr
                            insBody.isSound
                            (insFree
                              (insFree
                                insBound
                                nat503Neq502)
                              nat504Neq502))
                          (insFree
                            (insFree
                              insBound
                              nat502Neq501)
                            nat503Neq501))))))))))
    
    def isCauseToInsInterp.arbUn
      (dX: Pair)
      (insBody:
        InsInterp
          ((x, dX), boundVarsEnc) d (exprToEncoding body))
    :
      InsInterp boundVarsEnc d (exprToEncoding (Expr.Un x body))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.arbUn
            (insUnDom
            (insNatEncoding
              (fromNat.isNatEncoding x))
            (insUnDom
              (insExprEncoding
                (exprToEncoding body).property)
              (insArbUn
                boundVarsEnc
                (insPair
                  insBound
                  (insPair
                    (insPair
                      (insNatExpr _ _)
                      (insPair
                        (insFree
                          (insFree
                            insBound
                            nat501Neq500)
                          nat502Neq500)
                        (insFree
                          insBound
                          nat502Neq501)))
                    (insArbUn
                      dX
                      (insCallExpr
                        (insCallExpr
                          (insFree
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insFree
                                      insBody.isSound
                                      nat500NeqInterpretation)
                                    nat501NeqInterpretation)
                                  nat502NeqInterpretation)
                                nat503NeqInterpretation)
                              nat504NeqInterpretation)
                            nat505NeqInterpretation)
                          (insPair
                            (insPair
                              (insFree
                                (insFree
                                  (insFree
                                    (insFree
                                      (insFree
                                        insBound
                                        nat501Neq500)
                                      nat502Neq500)
                                    nat503Neq500)
                                  nat504Neq500)
                                nat505Neq500)
                              (insFree
                                (insFree
                                  insBound
                                  nat504Neq503)
                                nat505Neq503))
                            (insFree
                              (insFree
                                (insFree
                                  insBound
                                  nat503Neq502)
                                nat504Neq502)
                              nat505Neq502)))
                        (insFree
                          (insFree
                            (insFree
                              insBound
                              nat502Neq501)
                            nat503Neq501)
                          nat504Neq501))))))))))
    
    def isCauseToInsInterp.arbIr
      (insBody:
        ∀ dX: Pair,
          InsInterp
            ((x, dX), boundVarsEnc) d (exprToEncoding body))
    :
      InsInterp boundVarsEnc d (exprToEncoding (Expr.Ir x body))
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insFinUn
            interpretationInExprList.arbIr
            (insUnDom
              (insNatEncoding
                (fromNat.isNatEncoding x))
              (insUnDom
                (insExprEncoding
                  (exprToEncoding body).property)
                (insArbUn
                  boundVarsEnc
                  (insPair
                    insBound
                    (insPair
                      (insPair
                        (insNatExpr _ _)
                        (insPair
                          (insFree
                            (insFree
                              insBound
                              nat501Neq500)
                            nat502Neq500)
                          (insFree
                            insBound
                            nat502Neq501)))
                      (insArbIr
                        fun dX =>
                          insCallExpr
                            (insCallExpr
                              (insFree
                                (insFree
                                  (insFree
                                    (insFree
                                      (insFree
                                        (insFree
                                          (insBody dX).isSound
                                          nat500NeqInterpretation)
                                        nat501NeqInterpretation)
                                      nat502NeqInterpretation)
                                    nat503NeqInterpretation)
                                  nat504NeqInterpretation)
                                nat505NeqInterpretation)
                              (insPair
                                (insPair
                                  (insFree
                                    (insFree
                                      (insFree
                                        (insFree
                                          (insFree
                                            insBound
                                            nat501Neq500)
                                          nat502Neq500)
                                        nat503Neq500)
                                      nat504Neq500)
                                    nat505Neq500)
                                  (insFree
                                    (insFree
                                      insBound
                                      nat504Neq503)
                                    nat505Neq503))
                                (insFree
                                  (insFree
                                    (insFree
                                      insBound
                                      nat503Neq502)
                                    nat504Neq502)
                                  nat505Neq502)))
                            (insFree
                              (insFree
                                (insFree
                                  insBound
                                  nat502Neq501)
                                nat503Neq501)
                              nat504Neq501)))))))))
    
    def isCauseToInsInterp
      (isInternalCause:
        IsStrongCause pairSalgebra internalCause d expr)
      (boundVars: List (ValVar Pair))
      (boundVarsSat: internalCause.SatisfiesBoundVars boundVars)
      (cinsIns: CinsInsExternal internalCause boundVars)
      (binsIns: BinsInsExternal internalCause boundVars)
      (boutOut: BoutOutExternal internalCause boundVars)
    :
      InsInterp
        (boundVarsEncoding boundVars)
        d
        (exprToEncoding expr)
    :=
      let isConsistent: internalCause.IsConsistent :=
        fun vv =>
          if hI:
            vv ∈ internalCause.backgroundIns ∧
            vv ∈ internalCause.backgroundOut
          then
            if hB: IsBound boundVars vv.x then
              let ⟨d, isGetBound⟩ := hB
              let boundVarSat := boundVarsSat rfl isGetBound
              boundVarSat.ninBinsBout vv.d
            else
              False.elim
                ((boutOut hI.right hB).isSound
                  (Set3.defLePos _ (binsIns hI.left hB).isSound))
          else
            hI.toOr
      
      match expr with
      | var x =>
        isCauseToInsInterp.var
          isInternalCause
          isConsistent
          boundVars
          boundVarsSat
          cinsIns
      | op pairSignature.Op.zero args =>
        isCauseToInsInterp.exprZero isInternalCause isConsistent
      | op pairSignature.Op.pair args =>
        let ⟨args, ⟨dLeft, dRite, eq⟩, areStrong⟩ :=
        isInternalCause.elimOp (Or.inl isConsistent)
      
        let ihL := isCauseToInsInterp
          (areStrong ArityTwo.zth dLeft)
          boundVars boundVarsSat cinsIns binsIns boutOut
        
        let ihR := isCauseToInsInterp
          (areStrong ArityTwo.fst dRite)
          boundVars boundVarsSat cinsIns binsIns boutOut
        
        eq ▸ isCauseToInsInterp.exprPair ihL ihR
      | un left rite =>
        isInternalCause.elimUn.elim
          (fun isCauseLeft =>
            let ih := isCauseToInsInterp
              isCauseLeft boundVars boundVarsSat
              cinsIns binsIns boutOut
            
            isCauseToInsInterp.exprUnLeft ih)
          (fun isCauseRite =>
            let ih := isCauseToInsInterp
              isCauseRite boundVars boundVarsSat
              cinsIns binsIns boutOut
            
            isCauseToInsInterp.exprUnRite ih)
      | ir left rite =>
        let ⟨isCauseLeft, isCauseRite⟩ := isInternalCause.elimIr
        
        let ihL := isCauseToInsInterp
          isCauseLeft boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihR := isCauseToInsInterp
          isCauseRite boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        isCauseToInsInterp.exprIr ihL ihR
      | cpl expr => sorry
      | ifThen cond expr =>
        let ⟨⟨dC, isCauseCond⟩, isCauseBody⟩ :=
          isInternalCause.elimIfThen
        
        let ihCond := isCauseToInsInterp
          isCauseCond boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihBody := isCauseToInsInterp
          isCauseBody boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        isCauseToInsInterp.exprIfThen ihCond ihBody
      | Un x body =>
        let ⟨dX, isCauseWith⟩ :=
          isInternalCause.elimArbUn isConsistent
        
        let ih :=
          isCauseToInsInterp
            isCauseWith
            (⟨dX, x⟩ :: boundVars)
            boundVarsSat.withBoundSat
            (fun inCinsWith notBound =>
              let xNeq := IsBound.Not.xNotBoundHeadNotEq notBound
              cinsIns
                (Cause.inCinsOfInWithAndNotBound inCinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBinsWith notBound =>
              let xNeq := IsBound.Not.xNotBoundHeadNotEq notBound
              binsIns
                (Cause.inBinsOfInWithAndNotBound inBinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBoutWith notBound =>
              let xNeq := IsBound.Not.xNotBoundHeadNotEq notBound
              boutOut
                (Cause.inBoutOfInWithAndNotBound inBoutWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
        
        isCauseToInsInterp.arbUn dX ih
      | Ir x body =>
        let isCauseWith :=
          isInternalCause.elimArbIr isConsistent
        
        let ih dX :=
          isCauseToInsInterp
            (isCauseWith dX)
            (⟨dX, x⟩ :: boundVars)
            boundVarsSat.withBoundSat
            (fun inCinsWith notBound =>
              let xNeq := IsBound.Not.xNotBoundHeadNotEq notBound
              cinsIns
                (Cause.inCinsOfInWithAndNotBound inCinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBinsWith notBound =>
              let xNeq := IsBound.Not.xNotBoundHeadNotEq notBound
              binsIns
                (Cause.inBinsOfInWithAndNotBound inBinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBoutWith notBound =>
              let xNeq := IsBound.Not.xNotBoundHeadNotEq notBound
              boutOut
                (Cause.inBoutOfInWithAndNotBound inBoutWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
        
        isCauseToInsInterp.arbIr ih
    
    def insTheSetOfInterp
      (ins: InsInterp zero d (IsTheDefListExprPair.getNthExpr x).expr)
    :
      Ins
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (pair (fromNat x) d)
        uniDefList.theSet
    :=
      Ins.isComplete _ _
        (insWfmDefToIns
          (insUnDom
            (insNatEncoding
              (fromNat.isNatEncoding x))
            (insPair
              insBound
              (insCallExpr
                (insWfmDefToIns
                  (insCallExpr
                    ins.isSound
                    insZero))
                (insCallExpr
                  (insTheDefListExpr
                    (IsTheDefListExprPair.getNthExpr x).isNth)
                  (insFree
                    (insFree
                      insBound
                      nat501Neq500)
                    nat502Neq500))))))
    
  end uniSet3
end Pair
