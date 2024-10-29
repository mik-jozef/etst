import Utils.CauseSatisfiesBoundVars
import Utils.IsStrongCause
import Utils.NopeInterp

open Expr
open Pair
open Pair.uniSet3
open PairExpr

def CinsInsExternal
  (internalCause: Cause Pair)
  (boundVars: List (ValVar Pair))
:=
  ∀ {d x},
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
  ∀ {d x},
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
  ∀ {d x},
    ⟨d, x⟩ ∈ internalCause.backgroundOut →
    ¬IsBound boundVars x →
    Out
      pairSalgebra
      uniDefList.theExternalDefList.toDefList
      (Pair.pair x d)
      uniDefList.theSet

def InsInterp
  (boundVars: List (ValVar Pair))
  (d: Pair)
  (expr: Expr pairSignature)
:=
  Ins
    pairSalgebra
    uniDefList.theExternalDefList.toDefList
    (InterpEnc boundVars expr d)
    uniDefList.interpretation

def InsInterp.var
  (isInternalCause:
    IsStrongCause pairSalgebra internalCause d (Expr.var x))
  (isConsistent: internalCause.IsConsistent)
  (boundVars: List (ValVar Pair))
  (boundVarsSat: internalCause.SatisfiesBoundVars boundVars)
  (cinsIns: CinsInsExternal internalCause boundVars)
:
  InsInterp boundVars d (var x)
:=
  let insUn:
    Expr.Ins2
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
          have: Expr.Inw2 pairSalgebra _ anyExpr zero := inwAny
          let inw := inwCallElimBound inw rfl nat502Neq500
          let inw := inwCallElimBound inw rfl nat503Neq501
        let insGetBound := Inw.toInsGetBound inw
        h ⟨boundVal, Inw.toIsGetBound insGetBound.toInw⟩
      
      insUnR _
        (insIfThen
          (insCpl _ ninw)
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

def InsInterp.exprZero
  (isInternalCause:
    IsStrongCause pairSalgebra internalCause d zeroExpr)
  (isConsistent: internalCause.IsConsistent)
:
  InsInterp boundVars d zeroExpr
:=
  let dEq := isInternalCause.elimZeroExpr isConsistent
  
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
              (insNatExpr _ _ _)
              insZero)
            (dEq ▸ insZero))))))

def InsInterp.exprPair
  (insLeft: InsInterp boundVars dLeft left)
  (insRite: InsInterp boundVars dRite rite)
:
  InsInterp boundVars (pair dLeft dRite) (pairExpr left rite)
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
              (boundVarsEncoding
                boundVars)
              (insPair
                insBound
                (insPair
                  (insPair
                    (insNatExpr _ _ _)
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

def InsInterp.exprUnLeft
  (insLeft: InsInterp boundVars d left)
:
  InsInterp boundVars d (un left rite)
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
              (boundVarsEncoding
                boundVars)
              (insPair
                insBound
                (insPair
                  (insPair
                    (insNatExpr _ _ _)
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

def InsInterp.exprUnRite
  (insRite: InsInterp boundVars d rite)
:
  InsInterp boundVars d (un left rite)
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
              (boundVarsEncoding
                boundVars)
              (insPair
                insBound
                (insPair
                  (insPair
                    (insNatExpr _ _ _)
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

def InsInterp.exprIr
  (insLeft: InsInterp boundVars d left)
  (insRite: InsInterp boundVars d rite)
:
  InsInterp boundVars d (ir left rite)
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
              (boundVarsEncoding
                boundVars)
              (insPair
                insBound
                (insPair
                  (insPair
                    (insNatExpr _ _ _)
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

-- TODO? InsInterp.exprCpl

def InsInterp.exprIfThen
  {cond}
  (insCond: InsInterp boundVars dC cond)
  (insBody: InsInterp boundVars d body)
:
  InsInterp boundVars d (ifThen cond body)
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
              (boundVarsEncoding
                boundVars)
              (insPair
                insBound
                (insPair
                  (insPair
                    (insNatExpr _ _ _)
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

def InsInterp.arbUn
  (dX: Pair)
  (insBody:
    InsInterp (⟨dX, x⟩ :: boundVars) d body)
:
  InsInterp boundVars d (Expr.Un x body)
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
            (boundVarsEncoding
              boundVars)
            (insPair
              insBound
              (insPair
                (insPair
                  (insNatExpr _ _ _)
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

def InsInterp.arbIr
  (insBody:
    ∀ dX: Pair,
      InsInterp (⟨dX, x⟩ :: boundVars) d body)
:
  InsInterp boundVars d (Expr.Ir x body)
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
              (boundVarsEncoding
                boundVars)
              (insPair
                insBound
                (insPair
                  (insPair
                    (insNatExpr _ _ _)
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
