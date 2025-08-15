import old.Utils.CauseSatisfiesBoundVars
import old.Utils.IsStrongCause
import old.Utils.NopeInterp

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
      let ⟨dAlias, isBoundTo⟩ := h
      let boundVarSat := boundVarsSat isBoundTo
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
                      isBoundTo)
                    nat500NeqGetBound)
                  nat501NeqGetBound)
                nat502NeqGetBound)
              nat503NeqGetBound)
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
      insUnR _
        (insIr
          (insCondFull fun dE =>
            insCpl _ fun inw =>
              let inw := inwCallElimBound inw rfl nat502Neq500
              let inw := inwCallElimBound inw rfl nat503Neq501
              let insGetBound := Inw.toInsGetBound inw
              h ⟨dE, Inw.toIsBoundTo insGetBound.toInw⟩)
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
  InsInterp boundVars d (unExpr left rite)
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
  InsInterp boundVars d (unExpr left rite)
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
  InsInterp boundVars d (irExpr left rite)
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

def InsInterp.exprCpl
  (notPos:
    Not
      (Set3.posMem
        (uniDefList.theExternalWfm uniDefList.interpretation)
        (InterpEnc boundVars expr d)))
:
  InsInterp boundVars d expr.cpl
:=
  Ins.isComplete _ _
    (insWfmDefToIns
      (insFinUn
        (interpretationInExprList.exprCpl)
        (insUnDom
          (insExprEncoding
            (exprToEncoding expr).property)
          (insArbUn
            (boundVarsEncoding
              boundVars)
            (insPair
              insBound
              (insPair
                (insPair
                  (insNatExpr _ _ _)
                  (insFree
                    insBound
                    nat502Neq500))
                (insCpl _
                  fun inw =>
                    let inw := inwCallElimBound inw rfl nat503Neq500
                    let inw := inwCallElimBound inw rfl nat504Neq502
                    notPos inw)))))))

def InsInterp.exprCondSome
  (insExpr: InsInterp boundVars dE expr)
:
  InsInterp boundVars d (condSomeExpr expr)
:=
  Ins.isComplete _ _
    (insWfmDefToIns
      (insFinUn
        interpretationInExprList.exprCondSome
        (insUnDom
          (insExprEncoding
            (exprToEncoding expr).property)
          (insArbUn
            (boundVarsEncoding
              boundVars)
            (insPair
              insBound
              (insPair
                (insPair
                  (insNatExpr _ _ _)
                  (insFree
                    insBound
                    nat502Neq500))
                (insCondSome
                  (insCallExpr
                    (insCallExpr
                      insExpr.isSound
                      (insFree
                        (insFree
                          insBound
                          nat503Neq502)
                        nat504Neq502))
                    (insFree
                      (insFree
                        insBound
                        nat502Neq500)
                      nat503Neq500)))))))))

def InsInterp.exprCondFull
  (insExpr: (dE: pairSalgebra.D) → InsInterp boundVars dE expr)
:
  InsInterp boundVars d (condFullExpr expr)
:=
  Ins.isComplete _ _
    (insWfmDefToIns
      (insFinUn
        interpretationInExprList.exprCondFull
        (insUnDom
          (insExprEncoding
            (exprToEncoding expr).property)
          (insArbUn
            (boundVarsEncoding
              boundVars)
            (insPair
              insBound
              (insPair
                (insPair
                  (insNatExpr _ _ _)
                  (insFree
                    insBound
                    nat502Neq500))
                (insCondFull fun dE =>
                  (insCallExpr
                    (insCallExpr
                      (insExpr dE).isSound
                      (insFree
                        (insFree
                          insBound
                          nat503Neq502)
                        nat504Neq502))
                    (insFree
                      (insFree
                        insBound
                        nat502Neq500)
                      nat503Neq500)))))))))

def InsInterp.arbUn
  (dX: Pair)
  (insBody:
    InsInterp (⟨dX, x⟩ :: boundVars) d body)
:
  InsInterp boundVars d (Expr.arbUn x body)
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
  InsInterp boundVars d (Expr.arbIr x body)
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
