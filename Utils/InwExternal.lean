import UniSet3.Ch9_S0_InternalLe
import Utils.NopeInterp


namespace InwExternal
  open Expr
  open Pair
  open PairExpr
  open uniDefList
  open uniSet3
  
  def causeNat: Cause Pair := {
    contextIns :=
      fun ⟨dC, xC⟩ =>
        xC = uniDefList.nat ∧ dC.IsNatEncoding
    backgroundIns := Set.empty
    backgroundOut := Set.empty
  }
  
  def causeTheSet
    (x: Nat)
    (d: Pair)
  :
    Cause Pair
  :=
    let xthExpr := IsTheDefListExprPair.getNthExpr x
    
    causeNat.union {
      contextIns :=
        fun ⟨dC, xC⟩ =>
          xC = uniDefList.theDefList ∧ IsTheDefListExpr dC ∨
          (And
            (xC = uniDefList.interpretation)
            (dC = pair zero (pair xthExpr.exprEnc d)))
      backgroundIns := Set.empty
      backgroundOut := Set.empty
    }
  
  def causeTheSetIsCause
    (x: Nat)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeTheSet x d)
      (pair (fromNat x) d)
      (theExternalDefList.getDef uniDefList.theSet)
  :=
    let xthExpr := IsTheDefListExprPair.getNthExpr x
    
    fun isSat =>
      let inCinsNat := Or.inl ⟨rfl, fromNat.isNatEncoding x⟩
      let inwNat := isSat.contextInsHold inCinsNat
      
      let inCinsTheDl := Or.inr (Or.inl ⟨rfl, xthExpr.isNth⟩)
      let inwTheDefList := isSat.contextInsHold inCinsTheDl
      
      let inCinsInterp := Or.inr (Or.inr ⟨rfl, rfl⟩)
      let inwInterp := isSat.contextInsHold inCinsInterp
      
      inwUnDom
        inwNat
        (inwPair
          inwBound
          (inwCallExpr
            (inwCallExpr
              inwInterp
              inwZero)
            (inwCallExpr
              inwTheDefList
              (inwFree
                (inwFree
                  inwBound
                  nat501Neq500)
                nat502Neq500))))
  
  
  def boundVar
    (isBoundTo: IsBoundTo boundVars x d)
  :
    InwEdl
      interpretation
      (pair
        (boundVarsEncoding boundVars)
        (pair (exprToEncoding (Expr.var x)) d))
  :=
    inwWfmDefToInw
      (inwFinUn
        interpretationInExprList.exprVar
        (inwUnDom
          (insNatEncoding (fromNat.isNatEncoding x)).toInw
          (inwArbUn
            (boundVarsEncoding
              boundVars)
            (inwPair
              inwBound
              (inwPair
                (inwPair
                  inwZero
                  (inwFree
                    inwBound
                    nat501Neq500))
                (inwUnL _
                  (inwCallExpr
                    (inwCallExpr
                      (inwFree
                        (inwFree
                          (inwFree
                            (inwFree
                              (Ins.toInw
                                (insGetBound
                                  isBoundTo))
                              nat500NeqGetBound)
                            nat501NeqGetBound)
                          nat502NeqGetBound)
                        nat503NeqGetBound)
                      (inwFree
                        (inwFree
                          inwBound
                        nat502Neq501)
                      nat503Neq501))
                    (inwFree
                      (inwFree
                        inwBound
                        nat501Neq500)
                      nat502Neq500))))))))
  
  def causeFreeVar
    (boundVars: List (ValVar Pair))
    (x: Nat)
    (d: Pair)
  :
    Cause Pair
  := {
    contextIns :=
      fun ⟨dC, xC⟩ =>
        xC = uniDefList.nat ∧ dC.IsNatEncoding ∨
        xC = uniDefList.theSet ∧ dC = pair (fromNat x) d
    backgroundIns := Set.empty
    backgroundOut :=
      fun ⟨dC, xC⟩ =>
        And
          (xC = uniDefList.getBound)
          (∃ d, dC = pair (boundVarsEncoding boundVars) (pair x d))
  }
  
  def causeFreeVarIsCause
    (boundVars: List (ValVar Pair))
    (x: Nat)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeFreeVar boundVars x d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.var x))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let inCinsNat := Or.inl ⟨rfl, fromNat.isNatEncoding x⟩
      let inwNat := isSat.contextInsHold inCinsNat
      
      let inCinsTheSet := Or.inr ⟨rfl, rfl⟩
      let inwTheSet := isSat.contextInsHold inCinsTheSet
      
      let inBoutGetBound d := And.intro rfl ⟨d, rfl⟩
      let ninwGetBound d := isSat.backgroundOutHold (inBoutGetBound d)
      
      inwFinUn
        interpretationInExprList.exprVar
        (inwUnDom
          inwNat
          (inwArbUn
            (boundVarsEncoding
              boundVars)
            (inwPair
              inwBound
              (inwPair
                (inwPair
                  inwZero
                  (inwFree
                    inwBound
                    nat501Neq500))
                (inwUnR _
            (inwIfThen
              (inwCpl _ fun ins =>
                let ⟨⟨dBound, ins⟩, insAny⟩ := insIfThenElim ins
                -- W/o this, Lean errors bc cannot synthetize the type
                have: Expr.Ins pairSalgebra _ _ _ zero := insAny
                let ins := insCallElimBound ins rfl nat502Neq500
                let ins := insCallElimBound ins rfl nat503Neq501
                ninwGetBound dBound ins)
              (inwCallExpr
                (inwFree
                  (inwFree
                    (inwFree
                      inwTheSet
                      nat500NeqTheSet)
                    nat501NeqTheSet)
                  nat502NeqTheSet)
                (inwFree
                  (inwFree
                    inwBound
                    nat501Neq500)
                  nat502Neq500))))))))
  
  
  def causeExpr: Cause Pair :=
    {
      contextIns :=
        fun ⟨dC, xC⟩ =>
          xC = uniDefList.exprEncoding ∧ IsExprEncoding dC
      backgroundIns := Set.empty
      backgroundOut := Set.empty
    }
  
  def setInterp
    (boundVars: List (ValVar Pair))
    (expr: Expr)
    (d: Pair)
  :
    Set (ValVar Pair)
  :=
    let bvEnc := boundVarsEncoding boundVars
    fun ⟨dC, xC⟩ =>
      And
        (xC = uniDefList.interpretation)
        (dC = pair bvEnc (pair (exprToEncoding expr) d))
  
  def causeInterp
    (boundVars: List (ValVar Pair))
    (expr: Expr)
    (d: Pair)
  :
    Cause Pair
  := {
    contextIns := setInterp boundVars expr d
    backgroundIns := Set.empty
    backgroundOut := Set.empty
  }
  
  def causeInterpBout
    (boundVars: List (ValVar Pair))
    (expr: Expr)
    (d: Pair)
  :
    Cause Pair
  := {
    contextIns := Set.empty
    backgroundIns := Set.empty
    backgroundOut := setInterp boundVars expr d
  }
  
  def causePair
    (boundVars: List (ValVar Pair))
    (left rite: Expr)
    (dLeft dRite: Pair)
  :
    Cause Pair
  :=
    causeExpr.union
      (Cause.union
        (causeInterp boundVars left dLeft)
        (causeInterp boundVars rite dRite))
  
  def causeUn
    (boundVars: List (ValVar Pair))
    (expr: Expr)
    (d: Pair)
  :
    Cause Pair
  :=
    causeExpr.union (causeInterp boundVars expr d)
  
  def causeIr
    (boundVars: List (ValVar Pair))
    (left rite: Expr)
    (d: Pair)
  :
    Cause Pair
  :=
    causeExpr.union
      (Cause.union
        (causeInterp boundVars left d)
        (causeInterp boundVars rite d))
  
  def causeCpl
    (boundVars: List (ValVar Pair))
    (expr: Expr)
    (d: Pair)
  :
    Cause Pair
  :=
    causeExpr.union (causeInterpBout boundVars expr d)
  
  def causeIfThen
    (boundVars: List (ValVar Pair))
    (dC: Pair)
    (cond body: Expr)
    (d: Pair)
  :
    Cause Pair
  :=
    causeExpr.union
      (Cause.union
        (causeInterp boundVars cond dC)
        (causeInterp boundVars body d))
  
  def causeArbUn
    (boundVars: List (ValVar Pair))
    (x: Nat)
    (dX: Pair)
    (body: Expr)
    (d: Pair)
  :
    Cause Pair
  :=
    causeExpr.union
      (Cause.union
        causeNat
        (causeInterp (⟨dX, x⟩ :: boundVars) body d))
  
  def causeArbIr
    (boundVars: List (ValVar Pair))
    (x: Nat)
    (body: Expr)
    (d: Pair)
  :
    Cause Pair
  :=
    causeExpr.union
      (Cause.union
        causeNat
        (Cause.arbUn fun dX =>
          causeInterp (⟨dX, x⟩ :: boundVars) body d))
  
  
  def isCauseZero
    (boundVars: List (ValVar Pair))
    {cause: Cause Pair}
  :
    IsWeakCause
      pairSalgebra
      cause
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding zeroExpr)
          zero))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun _ =>
      inwFinUn
        interpretationInExprList.exprZero
        (inwArbUn
          (boundVarsEncoding
            boundVars)
          (inwPair
            inwBound
            (inwPair
              (inwPair
                (inwNatExpr _ _ _)
                inwZero)
              inwZero)))
  
  def isCausePair
    (boundVars: List (ValVar Pair))
    (left rite: Expr)
    (dLeft dRite: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causePair boundVars left rite dLeft dRite)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (pairExpr left rite))
          (pair dLeft dRite)))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let isExprEncL := (exprToEncoding left).property
      let inCinsExprL := Or.inl ⟨rfl, isExprEncL⟩
      let inwExprL := isSat.contextInsHold inCinsExprL
      
      let isExprEncR := (exprToEncoding rite).property
      let inCinsExprR := Or.inl ⟨rfl, isExprEncR⟩
      let inwExprR := isSat.contextInsHold inCinsExprR
      
      let inCinsL := Or.inr (Or.inl ⟨rfl, rfl⟩)
      let inwL := isSat.contextInsHold inCinsL
      
      let inCinsR := Or.inr (Or.inr ⟨rfl, rfl⟩)
      let inwR := isSat.contextInsHold inCinsR
      
      inwFinUn
        interpretationInExprList.exprPair
        (inwUnDom
          inwExprL
          (inwUnDom
            inwExprR
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwPair
                    (inwCallExpr
                      (inwCallExpr
                        inwL
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          (inwFree
                            inwBound
                            nat501Neq500)
                          nat502Neq500)
                        nat503Neq500))
                    (inwCallExpr
                      (inwCallExpr
                        inwR
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          inwBound
                          nat502Neq501)
                        nat503Neq501))))))))
  
  def isCauseUnL
    (boundVars: List (ValVar Pair))
    (left rite: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeUn boundVars left d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.un left rite))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let inCinsExprL := Or.inl ⟨rfl, (exprToEncoding left).property⟩
      let inwExprL := isSat.contextInsHold inCinsExprL
      
      let inCinsExprR := Or.inl ⟨rfl, (exprToEncoding rite).property⟩
      let inwExprR := isSat.contextInsHold inCinsExprR
      
      let inCinsL := Or.inr ⟨rfl, rfl⟩
      let inwL := isSat.contextInsHold inCinsL
      
      inwFinUn
        interpretationInExprList.exprUn
        (inwUnDom
          inwExprL
          (inwUnDom
            inwExprR
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwUnL _
                    (inwCallExpr
                      (inwCallExpr
                        (inwFree
                          (inwFree
                            (inwFree
                              (inwFree
                                (inwFree
                                  inwL
                                  nat500NeqInterpretation)
                                nat501NeqInterpretation)
                              nat502NeqInterpretation)
                            nat503NeqInterpretation)
                          nat504NeqInterpretation)
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          (inwFree
                            inwBound
                            nat501Neq500)
                          nat502Neq500)
                        nat503Neq500))))))))
  
  def isCauseUnR
    (boundVars: List (ValVar Pair))
    (left rite: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeUn boundVars rite d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.un left rite))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let inCinsExprL := Or.inl ⟨rfl, (exprToEncoding left).property⟩
      let inwExprL := isSat.contextInsHold inCinsExprL
      
      let inCinsExprR := Or.inl ⟨rfl, (exprToEncoding rite).property⟩
      let inwExprR := isSat.contextInsHold inCinsExprR
      
      let inCinsL := Or.inr ⟨rfl, rfl⟩
      let inwL := isSat.contextInsHold inCinsL
      
      inwFinUn
        interpretationInExprList.exprUn
        (inwUnDom
          inwExprL
          (inwUnDom
            inwExprR
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwUnR _
                    (inwCallExpr
                      (inwCallExpr
                        (inwFree
                          (inwFree
                            (inwFree
                              (inwFree
                                (inwFree
                                  inwL
                                  nat500NeqInterpretation)
                                nat501NeqInterpretation)
                              nat502NeqInterpretation)
                            nat503NeqInterpretation)
                          nat504NeqInterpretation)
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          inwBound
                          nat502Neq501)
                        nat503Neq501))))))))
  
  def isCauseIr
    (boundVars: List (ValVar Pair))
    (left rite: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeIr boundVars left rite d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.ir left rite))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let isExprEncL := (exprToEncoding left).property
      let inCinsExprL := Or.inl ⟨rfl, isExprEncL⟩
      let inwExprL := isSat.contextInsHold inCinsExprL
      
      let isExprEncR := (exprToEncoding rite).property
      let inCinsExprR := Or.inl ⟨rfl, isExprEncR⟩
      let inwExprR := isSat.contextInsHold inCinsExprR
      
      let inCinsL := Or.inr (Or.inl ⟨rfl, rfl⟩)
      let inwL := isSat.contextInsHold inCinsL
      
      let inCinsR := Or.inr (Or.inr ⟨rfl, rfl⟩)
      let inwR := isSat.contextInsHold inCinsR
      
      inwFinUn
        interpretationInExprList.exprIr
        (inwUnDom
          inwExprL
          (inwUnDom
            inwExprR
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwIr
                    (inwCallExpr
                      (inwCallExpr
                        inwL
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          (inwFree
                            inwBound
                            nat501Neq500)
                          nat502Neq500)
                        nat503Neq500))
                    (inwCallExpr
                      (inwCallExpr
                        inwR
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          inwBound
                          nat502Neq501)
                        nat503Neq501))))))))
  
  def isCauseCpl
    (boundVars: List (ValVar Pair))
    (expr: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeCpl boundVars expr d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.cpl expr))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let isExprEnc := (exprToEncoding expr).property
      let inCinsExpr := Or.inl ⟨rfl, isExprEnc⟩
      let inwExpr := isSat.contextInsHold inCinsExpr
      
      let inBoutExpr := Or.inr ⟨rfl, rfl⟩
      let ninsExpr := isSat.backgroundOutHold inBoutExpr
      
      inwFinUn
        (interpretationInExprList.exprCpl)
        (inwUnDom
          inwExpr
          (inwArbUn
            (boundVarsEncoding
              boundVars)
            (inwPair
              inwBound
              (inwPair
                (inwPair
                  (inwNatExpr _ _ _)
                  (inwFree
                    inwBound
                    nat502Neq500))
                (inwCpl _
                  fun ins =>
                    let ins := insCallElimBound ins rfl nat503Neq500
                    let ins := insCallElimBound ins rfl nat504Neq502
                    ninsExpr ins)))))
  
  def isCauseIfThen
    (boundVars: List (ValVar Pair))
    (dC: Pair)
    (cond body: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeIfThen boundVars dC cond body d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.ifThen cond body))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let isExprEncCond := (exprToEncoding cond).property
      let inCinsExprCond := Or.inl ⟨rfl, isExprEncCond⟩
      let inwExprCond := isSat.contextInsHold inCinsExprCond
      
      let isExprEncBody := (exprToEncoding body).property
      let inCinsExprBody := Or.inl ⟨rfl, isExprEncBody⟩
      let inwExprBody := isSat.contextInsHold inCinsExprBody
      
      let inCinsCond := Or.inr (Or.inl ⟨rfl, rfl⟩)
      let inwCond := isSat.contextInsHold inCinsCond
      
      let inCinsBody := Or.inr (Or.inr ⟨rfl, rfl⟩)
      let inwBody := isSat.contextInsHold inCinsBody
      
      inwFinUn
        interpretationInExprList.exprIfThen
        (inwUnDom
          inwExprCond
          (inwUnDom
            inwExprBody
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwIfThen
                    (inwCallExpr
                      (inwCallExpr
                        inwCond
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          (inwFree
                            inwBound
                            nat501Neq500)
                          nat502Neq500)
                        nat503Neq500))
                    (inwCallExpr
                      (inwCallExpr
                        inwBody
                        (inwFree
                          (inwFree
                            inwBound
                            nat503Neq502)
                          nat504Neq502))
                      (inwFree
                        (inwFree
                          inwBound
                          nat502Neq501)
                        nat503Neq501))))))))
  
  def isCauseArbUn
    (boundVars: List (ValVar Pair))
    (x: Nat)
    (dX: Pair)
    (body: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeArbUn boundVars x dX body d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.Un x body))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let isExprEncBody := (exprToEncoding body).property
      let inCinsExprBody := Or.inl ⟨rfl, isExprEncBody⟩
      let inwExprBody := isSat.contextInsHold inCinsExprBody
      
      let inCinsNat :=
        Or.inr (Or.inl ⟨rfl, fromNat.isNatEncoding x⟩)
      let inwNat := isSat.contextInsHold inCinsNat
      
      let inCinsBody := Or.inr (Or.inr ⟨rfl, rfl⟩)
      let inwBody := isSat.contextInsHold inCinsBody
      
      inwFinUn
        interpretationInExprList.arbUn
        (inwUnDom
          inwNat
          (inwUnDom
            inwExprBody
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwArbUn
                    dX
                    (inwCallExpr
                      (inwCallExpr
                        (inwFree
                          (inwFree
                            (inwFree
                              (inwFree
                                (inwFree
                                  (inwFree
                                    inwBody
                                    nat500NeqInterpretation)
                                  nat501NeqInterpretation)
                                nat502NeqInterpretation)
                              nat503NeqInterpretation)
                            nat504NeqInterpretation)
                          nat505NeqInterpretation)
                        (inwPair
                          (inwPair
                            (inwFree
                              (inwFree
                                (inwFree
                                  (inwFree
                                    (inwFree
                                      inwBound
                                      nat501Neq500)
                                    nat502Neq500)
                                  nat503Neq500)
                                nat504Neq500)
                              nat505Neq500)
                            (inwFree
                              (inwFree
                                inwBound
                                nat504Neq503)
                              nat505Neq503))
                          (inwFree
                            (inwFree
                              (inwFree
                                inwBound
                                nat503Neq502)
                              nat504Neq502)
                            nat505Neq502)))
                      (inwFree
                        (inwFree
                          (inwFree
                            inwBound
                            nat502Neq501)
                          nat503Neq501)
                        nat504Neq501))))))))
  
  def isCauseArbIr
    (boundVars: List (ValVar Pair))
    (x: Nat)
    (body: Expr)
    (d: Pair)
  :
    IsWeakCause
      pairSalgebra
      (causeArbIr boundVars x body d)
      (pair
        (boundVarsEncoding boundVars)
        (pair
          (exprToEncoding (Expr.Ir x body))
          d))
      (theExternalDefList.getDef uniDefList.interpretation)
  :=
    fun isSat =>
      let isExprEncBody := (exprToEncoding body).property
      let inCinsExprBody := Or.inl ⟨rfl, isExprEncBody⟩
      let inwExprBody := isSat.contextInsHold inCinsExprBody
      
      let inCinsNat :=
        Or.inr (Or.inl ⟨rfl, fromNat.isNatEncoding x⟩)
      let inwNat := isSat.contextInsHold inCinsNat
      
      let inCinsBody dX := Or.inr (Or.inr ⟨dX, rfl, rfl⟩)
      let inwBody dX := isSat.contextInsHold (inCinsBody dX)
      
      inwFinUn
        interpretationInExprList.arbIr
        (inwUnDom
          inwNat
          (inwUnDom
            inwExprBody
            (inwArbUn
              (boundVarsEncoding
                boundVars)
              (inwPair
                inwBound
                (inwPair
                  (inwPair
                    (inwNatExpr _ _ _)
                    (inwPair
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500)
                      (inwFree
                        inwBound
                        nat502Neq501)))
                  (inwArbIr
                    fun dX =>
                      inwCallExpr
                        (inwCallExpr
                          (inwFree
                            (inwFree
                              (inwFree
                                (inwFree
                                  (inwFree
                                    (inwFree
                                      (inwBody dX)
                                      nat500NeqInterpretation)
                                    nat501NeqInterpretation)
                                  nat502NeqInterpretation)
                                nat503NeqInterpretation)
                              nat504NeqInterpretation)
                            nat505NeqInterpretation)
                          (inwPair
                            (inwPair
                              (inwFree
                                (inwFree
                                  (inwFree
                                    (inwFree
                                      (inwFree
                                        inwBound
                                        nat501Neq500)
                                      nat502Neq500)
                                    nat503Neq500)
                                  nat504Neq500)
                                nat505Neq500)
                              (inwFree
                                (inwFree
                                  inwBound
                                  nat504Neq503)
                                nat505Neq503))
                            (inwFree
                              (inwFree
                                (inwFree
                                  inwBound
                                  nat503Neq502)
                                nat504Neq502)
                              nat505Neq502)))
                        (inwFree
                          (inwFree
                            (inwFree
                              inwBound
                              nat502Neq501)
                            nat503Neq501)
                          nat504Neq501)))))))
  
end InwExternal
