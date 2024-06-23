import Utils.DefListDefEq
import Utils.LfpLeOfOpLe
import UniSet3.DefListToEncoding
import UniSet3.TheSet3


namespace Pair
  namespace uniSet3
    open uniDefList
    
    noncomputable def theDefListInternal.getDef
      (n: Nat)
    :
      Expr pairSignature
    :=
      encodingToExpr
        (IsTheDefListExprPair.getNthExpr n).expr

    noncomputable def theDefListInternal:
      DefList pairSignature
    := {
      getDef := theDefListInternal.getDef
    }
    
    def theDefListInternal.inListOfIsDefList
      (isInDl: IsTheDefListExprPair (fromNat i) exprEnc)
      (eqEnc: exprEnc = exprToEncoding expr)
    :
      expr = theDefListInternal.getDef i
    :=
      by
        unfold theDefListInternal.getDef;
        exact
          IsTheDefListExprPair.getNthExpr.eq isInDl rfl ▸
          eqEnc ▸
          (encodingToExpr.isInverse expr).symm
    
    def IsIncrVarsExprPair.incrVarsEqMapVars:
      incrVars (exprToEncoding expr)
        =
      exprToEncoding (Expr.mapVars Nat.succ expr)
    :=
      open pairSignature in
      open IsExprEncoding.Bin in
      open IsExprEncoding.Quantifier in
      match expr with
      | Expr.var _ => incrVars.eq0 _ ▸ rfl
      | Expr.op Op.zero _args => incrVars.eq1 _ ▸ rfl
      | Expr.op Op.pair _args =>
        show (pair _ _) = _ from
          congr rfl
            (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.un _ _ =>
        show (pair _ _) = _ from
          congr rfl (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.ir _ _ =>
        incrVars.eqBin (Is4 rfl) _ _ ▸
        congr rfl (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.cpl _ =>
        incrVars.eqCpl _ ▸ congr rfl incrVarsEqMapVars
      | Expr.ifThen _ _ =>
        incrVars.eqBin (Is6 rfl) _ _ ▸
        congr rfl (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.Un _ _ =>
        incrVars.eqQuant (Is7 rfl) _ _ ▸
        congrBin rfl rfl (congr rfl incrVarsEqMapVars)
      | Expr.Ir _ _ =>
        incrVars.eqQuant (Is8 rfl) _ _ ▸
        congrBin rfl rfl (congr rfl incrVarsEqMapVars)
    
    def IsIncrVarsExprPair.shiftVarsEqMapVars.incr
      (eqN:
        shiftVars n (exprToEncoding expr)
          =
        exprToEncoding (Expr.mapVars (n + ·) expr))
    :
      shiftVars n.succ (exprToEncoding expr)
        =
      exprToEncoding (Expr.mapVars (n.succ + ·) expr)
    :=
      open pairSignature in
      open IsIncrVarsExprPair in
      show
        incrVars (shiftVars n (exprToEncoding expr))
          =
        exprToEncoding (Expr.mapVars (n.succ + ·) expr)
      from
        eqN ▸
        incrVarsEqMapVars ▸
        Expr.mapVars.eqOfIsComposition
          _ _ _ _ (Nat.succ_add n) ▸
        rfl
    
    def IsIncrVarsExprPair.shiftVarsEqMapVars:
      shiftVars n (exprToEncoding expr)
        =
      exprToEncoding (Expr.mapVars (n + ·) expr)
    :=
      match n with
      | Nat.zero =>
        let eqMapVars :=
          Expr.mapVars.eqOfIsId expr (0 + ·) Nat.zero_add
        
        eqMapVars.symm ▸ rfl
      | Nat.succ _ =>
        shiftVarsEqMapVars.incr shiftVarsEqMapVars
    
    
    noncomputable def wfmInternal :=
      theDefListInternal.wellFoundedModel pairSalgebra
    
    def theDefListInternal.hasAllDefinable
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x, s3 = wfmInternal x
    :=
      let ⟨dl, x, sEq⟩ := isDef
      
      let ⟨dlSliceEnd, gtBounds⟩ := dl.isFinBounded x
      
      -- Potential for Lean improvement detected.
      -- let ⟨dlSliceEncoding, isDefSlice, eqAtSlice⟩ :=
      let dlEnc :=
        defListToEncoding dl.toDefList 0 dlSliceEnd
      let dlSliceEncoding := dlEnc.1
      let isDefSlice := dlEnc.2
      let eqAtSlice := dlEnc.3
      
      let ⟨iStart, eqAt⟩ := IsTheDefListExprPair.getIndexOf isDefSlice
      
      let dlSliceLengthEq:
        dlSliceEncoding.arrayLength = dlSliceEnd
      :=
        defListToEncoding.lengthEq dl.toDefList 0 dlSliceEnd
      
      let eq :=
        DefList.eqDefsToEqSets
          dl.toDefList
          theDefListInternal
          pairSalgebra
          (fun i => iStart + i)
          (fun i => DefList.DependsOn dl.getDef x i)
          Nat.add_left_cancel
          (fun ⟨i, isUsed⟩ =>
            let withinBounds: i < dlSliceEncoding.arrayLength :=
              dlSliceLengthEq ▸ gtBounds isUsed
            
            let eqInSlice:
              dlSliceEncoding.arrayAt i
                =
              Pair.exprToEncoding (dl.getDef i)
            := by
              conv => rhs; rw [(Nat.zero_add i).symm]; rfl
              exact eqAtSlice i withinBounds
            
            let isDefList := eqAt eqInSlice
            
            inListOfIsDefList
              isDefList
              IsIncrVarsExprPair.shiftVarsEqMapVars)
          (fun ⟨xM, isMapped⟩ ⟨xF, isFree⟩ => isMapped.push isFree)
          x
          (DefList.DependsOn.Refl x)
      
      ⟨iStart + x, by unfold wfmInternal; exact eq ▸ sEq⟩
    
    
    def theInternalValuation.interpretationsEqualGeneral
      (b c: Valuation Pair)
      (x: Nat)
      (bEqExceptSet:
        ∀ x, x ≠ theSet → b x = wfModel x)
      (cEqExceptSet:
        ∀ x, x ≠ theSet → c x = wfModel x)
    :
      (Set3.pairCallJust
        ((defList.getDef theSet).interpretation pairSalgebra b c)
        (fromNat x))
        =
      (theDefListInternal.interpretation
        pairSalgebra
        (internalOfExternal b)
        (internalOfExternal c)
        x)
    :=
      sorry
    
    def theInternalValuation.interpretationsEqual
      (x: Nat)
    :
      Set3.pairCallJust uniSet3 (fromNat x)
        =
      Expr.interpretation
        pairSalgebra
        theInternalValuation
        theInternalValuation
        (encodingToExpr (IsTheDefListExprPair.getNthExpr x).expr)
    :=
      Set3.ord.standard.le_antisymm _ _ ⟨
        fun _ => inDefNthOfInsTheSet,
        fun _ => inPosNthOfInwTheSet,
      ⟩ ⟨
        fun _ => insTheSetOfInDefNth,
        fun _ => inwTheSetOfInPosNth,
      ⟩
    
    def theInternalValuation.isFixedPointOpC:
      IsFixedPoint
        (operatorC pairSalgebra theDefListInternal theInternalValuation)
        theInternalValuation
    :=
      funext interpretationsEqual
    
    def theInternalValuation.interpretationLeStd
      (isLfpC:
        IsLfp
          (Valuation.ord.standard Pair)
          (operatorC pairSalgebra defList.toDefList wfModel)
          lfpC)
      (cLe: c ≤ lfpC)
    :
      internalOfExternal
        (defList.interpretation pairSalgebra wfModel c)
        ≤
      theDefListInternal.interpretation
        pairSalgebra
        theInternalValuation
        (internalOfExternal c)
    :=
      sorry
    
    def theInternalValuation.isLeCLfp:
      (Valuation.ord.standard Pair).le
        theInternalValuation
        (operatorC.lfp pairSalgebra
          theDefListInternal
          theInternalValuation).val
    :=
      let b := wfModel
      
      let opCB :=
        operatorC.lfp pairSalgebra defList.toDefList b
      
      let eqC: b = opCB.val :=
        (operatorB.lfp pairSalgebra defList.toDefList).property.isMember
      
      let eqL:
        internalOfExternal b = internalOfExternal opCB.val
      :=
        congr rfl eqC

      by
        conv =>
          lhs;
          unfold
            internalOfExternal
            theInternalValuation
          rw [eqL]
        exact
          lfp.leOfOpLeMappedSameOrd
            (Valuation.ord.standard.isChainComplete Pair)
            (Valuation.ord.standard.isChainComplete Pair)
            (operatorC pairSalgebra defList.toDefList b)
            (operatorC pairSalgebra theDefListInternal (internalOfExternal b))
            (operatorC.isMonotonic pairSalgebra _ _)
            (operatorC.isMonotonic pairSalgebra _ _)
            internalOfExternal
            (fun isLfpC cLe =>
              interpretationLeStd isLfpC cLe)
            internalOfExternal.preservesSupremaStd
    
    def theInternalValuation.isFixedPointOpB:
      IsFixedPoint
        (operatorB pairSalgebra theDefListInternal)
        theInternalValuation
    :=
      let lfp :=
        operatorC.lfp pairSalgebra theDefListInternal theInternalValuation
      
      let isGe := lfp.property.isLeMember isFixedPointOpC
      
      (Valuation.ord.standard Pair).le_antisymm _ _ isLeCLfp isGe
    
    def theInternalValuation.isGeWfm:
      (Valuation.ord.approximation Pair).le wfmInternal theInternalValuation
    :=
      let isLfp :=
        DefList.wellFoundedModel.isLfp pairSalgebra theDefListInternal
      
      isLfp.isLeMember theInternalValuation.isFixedPointOpB
    
    
    def theInternalValuation.interpretationLeApx
      (isLfpB:
        IsLfp
          (Valuation.ord.approximation Pair)
          (operatorB pairSalgebra defList.toDefList) lfpB)
      (bLe: b ⊑ lfpB)
      (isLfpC:
        IsLfp
          (Valuation.ord.standard Pair)
          (operatorC pairSalgebra defList.toDefList b) lfpC)
      (cLe: c ≤ lfpC)
    :
      internalOfExternal
        (defList.interpretation pairSalgebra b c)
        ⊑
      theDefListInternal.interpretation
        pairSalgebra (internalOfExternal b) (internalOfExternal c)
    :=
      sorry
    
    def theInternalValuation.isLeWfmWithPartialB
      (isLfpB:
        IsLfp
          (Valuation.ord.approximation Pair)
          (operatorB pairSalgebra defList.toDefList) lfpB)
      (bLe: b ⊑ lfpB)
    :
      (Valuation.ord.approximation Pair).le
        (internalOfExternal
          (Subtype.val
            (operatorC.lfp pairSalgebra defList.toDefList b)))
        (Subtype.val
          (operatorC.lfp
            pairSalgebra
            theDefListInternal
            (internalOfExternal b)))
    :=
      lfp.leOfOpLeMapped
        (Valuation.ord.standard.isChainComplete Pair)
        (Valuation.ord.standard.isChainComplete Pair)
        (operatorC pairSalgebra defList.toDefList b)
        (operatorC pairSalgebra theDefListInternal (internalOfExternal b))
        (operatorC.isMonotonic pairSalgebra _ _)
        (operatorC.isMonotonic pairSalgebra _ _)
        internalOfExternal
        (operatorC.isMonotonic.approximation pairSalgebra _ _)
        (fun isLfpC cLe =>
          interpretationLeApx isLfpB bLe isLfpC cLe)
        internalOfExternal.preservesSupremaStd
        Valuation.ord.standard.supPreservesLeApx
    
    def theInternalValuation.isLeWfm:
      (Valuation.ord.approximation Pair).le theInternalValuation wfmInternal
    :=
      lfp.leOfOpLeMappedSameOrd
        (Valuation.ord.approximation.isChainComplete Pair)
        (Valuation.ord.approximation.isChainComplete Pair)
        (operatorB pairSalgebra defList.toDefList)
        (operatorB pairSalgebra theDefListInternal)
        (operatorB.isMonotonic pairSalgebra _)
        (operatorB.isMonotonic pairSalgebra _)
        internalOfExternal
        (fun isLfpB bLe =>
          isLeWfmWithPartialB isLfpB bLe)
        internalOfExternal.preservesSupremaApx
    
    def theInternalValuation.eqWfm:
      wfmInternal = theInternalValuation
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ theInternalValuation.isGeWfm theInternalValuation.isLeWfm
    
    def isUniversal
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨x, s3EqWfm⟩ := theDefListInternal.hasAllDefinable s3 isDef
      
      ⟨
        x,
        (s3EqWfm.trans (congr theInternalValuation.eqWfm rfl)).symm
      ⟩
    
  end uniSet3
end Pair
