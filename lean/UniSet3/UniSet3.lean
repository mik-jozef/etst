import DefListDefEq
import UniSet3.DefListToEncoding

def Set3.pairCall (fn arg: Set3 Pair): Set3 Pair := {
  defMem := fun p => ∃ (a: arg.defMem), fn.defMem (Pair.pair a p)
  posMem := fun p => ∃ (a: arg.posMem), fn.posMem (Pair.pair a p)
  defLePos :=
    fun _p pInDef =>
      let ⟨⟨a, aInArgDef⟩, apInFnDef⟩ := pInDef
      
      ⟨
        ⟨a, (arg.defLePos aInArgDef)⟩,
        fn.defLePos apInFnDef
      ⟩
}

def Set3.pairCallJust
  (fn: Set3 Pair)
  (arg: Pair)
:=
  Set3.pairCall fn (Set3.just arg)


namespace Pair
  noncomputable def uniSet3 := uniDefList.wfModel uniDefList.theSet
  
  namespace uniSet3
    noncomputable def theDefListExternal.getDef
      (n: Nat)
    :
      Expr pairSignature
    :=
      encodingToExpr
        (IsTheDefListExprPair.getNthExpr n).expr

    noncomputable def theDefListExternal:
      DefList pairSignature
    := {
      getDef := theDefListExternal.getDef
    }
    
    def theDefListExternal.inListOfIsDefList
      (isInDl: IsTheDefListExprPair (fromNat i) exprEnc)
      (eqEnc: exprEnc = exprToEncoding expr)
    :
      expr = theDefListExternal.getDef i
    :=
      let isInDlNth := (IsTheDefListExprPair.getNthExpr i).isNth
      let eq := IsTheDefListExprPair.isUnique isInDlNth isInDl
      
      by
        unfold theDefListExternal.getDef;
        exact
          eq ▸ eqEnc ▸ (encodingToExpr.isInverse expr).symm
    
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
    
    
    noncomputable def wfm :=
      theDefListExternal.wellFoundedModel pairSalgebra
    
    def theDefListExternal.hasAllDefinable
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x, s3 = wfm x
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
          theDefListExternal
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
      
      ⟨iStart + x, by unfold wfm; exact eq ▸ sEq⟩
    
    def theSetAsValuation: Valuation Pair :=
      fun n => Set3.pairCallJust uniSet3 (fromNat n)
    
    def theSetAsValuation.interpretationsEqual
      (x: Nat)
    :
      Set3.pairCallJust
        (Expr.interpretation
          pairSalgebra
          uniDefList.wfModel
          uniDefList.wfModel
          (uniDefList.defList.getDef uniDefList.theSet))
        (fromNat x)
        =
      Expr.interpretation
        pairSalgebra
        theSetAsValuation
        theSetAsValuation
        (encodingToExpr (IsTheDefListExprPair.getNthExpr x).expr)
    :=
      Set3.eq
        sorry
        sorry
    
    def theSetAsValuation.isFixedPointOpC:
      IsFixedPoint
        (operatorC pairSalgebra theDefListExternal theSetAsValuation)
        theSetAsValuation
    :=
      funext fun x => by
        conv => lhs; unfold theSetAsValuation uniSet3 uniDefList.wfModel;
        exact
          wfmAtEq
            uniDefList.defList.toDefList
            pairSalgebra uniDefList.theSet ▸
          interpretationsEqual x
    
    def theSetAsValuation.isLeCLfp:
      (Valuation.ord.standard Pair).le
        theSetAsValuation
        (operatorC.lfp pairSalgebra theDefListExternal theSetAsValuation).val
    :=
      -- TODO only start this proof after `theSetAsValuation.isLeWfm`,
      -- you might need to generalize this.
      sorry
    
    def theSetAsValuation.isFixedPointOpB:
      IsFixedPoint
        (operatorB pairSalgebra theDefListExternal)
        theSetAsValuation
    :=
      let lfp :=
        operatorC.lfp pairSalgebra theDefListExternal theSetAsValuation
      
      let isGe := lfp.property.isLeMember isFixedPointOpC
      
      (Valuation.ord.standard Pair).le_antisymm _ _ isLeCLfp isGe
    
    def theSetAsValuation.isGeWfm:
      (Valuation.ord.approximation Pair).le wfm theSetAsValuation
    :=
      let isLfp :=
        DefList.wellFoundedModel.isLfp pairSalgebra theDefListExternal
      
      isLfp.isLeMember theSetAsValuation.isFixedPointOpB
    
    def theSetAsValuation.isLeWfm:
      (Valuation.ord.approximation Pair).le theSetAsValuation wfm
    :=
      sorry
    
    def theSetAsValuation.eqWfm:
      wfm = theSetAsValuation
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ theSetAsValuation.isGeWfm theSetAsValuation.isLeWfm
    
    def isUniversal
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨x, s3EqWfm⟩ := theDefListExternal.hasAllDefinable s3 isDef
      
      ⟨
        x,
        (s3EqWfm.trans (congr theSetAsValuation.eqWfm rfl)).symm
      ⟩
  end uniSet3
end Pair
