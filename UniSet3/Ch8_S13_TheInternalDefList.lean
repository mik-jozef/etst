-- The thirteenth section of chapter 8. See the zeroth section.

import Utils.DefListDefEq
import Utils.DependsOnRefl
import UniSet3.Ch8_S12_DefListToEncoding


namespace Pair
  namespace uniSet3
    noncomputable def theInternalDefList.getDef
      (n: Nat)
    :
      Expr pairSignature
    :=
      encodingToExpr
        (IsTheDefListExprPair.getNthExpr n).exprEnc

    noncomputable def theInternalDefList:
      DefList pairSignature
    := {
      getDef := theInternalDefList.getDef
    }
    
    def theInternalDefList.eqEnc
      (x: Nat)
    :
      exprToEncoding (theInternalDefList.getDef x)
        =
      (IsTheDefListExprPair.getNthExpr x).exprEnc
    := by
      unfold theInternalDefList.getDef
      rw [exprToEncoding.isInverse]
      exact (IsTheDefListExprPair.getNthExpr x).isNth.isExpr
    
    def theInternalDefList.eqExpr
      (x: Nat)
    :
      (theInternalDefList.getDef x)
        =
      (IsTheDefListExprPair.getNthExpr x).exprEnc.encodingToExpr
    :=
      theInternalDefList.eqEnc x ▸
      (encodingToExpr.isInverse (getDef x)).symm
    
    def theInternalDefList.inListOfIsDefList
      (isInDl: IsTheDefListExprPair (fromNat i) exprEnc)
      (eqEnc: exprEnc = exprToEncoding expr)
    :
      expr = theInternalDefList.getDef i
    :=
      by
        unfold theInternalDefList.getDef;
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
      | Expr.op Op.un _args =>
        show (pair _ _) = _ from
          congr rfl (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.op Op.ir _args =>
        incrVars.eqBin (Is4 rfl) _ _ ▸
        congr rfl (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.cpl _ =>
        incrVars.eqCpl _ ▸ congr rfl incrVarsEqMapVars
      | Expr.op Op.ifThen _args =>
        incrVars.eqBin (Is6 rfl) _ _ ▸
        congr rfl (congrBin rfl incrVarsEqMapVars incrVarsEqMapVars)
      | Expr.arbUn _ _ =>
        incrVars.eqQuant (Is7 rfl) _ _ ▸
        congrBin rfl rfl (congr rfl incrVarsEqMapVars)
      | Expr.arbIr _ _ =>
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
    
    
    noncomputable def theInternalWfm :=
      theInternalDefList.wellFoundedModel pairSalgebra
    
    def theInternalDefList.hasAllDefinable
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x, s3 = theInternalWfm x
    :=
      let ⟨dl, x, sEq⟩ := isDef
      
      let ⟨dlSliceEnd, gtBounds⟩ := dl.isFinBoundedRefl x
      
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
          theInternalDefList
          pairSalgebra
          (fun i => iStart + i)
          (fun i => DefList.DependsOnRefl dl.getDef x i)
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
          (DefList.DependsOnRefl.Refl x)
      
      ⟨iStart + x, by unfold theInternalWfm; exact eq ▸ sEq⟩
    
  end uniSet3
end Pair
