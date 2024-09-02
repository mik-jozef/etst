/-
  `Pair.uniSet3.isUniversal` is the main result of this file.
  It states that any definable triset of pairs is in a sense
  "contained" in the triset `uniSet3`. See the file `./UniDefList.lean`
  for more info.
-/

import Utils.DefListDefEq
import UniSet3.TheSet3
import WFC.Ch6_S1_AProofSystem


namespace Pair
  namespace uniSet3
    open uniDefList
    
    noncomputable def theInternalDefList.getDef
      (n: Nat)
    :
      Expr pairSignature
    :=
      encodingToExpr
        (IsTheDefListExprPair.getNthExpr n).expr

    noncomputable def theInternalDefList:
      DefList pairSignature
    := {
      getDef := theInternalDefList.getDef
    }
    
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
    
    
    noncomputable def theInternalWfm :=
      theInternalDefList.wellFoundedModel pairSalgebra
    
    def theInternalDefList.hasAllDefinable
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x, s3 = theInternalWfm x
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
          theInternalDefList
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
      
      ⟨iStart + x, by unfold theInternalWfm; exact eq ▸ sEq⟩
    
    
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
    
    def insInternalToInsExternal
      (ins: Ins pairSalgebra theInternalDefList p x)
    :
      Ins pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x p)
        theSet
    :=
      -- Cannot use s
      match ins with
      | Ins.intro _ _
        causeInternal
        isCauseInternal
        cinsIns
        binsIns
        boutOut
      =>
        let causeExternal: Cause Pair := {
          contextIns :=
            fun ⟨p, x⟩ =>
              x = theSet ∧
              ∃ vv ∈ causeInternal.contextIns,
                p = Pair.pair vv.x vv.d,
          backgroundIns := sorry
          backgroundOut := sorry
        }
        
        let isCauseExternal:
          IsStrongCause pairSalgebra causeExternal _ _
        :=
          fun isSat =>
            sorry
        
        Ins.intro
          _
          _
          causeExternal
          isCauseExternal
          (fun ⟨xEq, ⟨vv, lr⟩⟩ =>
            let ⟨inCinsInternal, dEq⟩ := lr
            
            xEq ▸
            dEq ▸
            insInternalToInsExternal (cinsIns inCinsInternal))
          sorry
          sorry
    
    def outInternalToOutExternal
      (out: Out pairSalgebra theInternalDefList p x)
    :
      ¬ d ∈ (theInternalValuation x).posMem
    :=
      sorry
    
    
    def theInternalValuation.isGeWfm:
      theInternalWfm ⊑ theInternalValuation
    :=
      fun _ => {
        defLe :=
          fun _ insValExternal =>
            let ins := Ins.isComplete _ _ insValExternal
            (insInternalToInsExternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraDne
              fun outValExternal =>
                let out := Out.isComplete _ _ outValExternal
                outInternalToOutExternal out
      }
    
    def theInternalValuation.isLeWfm:
      theInternalValuation ⊑ theInternalWfm
    :=
      fun x =>
        sorry
    
    def theInternalValuation.eqWfm:
      theInternalWfm = theInternalValuation
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ isGeWfm isLeWfm
    
    def isUniversal
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨x, s3EqWfm⟩ := theInternalDefList.hasAllDefinable s3 isDef
      
      ⟨
        x,
        (s3EqWfm.trans (congr theInternalValuation.eqWfm rfl)).symm
      ⟩
    
  end uniSet3
end Pair
