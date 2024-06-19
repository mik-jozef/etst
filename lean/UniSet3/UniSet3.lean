import Utils.DefListDefEq
import Utils.LfpLeOfOpLe
import UniSet3.DefListToEncoding
import UniSet3.TheSet3


namespace Pair
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
      by
        unfold theDefListExternal.getDef;
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
    
    def theSetAsValuation.interpretationsEqual
      (x: Nat)
    :
      Set3.pairCallJust uniSet3 (fromNat x)
        =
      Expr.interpretation
        pairSalgebra
        theSetAsValuation
        theSetAsValuation
        (encodingToExpr (IsTheDefListExprPair.getNthExpr x).expr)
    :=
      Set3.ord.standard.le_antisymm _ _ ⟨
        fun _ => inDefNthOfInsTheSet,
        fun _ => inPosNthOfInwTheSet,
      ⟩ ⟨
        fun _ => insTheSetOfInDefNth,
        fun _ => inwTheSetOfInPosNth,
      ⟩
    
    def theSetAsValuation.ofArbitraryValuation
      (v: Valuation Pair)
    :
      Valuation Pair
    :=
      fun n =>
        Set3.pairCallJust
          (v uniDefList.theSet)
          (fromNat n)
    
    def theSetAsValuation.ofArbitraryValuation.isMonoStd
    :
      IsMonotonic
        (Valuation.ord.standard Pair)
        (Valuation.ord.standard Pair)
        ofArbitraryValuation
    :=
      fun valLe _ => {
        -- Would be nice if this worked: `defLe t inVal := ...`
        defLe :=
          fun _ inVal => (valLe uniDefList.theSet).defLe inVal,
        posLe :=
          fun _ inVal => (valLe uniDefList.theSet).posLe inVal,
      }
    
    def theSetAsValuation.ofArbitraryValuation.isMonoApx
    :
      IsMonotonic
        (Valuation.ord.approximation Pair)
        (Valuation.ord.approximation Pair)
        ofArbitraryValuation
    :=
      fun valLe _ => {
        defLe :=
          fun _ inVal => (valLe uniDefList.theSet).defLe inVal,
        posLe :=
          fun _ inVal => (valLe uniDefList.theSet).posLe inVal,
      }
    
    def theSetAsValuation.ofArbitraryValuation.preservesSupremaStd
      (ch: Chain (Valuation.ord.standard Pair))
    :
      let isCc := Valuation.ord.standard.isChainComplete Pair
      
      IsSupremum
        (Valuation.ord.standard Pair)
        (ofArbitraryValuation '' ch.set)
        (ofArbitraryValuation (ch.sup isCc).val)
    :=
      -- In your language, the vars of the return type should be
      -- in scope (I guess)?
      let isCc := Valuation.ord.standard.isChainComplete Pair
      
      {
        isMember :=
          fun ⟨v, vIn⟩ =>
            let ⟨preV, ⟨preVInCh, isPre⟩⟩ := vIn.unwrap
            let preLeSup :=
              (ch.sup isCc).property.isMember ⟨preV, preVInCh⟩
            
            isPre ▸ isMonoStd preLeSup
        isLeMember :=
          fun ub isUb x => {
            defLe :=
              fun p inSup =>
                let ⟨⟨v, inCh⟩, insTheSet⟩ :=
                  Valuation.ord.standard.inSup.inSomeSet.defMem
                    (ch.sup isCc)
                    inSup
                    
                let vIsLeUb :=
                  isUb ⟨ofArbitraryValuation v, ⟨v, ⟨inCh, rfl⟩⟩⟩ x
                
                vIsLeUb.defLe insTheSet
            posLe :=
              fun p inSup =>
                let ⟨⟨v, inCh⟩, insTheSet⟩ :=
                  Valuation.ord.standard.inSup.inSomeSet.posMem
                    (ch.sup isCc)
                    inSup
                    
                let vIsLeUb :=
                  isUb ⟨ofArbitraryValuation v, ⟨v, ⟨inCh, rfl⟩⟩⟩ x
                
                vIsLeUb.posLe insTheSet
          }
      }
    
    def theSetAsValuation.ofArbitraryValuation.preservesSupremaApx
      (ch: Chain (Valuation.ord.approximation Pair))
    :
      let isCc := Valuation.ord.approximation.isChainComplete Pair
      
      IsSupremum
        (Valuation.ord.approximation Pair)
        (ofArbitraryValuation '' ch.set)
        (ofArbitraryValuation (ch.sup isCc).val)
    :=
      let isCc := Valuation.ord.approximation.isChainComplete Pair
      
      {
        isMember :=
          fun ⟨v, vIn⟩ =>
            let ⟨preV, ⟨preVInCh, isPre⟩⟩ := vIn.unwrap
            let preLeSup :=
              (ch.sup isCc).property.isMember ⟨preV, preVInCh⟩
            
            isPre ▸ isMonoApx preLeSup
        isLeMember :=
          fun ub isUb x => {
            defLe :=
              fun p inSup =>
                let ⟨⟨v, inCh⟩, insTheSet⟩ :=
                  Valuation.ord.approximation.inSup.inSomeSet.defMem
                    (ch.sup isCc)
                    inSup
                    
                let vIsLeUb :=
                  isUb ⟨ofArbitraryValuation v, ⟨v, ⟨inCh, rfl⟩⟩⟩ x
                
                vIsLeUb.defLe insTheSet
            posLe :=
              fun p inUb =>
                Valuation.ord.approximation.allInSet.inSup.posMem
                  (ch.sup isCc)
                  (fun v =>
                    let leUb :=
                      isUb
                        ⟨
                          ofArbitraryValuation v,
                          v,
                          v.property,
                          rfl,
                        ⟩
                        x
                    
                    leUb.posLe inUb)
          }
      }
    
    def theSetAsValuation.eqOfWfm:
      theSetAsValuation = ofArbitraryValuation uniDefList.wfModel
    :=
      rfl
    
    
    def theSetAsValuation.isFixedPointOpC:
      IsFixedPoint
        (operatorC pairSalgebra theDefListExternal theSetAsValuation)
        theSetAsValuation
    :=
      funext interpretationsEqual
    
    def theSetAsValuation.interpretationLeStd
      (isLfpC:
        IsLfp
          (Valuation.ord.standard Pair)
          (operatorC pairSalgebra uniDefList.defList.toDefList b)
          lfpC)
      (cLe: c ≤ lfpC)
    :
      let b := uniDefList.wfModel
      
      ofArbitraryValuation
        (uniDefList.defList.interpretation pairSalgebra b c)
        ≤
      theDefListExternal.interpretation
        pairSalgebra (ofArbitraryValuation b) (ofArbitraryValuation c)
    :=
      sorry
    
    def theSetAsValuation.isLeCLfp:
      (Valuation.ord.standard Pair).le
        theSetAsValuation
        (operatorC.lfp pairSalgebra theDefListExternal theSetAsValuation).val
    :=
      let b := uniDefList.wfModel
      let opCB :=
        operatorC.lfp pairSalgebra uniDefList.defList.toDefList b
      
      let eqC:
        b = opCB.val
      :=
        let opB :=
          operatorB.lfp pairSalgebra uniDefList.defList.toDefList
        
        opB.property.isMember
      
      let eqL: ofArbitraryValuation b = _ := congr rfl eqC
      
      by
        conv => lhs; rw [eqOfWfm, eqL]
        exact
          lfp.leOfOpLeMappedSameOrd
            (Valuation.ord.standard.isChainComplete Pair)
            (Valuation.ord.standard.isChainComplete Pair)
            (operatorC pairSalgebra uniDefList.defList.toDefList b)
            (operatorC pairSalgebra theDefListExternal (ofArbitraryValuation b))
            (operatorC.isMonotonic pairSalgebra _ _)
            (operatorC.isMonotonic pairSalgebra _ _)
            ofArbitraryValuation
            (fun isLfpC cLe =>
              interpretationLeStd isLfpC cLe)
            ofArbitraryValuation.preservesSupremaStd
    
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
    
    
    def theSetAsValuation.interpretationLeApx
      (isLfpB:
        IsLfp
          (Valuation.ord.approximation Pair)
          (operatorB pairSalgebra uniDefList.defList.toDefList) lfpB)
      (bLe: b ⊑ lfpB)
      (isLfpC:
        IsLfp
          (Valuation.ord.standard Pair)
          (operatorC pairSalgebra uniDefList.defList.toDefList b) lfpC)
      (cLe: c ≤ lfpC)
    :
      ofArbitraryValuation
        (uniDefList.defList.interpretation pairSalgebra b c)
        ⊑
      theDefListExternal.interpretation
        pairSalgebra (ofArbitraryValuation b) (ofArbitraryValuation c)
    :=
      sorry
    
    def theSetAsValuation.isLeWfmWithPartialB
      (isLfpB:
        IsLfp
          (Valuation.ord.approximation Pair)
          (operatorB pairSalgebra uniDefList.defList.toDefList) lfpB)
      (bLe: b ⊑ lfpB)
    :
      (Valuation.ord.approximation Pair).le
        (ofArbitraryValuation
          (Subtype.val
            (operatorC.lfp pairSalgebra uniDefList.defList.toDefList b)))
        (Subtype.val
          (operatorC.lfp
            pairSalgebra
            theDefListExternal
            (ofArbitraryValuation b)))
    :=
      lfp.leOfOpLeMapped
        (Valuation.ord.standard.isChainComplete Pair)
        (Valuation.ord.standard.isChainComplete Pair)
        (operatorC pairSalgebra uniDefList.defList.toDefList b)
        (operatorC pairSalgebra theDefListExternal (ofArbitraryValuation b))
        (operatorC.isMonotonic pairSalgebra _ _)
        (operatorC.isMonotonic pairSalgebra _ _)
        ofArbitraryValuation
        (operatorC.isMonotonic.approximation pairSalgebra _ _)
        (fun isLfpC cLe =>
          interpretationLeApx isLfpB bLe isLfpC cLe)
        ofArbitraryValuation.preservesSupremaStd
        Valuation.ord.standard.supPreservesLeApx
    
    def theSetAsValuation.isLeWfm:
      (Valuation.ord.approximation Pair).le theSetAsValuation wfm
    :=
      lfp.leOfOpLeMappedSameOrd
        (Valuation.ord.approximation.isChainComplete Pair)
        (Valuation.ord.approximation.isChainComplete Pair)
        (operatorB pairSalgebra uniDefList.defList.toDefList)
        (operatorB pairSalgebra theDefListExternal)
        (operatorB.isMonotonic pairSalgebra _)
        (operatorB.isMonotonic pairSalgebra _)
        ofArbitraryValuation
        (fun isLfpB bLe =>
          isLeWfmWithPartialB isLfpB bLe)
        ofArbitraryValuation.preservesSupremaApx
    
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
