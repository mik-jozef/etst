/-
  `Pair.uniSet3.isUniversal` is the main result of this volume.
  It states that any definable triset of pairs is in a sense
  "contained" in the triset `uniSet3`. See chapter 7 for more
  info.
  
  TODO summarize informally the proof strategy here.
-/

import UniSet3.Ch10_S00_TheInternalDefList


namespace Pair
  namespace uniSet3
    def theExternalDefList := uniDefList.theExternalDefList
    
    
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
    
    
    def interpretationsEqual
      (b c: Valuation Pair)
      -- TODO extra conditions will be necessary
    :
      (Expr.interpretation
        pairSalgebra
        (internalOfExternal b)
        (internalOfExternal c)
        (theInternalDefList.getDef x)).defMem d
        =
      (Expr.interpretation
        pairSalgebra
        b
        c
        (theExternalDefList.getDef uniDefList.theSet)
      ).defMem (pair x d)
    :=
      sorry
    
    
    /-
      Converts an internal cause to the corresponding external
      cause. The external cause also includes requirements that
      are necessary for the interpretation (ie. the definition
      number 34 in `theExternalDefList`) to work correctly in the
      external valuation.
    -/
    inductive IsInExternalCause
      (internalCause: Set (ValVar Pair))
      (isIns: Prop)
      (vv: ValVar Pair)
    :
      Prop
    
    -- TODO:
    -- 0  - NatIsOk
    -- 33 - GetBoundIsOk
    -- 7  - ExprEncodingIsOk
    -- 32 - TheDefListIsOk
    
    | TheSetIsOk
      (xEq: vv.x = uniDefList.theSet)
      (matchesInternalPart:
        ∃ vvI ∈ internalCause, vv.d = (vvI.x, vvI.d))
    
    
    def externalOfInternalCause
      (internalCause: Cause Pair)
    :
      Cause Pair
    :=
      let ic := internalCause
      {
        contextIns := IsInExternalCause ic.contextIns True
        backgroundIns := IsInExternalCause ic.backgroundIns True
        backgroundOut := IsInExternalCause ic.backgroundOut False
      }
    
    /-
      A part of the external cause that's just the contents
      of `theSet`.
    -/
    def theSetOfInternalCause
      (internalCause: Cause Pair)
    :
      Cause Pair
    := {
      contextIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.contextIns,
            d = (vvI.x, vvI.d)
      backgroundIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundIns,
            d = (vvI.x, vvI.d)
      backgroundOut :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundOut,
            d = (vvI.x, vvI.d)
    }
    
    def internalOfExternalCause
      (externalCause: Cause Pair)
    :
      Cause Pair
    := {
      contextIns :=
        fun ⟨d, x⟩ =>
          externalCause.contextIns
            ⟨Pair.pair x d, uniDefList.theSet⟩
      backgroundIns :=
        fun ⟨d, x⟩ =>
          externalCause.backgroundIns
            ⟨Pair.pair x d, uniDefList.theSet⟩
      backgroundOut :=
        fun ⟨d, x⟩ =>
          externalCause.backgroundOut
            ⟨Pair.pair x d, uniDefList.theSet⟩
    }
    
    
    def externalOfInternalCycle
      (internalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    :=
      fun vv =>
        Or (
          vv.x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCycle, vv.d = (vvI.x, vvI.d)
        ) (
          ¬ (uniDefList.theExternalWfm vv.x).posMem vv.d
        )
    
    def internalOfExternalCycle
      (externalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    :=
      fun ⟨d, x⟩ =>
        externalCycle ⟨Pair.pair x d, uniDefList.theSet⟩
    
    
    structure IsCauseApplicalbeExceptForTheSet
      (externalCycle: Set (ValVar Pair))
      (externalCause: Cause Pair)
    :
      Prop
    where
      contextInsIsOkEq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCause.contextIns →
          x = uniDefList.theSet →
        ∃ n p,
          d = pair (fromNat n) p
      contextInsIsOkNeq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCause.contextIns →
          x ≠ uniDefList.theSet →
          (uniDefList.theExternalWfm x).posMem d
      
      cycleIsOutNeq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCycle →
          x ≠ uniDefList.theSet →
          ¬ (uniDefList.theExternalWfm x).posMem d
      
      backgroundInsIsOkEq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCause.backgroundIns →
          x = uniDefList.theSet →
        ∃ n p,
          d = pair (fromNat n) p
      backgroundInsIsOkNeq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCause.backgroundIns →
          x ≠ uniDefList.theSet →
          (uniDefList.theExternalWfm x).posMem d
      
      backgroundOutIsOkEq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCause.backgroundOut →
          x = uniDefList.theSet →
        ∃ n p,
          d = pair (fromNat n) p
      backgroundOutIsOkNeq:
        ∀ {d x},
          ⟨d, x⟩ ∈ externalCause.backgroundOut →
          x ≠ uniDefList.theSet →
          ¬ (uniDefList.theExternalWfm x).defMem d
    
    
    def causeExtIntExtSubset
      (externalCause: Cause Pair)
    :
      (theSetOfInternalCause (internalOfExternalCause externalCause))
        ⊆
      externalCause
    :=
      {
        cinsLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inCins, dEq⟩⟩⟩ =>
            xEq ▸ dEq ▸ inCins
        binsLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inBins, dEq⟩⟩⟩ =>
            xEq ▸ dEq ▸ inBins
        boutLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inBout, dEq⟩⟩⟩ =>
            xEq ▸ dEq ▸ inBout
      }
    
    
    def isStrongExtOfInt
      (isCauseInternal:
        IsStrongCause
          pairSalgebra
          cause
          d
          (theInternalDefList.getDef x))
    :
      IsStrongCause
        pairSalgebra
        (externalOfInternalCause cause)
        (Pair.pair x d)
        (theExternalDefList.getDef uniDefList.theSet)
    :=
      fun {b c} isSat =>
        let isDefInternal:
          Set3.defMem
            ((theInternalDefList.getDef x).interpretation
              pairSalgebra
              (internalOfExternal b)
              (internalOfExternal c))
            d
        :=
          open IsInExternalCause in
          isCauseInternal {
            contextInsHold :=
              fun {dd xx} inCins =>
                isSat.contextInsHold
                  (TheSetIsOk rfl ⟨⟨dd, xx⟩, inCins, rfl⟩)
            backgroundInsHold :=
              fun {dd xx} inBins =>
                isSat.backgroundInsHold
                  (TheSetIsOk rfl ⟨⟨dd, xx⟩, inBins, rfl⟩)
            backgroundOutHold :=
              fun {dd xx} inBout =>
                isSat.backgroundOutHold
                  (TheSetIsOk rfl ⟨⟨dd, xx⟩, inBout, rfl⟩)
          }
        -- TODO it remains to prove that, assuming `b` and `c`
        -- satisfy the constraints of `IsInExternalCause`,
        -- the valuation's definite members are equal.
        sorry
    
    -- TODO split into several functions?
    def isWeakIntOrInappExtOfExt
      (inCycle: ⟨d, x⟩ ∈ internalCycle)
      (isCauseExternal:
        IsWeakCause
          pairSalgebra
          externalCause
          (Pair.pair (fromNat x) d)
          (theExternalDefList.getDef uniDefList.theSet))
    :
      Or
        (IsWeakCause
          pairSalgebra
          (internalOfExternalCause externalCause)
          d
          (theInternalDefList.getDef x))
        (IsCauseInapplicable
          pairSalgebra
          theExternalDefList.toDefList
          (externalOfInternalCycle internalCycle)
          externalCause)
    :=
      if hCins:
        ∃ vv ∈ externalCause.contextIns,
          vv.d ∉ (uniDefList.theExternalWfm vv.x).posMem
      then
        let ⟨⟨d, x⟩, inCins, ninDef⟩ := hCins
        
        Or.inr
          (IsCauseInapplicable.blockedContextIns
            externalCause inCins (Or.inr ninDef))
      else if hBins:
        ∃ vv ∈ externalCause.backgroundIns,
          vv.d ∉ (uniDefList.theExternalWfm vv.x).posMem
      then
        let ⟨⟨d, x⟩, inBins, ninDef⟩ := hBins
        
        Or.inr
          (IsCauseInapplicable.blockedBackgroundIns
            externalCause
            inBins
            (Out.isComplete
              pairSalgebra
              theExternalDefList.toDefList
              ninDef))
      else if hBout:
        ∃ vv ∈ externalCause.backgroundOut,
          vv.d ∈ (uniDefList.theExternalWfm vv.x).defMem
      then
        let ⟨⟨d, x⟩, inBout, inDef⟩ := hBout
        
        Or.inr
          (IsCauseInapplicable.blockedBackgroundOut
            externalCause
            inBout
            (Ins.isComplete
              pairSalgebra
              theExternalDefList.toDefList
              inDef))
      else
        Or.inl
          fun {b c} isSat =>
            let isDefExternal:
              Set3.posMem
                (Expr.interpretation
                  pairSalgebra
                  (externalOfInternal b)
                  (externalOfInternal c)
                  (theExternalDefList.getDef uniDefList.theSet))
                (Pair.pair x d)
            :=
              isCauseExternal {
                contextInsHold :=
                  fun {dd xx} inCins =>
                    let isPos:
                      dd ∈ (uniDefList.theExternalWfm xx).posMem
                    :=
                      byContradiction fun ninPos =>
                        hCins ⟨_, inCins, ninPos⟩
                    
                    if hX: xx = uniDefList.theSet then
                      match hD: dd with
                      | zero =>
                        inwTheSet.nopeZero (hX ▸ hD ▸ isPos)
                      | pair dA dB =>
                        let isNatDa :=
                          inwTheSet.toIsNat (hX ▸ hD ▸ isPos)
                        
                        let inCins:
                          externalCause.contextIns
                            ⟨pair isNatDa.toNat dB, uniDefList.theSet⟩
                        :=
                          hX ▸
                          isNatDa.toNatFromNatEq.symm ▸
                          inCins
                        
                        hX ▸ ⟨
                          isNatDa.toNat,
                          ⟨dB, isSat.contextInsHold inCins⟩,
                          isNatDa.toNatFromNatEq.symm ▸ rfl,
                        ⟩
                    else
                      externalOfInternal.eqAtOther _ hX ▸
                      isPos
                backgroundInsHold :=
                  fun {dd xx} inBins =>
                    let isPos:
                      dd ∈ (uniDefList.theExternalWfm xx).posMem
                    :=
                      byContradiction fun ninPos =>
                        hBins ⟨_, inBins, ninPos⟩
                    
                    if hX: xx = uniDefList.theSet then
                      match hD: dd with
                      | zero =>
                        inwTheSet.nopeZero (hX ▸ hD ▸ isPos)
                      | pair dA dB =>
                        let isNatDa :=
                          inwTheSet.toIsNat (hX ▸ hD ▸ isPos)
                        
                        let inBins:
                          externalCause.backgroundIns
                            ⟨pair isNatDa.toNat dB, uniDefList.theSet⟩
                        :=
                          hX ▸
                          isNatDa.toNatFromNatEq.symm ▸
                          inBins
                        
                        hX ▸ ⟨
                          isNatDa.toNat,
                          ⟨dB, isSat.backgroundInsHold inBins⟩,
                          isNatDa.toNatFromNatEq.symm ▸ rfl,
                        ⟩
                    else
                      externalOfInternal.eqAtOther _ hX ▸
                      isPos
                backgroundOutHold :=
                  fun {dd xx} inBout =>
                    let notDef:
                      dd ∉ (uniDefList.theExternalWfm xx).defMem
                    :=
                      fun isDef =>
                        hBout ⟨_, inBout, isDef⟩
                    
                    if hX: xx = uniDefList.theSet then
                      match hD: dd with
                      | zero =>
                        fun isDef =>
                          let ⟨x, d, nope⟩ :=
                            externalOfInternal.eqAtTheSet b ▸
                            hX ▸
                            isDef
                          Pair.noConfusion nope
                      | pair dA dB =>
                          hX ▸
                          externalOfInternal.eqAtTheSet b ▸
                          fun ⟨xx, ⟨dd, ddIsDef⟩, eq⟩ =>
                            let inBout:
                              externalCause.backgroundOut ⟨
                                pair (fromNat xx) dd,
                                uniDefList.theSet,
                              ⟩
                            :=
                              hX ▸ eq ▸ inBout
                            
                            isSat.backgroundOutHold inBout ddIsDef
                    else
                      externalOfInternal.eqAtOther _ hX ▸
                      notDef
              }
          sorry
    
    
    def isStrongIntOfExt
      (isCauseExternal:
        IsStrongCause
          pairSalgebra
          externalCause
          (Pair.pair (fromNat x) d)
          (theExternalDefList.getDef uniDefList.theSet))
      (cinsInsExternal:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.contextIns →
          Ins pairSalgebra theExternalDefList.toDefList d x)
      (binsInsExternal:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundIns →
          Ins pairSalgebra theExternalDefList.toDefList d x)
      (boutOutExternal:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundOut →
          Out pairSalgebra theExternalDefList.toDefList d x)
    :
      IsStrongCause
        pairSalgebra
        (internalOfExternalCause externalCause)
        d
        (theInternalDefList.getDef x)
    :=
      fun {b c} isSat =>
        let isDefExternal:
          Set3.defMem
            (Expr.interpretation
              pairSalgebra
              (externalOfInternal b)
              (externalOfInternal c)
              (theExternalDefList.getDef uniDefList.theSet))
            (Pair.pair x d)
        :=
          isCauseExternal {
            contextInsHold :=
              fun {dd xx} inCins =>
                if h: xx = uniDefList.theSet then
                  h ▸
                  externalOfInternal.eqAtTheSet c ▸
                  match dd with
                  | zero =>
                    let isDef := (cinsInsExternal inCins).isSound
                    insTheSet.nopeZero (h ▸ isDef)
                  | pair dA dB =>
                    let isDef :=
                      (cinsInsExternal inCins).isSound
                    let isNatDa := insTheSet.toIsNat (h ▸ isDef)
                    let eqDa: fromNat isNatDa.toNat = dA :=
                      isNatDa.toNatFromNatEq
                    let inCinsExternal:
                      externalCause.contextIns ⟨
                        (fromNat isNatDa.toNat).pair dB,
                        uniDefList.theSet
                      ⟩
                    :=
                      eqDa.symm ▸ h ▸ inCins
                    ⟨
                      isNatDa.toNat,
                      ⟨dB, isSat.contextInsHold inCinsExternal⟩,
                      eqDa.symm ▸ rfl,
                    ⟩
                else
                  externalOfInternal.eqAtOther _ h ▸
                  (cinsInsExternal inCins).isSound
            backgroundInsHold :=
              fun {dd xx} inBins =>
                if h: xx = uniDefList.theSet then
                  h ▸
                  externalOfInternal.eqAtTheSet b ▸
                  match dd with
                  | zero =>
                    let isDef := (binsInsExternal inBins).isSound
                    insTheSet.nopeZero (h ▸ isDef)
                  | pair dA dB =>
                    let isDef :=
                      (binsInsExternal inBins).isSound
                    let isNatDa := insTheSet.toIsNat (h ▸ isDef)
                    let eqDa: fromNat isNatDa.toNat = dA :=
                      isNatDa.toNatFromNatEq
                    let inBinsExternal:
                      externalCause.backgroundIns ⟨
                        (fromNat isNatDa.toNat).pair dB,
                        uniDefList.theSet
                      ⟩
                    :=
                      eqDa.symm ▸ h ▸ inBins
                    ⟨
                      isNatDa.toNat,
                      ⟨dB, isSat.backgroundInsHold inBinsExternal⟩,
                      eqDa.symm ▸ rfl,
                    ⟩
                else
                  externalOfInternal.eqAtOther _ h ▸
                  (binsInsExternal inBins).isSound
            backgroundOutHold :=
              fun {dd xx} inBout =>
                if h: xx = uniDefList.theSet then
                  h ▸
                  externalOfInternal.eqAtTheSet b ▸
                  match dd with
                  | zero =>
                    fun ⟨_, _, eq⟩ => Pair.noConfusion eq
                  | pair dA dB =>
                    fun ⟨x, ⟨d, dPos⟩, eq⟩ =>
                      let ⟨eqDa, eqDb⟩ :=
                        Pair.noConfusion eq And.intro
                      isSat.backgroundOutHold
                        (eqDa ▸ h ▸ inBout)
                        (eqDb ▸ dPos)
                else
                  externalOfInternal.eqAtOther _ h ▸
                  (boutOutExternal inBout).isSound
          }
        
        -- TODO remains to use the internal/external equivalence
        -- of interpretations.
        sorry
    
    
    /-
      For a value `d` that is provably in the internal definition
      `x`, `(x, d)` is provably in the external definition `theSet`.
      
      We proceed by induction on the structure of the proof, and
      this is the inductive step for `Ins`. The last three arguments
      are the inductive hypotheses.
    -/
    def isCauseInternalToInsExternal
      (isCauseInternal:
        IsStrongCause
          pairSalgebra
          internalCause
          d
          (theInternalDefList.getDef x))
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.contextIns →
          Ins
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (binsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.backgroundIns →
          Ins
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.backgroundOut →
          Out
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
    :
      Ins
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      let isCauseExternal:
        IsStrongCause
          pairSalgebra
          (externalOfInternalCause internalCause)
          (Pair.pair x d)
          (theExternalDefList.getDef uniDefList.theSet)
      :=
        isStrongExtOfInt isCauseInternal
      
      Ins.intro
        _
        _
        (externalOfInternalCause internalCause)
        isCauseExternal
        (fun {dd xx} ⟨xEq, ⟨_, ⟨inCinsInternal, dEq⟩⟩⟩ =>
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          cinsIns inCinsInternal)
        (fun {dd xx} ⟨xEq, ⟨_, ⟨inBinsInternal, dEq⟩⟩⟩ =>
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          binsIns inBinsInternal)
        (fun {dd xx} ⟨xEq, ⟨_, ⟨inBoutInternal, dEq⟩⟩⟩ =>
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          boutOut inBoutInternal)
    
    /-
      Ins external to Ins internal, the inductive step.
      The last three arguments are the inductive hypotheses.
    -/
    def isCauseExternalToInsInternal
      (isCauseExternal:
        IsStrongCause
          pairSalgebra
          externalCause
          (Pair.pair (fromNat x) d)
          (theExternalDefList.getDef uniDefList.theSet))
      (cinsInsExternal:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.contextIns →
          Ins pairSalgebra theExternalDefList.toDefList d x)
      (binsInsExternal:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundIns →
          Ins pairSalgebra theExternalDefList.toDefList d x)
      (boutOutExternal:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundOut →
          Out pairSalgebra theExternalDefList.toDefList d x)
      (cinsInsInternal:
        ∀ {d} {x: Nat},
          ⟨Pair.pair x d, uniDefList.theSet⟩
            ∈ externalCause.contextIns →
          Ins pairSalgebra theInternalDefList d x)
      (binsInsInternal:
        ∀ {d} {x: Nat},
          ⟨Pair.pair x d, uniDefList.theSet⟩
            ∈ externalCause.backgroundIns →
          Ins pairSalgebra theInternalDefList d x)
      (boutOutInternal:
        ∀ {d} {x: Nat},
          ⟨Pair.pair x d, uniDefList.theSet⟩
            ∈ externalCause.backgroundOut →
          Out pairSalgebra theInternalDefList d x)
    :
      Ins pairSalgebra theInternalDefList d x
    :=
      let isCauseInternal:
        IsStrongCause
          pairSalgebra
          (internalOfExternalCause externalCause)
          d
          (theInternalDefList.getDef x)
      :=
        isStrongIntOfExt
          isCauseExternal
          cinsInsExternal
          binsInsExternal
          boutOutExternal
      
      Ins.intro
        _
        _
        (internalOfExternalCause externalCause)
        isCauseInternal
        cinsInsInternal
        binsInsInternal
        boutOutInternal
    
    
    /-
      For a value `d` that is provably out of the internal definition
      `x`, the pair `(x, d)` is provably out of `theSet`.
      
      We proceed by induction on the structure of the proof, and
      this is the inductive step for `Out`. The induction hypothesis
      is incorporated into the parameter `isEmptyCycle`.
    -/
    def inEmptyCycleInternalToOutExternal
      {internalCycle: Set (ValVar Pair)}
      {d: Pair}
      {x: Nat}
      (inCycle: ⟨d, x⟩ ∈ internalCycle)
      (isEmptyCycle:
        ∀ {d x},
          ⟨d, x⟩ ∈ internalCycle →
          (internalCause: Cause Pair) →
          IsWeakCause
            pairSalgebra
            internalCause
            d
            (theInternalDefList.getDef x) →
          IsCauseInapplicable
            pairSalgebra
            theExternalDefList.toDefList
            (externalOfInternalCycle internalCycle)
            (theSetOfInternalCause internalCause))
    :
      Out
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      Out.intro
        (externalOfInternalCycle internalCycle)
        (fun
          {dd xx}
          inInternalCycle
          externalCause
          isCauseExternal
        =>
          inInternalCycle.elim
            (fun ⟨xEq, vvI, inCycle, dEq⟩ =>
              let isCauseExternal:
                IsWeakCause
                  pairSalgebra
                  externalCause
                  (Pair.pair vvI.x vvI.d)
                  (theExternalDefList.getDef uniDefList.theSet)
              := by
                rw [xEq.symm]
                rw [show Pair.pair vvI.x vvI.d = dd from dEq.symm]
                exact isCauseExternal
              
              (isWeakIntOrInappExtOfExt inCycle isCauseExternal).elim
                (fun isCauseInternal =>
                  let isInapp :=
                    isEmptyCycle
                      inCycle
                      (internalOfExternalCause externalCause)
                      isCauseInternal
                  
                  isInapp.toSuperCause
                    (causeExtIntExtSubset externalCause))
                id)
            (fun notPos =>
              -- If the cause's goal is not a member, then the
              -- cause musn't be satisfied, ergo cannot be
              -- applicable either.
              
              let notSat:
                Not
                  (externalCause.IsWeaklySatisfiedBy
                    uniDefList.theExternalWfm
                    uniDefList.theExternalWfm)
              :=
                notPos ∘ inwWfmDef.toInwWfm ∘ isCauseExternal
              
              let isInapp :=
                Cause.IsWeaklySatisfiedBy.toIsInapplicable
                  notSat
              
              open IsCauseInapplicable in
              isInapp.rec
                (fun inCins notPos =>
                  blockedContextIns
                    externalCause
                    inCins
                    (Or.inr notPos))
                (fun inBins notPos =>
                  blockedBackgroundIns
                    externalCause
                    inBins
                    (Out.isComplete _ _ notPos))
                (fun inBout isDef =>
                  blockedBackgroundOut
                    externalCause
                    inBout
                    (Ins.isComplete _ _ isDef))))
        (Or.inl ⟨rfl, _, inCycle, rfl⟩)
    
    def inEmptyCycleExternalToOutInternal
      {externalCycle: Set (ValVar Pair)}
      {d: Pair}
      {x: Nat}
      (inExternalCycle:
        ⟨Pair.pair x d, uniDefList.theSet⟩ ∈ externalCycle)
      (isEmptyCycle:
        ∀ {d x},
          ⟨Pair.pair x d, uniDefList.theSet⟩ ∈ externalCycle →
          (externalCause: Cause Pair) →
          IsWeakCause
            pairSalgebra
            externalCause
            (Pair.pair x d)
            (theExternalDefList.getDef uniDefList.theSet) →
          IsCauseApplicalbeExceptForTheSet
            externalCycle
            externalCause →
          IsCauseInapplicable
            pairSalgebra
            theInternalDefList
            (internalOfExternalCycle externalCycle)
            (internalOfExternalCause externalCause))
    :
      Out
        pairSalgebra
        theInternalDefList
        d
        x
    :=
      Out.intro
        (internalOfExternalCycle externalCycle)
        (fun inInternalCycle causeInternal isCauseInternal =>
          sorry)
        inExternalCycle
    
    
    /-
      This function invokes the induction principle whose inductive
      steps are `isCauseInternalToInsExternal` and
      `inEmptyCycleInternalToOutExternal`. (`IsCauseInapplicable`
      is handled here as well.)
    -/
    def insInternalToInsExternal
      (ins: Ins pairSalgebra theInternalDefList d x)
    :
      Ins
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      -- Cannot use structural recursion on mutual inductives :(
      open IsCauseInapplicable in
      open IsInExternalCause in
      ins.rec
        (motive_1 :=
          fun d x _ =>
            Ins
              pairSalgebra
              theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseInapplicable
              pairSalgebra
              theExternalDefList.toDefList
              (externalOfInternalCycle cycle)
              (theSetOfInternalCause cause))
        (motive_3 :=
          fun d x _ =>
            Out
              pairSalgebra
              theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (fun _ _ _ isCause _ _ _ =>
          isCauseInternalToInsExternal isCause)
        (fun cause _ _ inCins inCycle =>
          blockedContextIns
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).contextIns
            from
              And.intro rfl ⟨_, inCins, rfl⟩)
            (show _ ∈ externalOfInternalCycle _ from
              Or.inl ⟨rfl, _, inCycle, rfl⟩))
        (fun cause _ _ inBins _ ihOut =>
          blockedBackgroundIns
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).backgroundIns
            from
              And.intro rfl ⟨_, inBins, rfl⟩)
            ihOut)
        (fun cause _ _ inBout _ ihIns =>
          blockedBackgroundOut
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).backgroundOut
            from
              And.intro rfl ⟨_, inBout, rfl⟩)
            ihIns)
        (fun _ _ => inEmptyCycleInternalToOutExternal)
    
    def outInternalToOutExternal
      (out: Out pairSalgebra theInternalDefList d x)
    :
      Out
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair (fromNat x) d)
        uniDefList.theSet
    :=
      -- Cannot use structural recursion on mutual inductives :(
      open IsCauseInapplicable in
      open IsInExternalCause in
      out.rec
        (motive_1 :=
          fun d x _ =>
            Ins
              pairSalgebra
              theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseInapplicable
              pairSalgebra
              theExternalDefList.toDefList
              (externalOfInternalCycle cycle)
              (theSetOfInternalCause cause))
        (motive_3 :=
          fun d x _ =>
            Out
              pairSalgebra
              theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (fun _ _ _ isCause _ _ _ =>
          isCauseInternalToInsExternal isCause)
        (fun cause _ _ inCins inCycle =>
          blockedContextIns
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).contextIns
            from
              And.intro rfl ⟨_, inCins, rfl⟩)
            (show _ ∈ externalOfInternalCycle _ from
              Or.inl ⟨rfl, _, inCycle, rfl⟩))
        (fun cause _ _ inBins _ ihOut =>
          blockedBackgroundIns
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).backgroundIns
            from
              And.intro rfl ⟨_, inBins, rfl⟩)
            ihOut)
        (fun cause _ _ inBout _ ihIns =>
          blockedBackgroundOut
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).backgroundOut
            from
              And.intro rfl ⟨_, inBout, rfl⟩)
            ihIns)
        (fun _ _ => inEmptyCycleInternalToOutExternal)
    
    
    def insExternalToInsInternal
      (ins:
        Ins
          pairSalgebra
          theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Ins pairSalgebra theInternalDefList d x
    :=
      open IsCauseInapplicable in
      ins.rec
        (motive_1 :=
          fun d x _ =>
            x = uniDefList.theSet →
            (xInt: Nat) →
            (dInt: Pair) →
            d = Pair.pair xInt dInt →
            Ins pairSalgebra theInternalDefList dInt xInt)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseApplicalbeExceptForTheSet cycle cause →
            IsCauseInapplicable
              pairSalgebra
              theInternalDefList
              (internalOfExternalCycle cycle)
              (internalOfExternalCause cause))
        (motive_3 :=
          fun d x _ =>
            x = uniDefList.theSet →
            (xInt: Nat) →
            (dInt: Pair) →
            d = Pair.pair xInt dInt →
            Out pairSalgebra theInternalDefList dInt xInt)
        (fun _ _ _ isCause
          cinsInsExternal binsInsExternal boutOutExternal
          cinsInsInternal binsInsInternal boutOutInternal
          xEq _ _ dEq
        =>
          isCauseExternalToInsInternal
            (xEq ▸ dEq ▸ isCause)
            cinsInsExternal
            binsInsExternal
            boutOutExternal
            (cinsInsInternal · rfl _ _ rfl)
            (binsInsInternal · rfl _ _ rfl)
            (boutOutInternal · rfl _ _ rfl))
        (fun {cycle} cause _dd xx inCins inCycle isApp =>
          if h: xx = uniDefList.theSet then
            let ⟨n, p, eq⟩ := isApp.contextInsIsOkEq inCins h
            blockedContextIns
              (internalOfExternalCause cause)
              (show ⟨p, n⟩ ∈ _ from show
                cause.contextIns
                  ⟨pair (fromNat n) p, uniDefList.theSet⟩
              from
                eq ▸ h ▸ inCins)
              (show ⟨p, n⟩ ∈ _ from show
                cycle ⟨pair (fromNat n) p, uniDefList.theSet⟩
              from
                eq ▸ h ▸ inCycle)
          else
            let isPos := isApp.contextInsIsOkNeq inCins h
            let notPos := isApp.cycleIsOutNeq inCycle h
            
            False.elim (notPos isPos))
        (fun cause _dd xx inBins isOut ihOut isApp =>
          if h: xx = uniDefList.theSet then
            let ⟨n, p, eq⟩ := isApp.backgroundInsIsOkEq inBins h
            let isOut := ihOut h n p eq
            blockedBackgroundIns
              (internalOfExternalCause cause)
              (show
                ⟨p, n⟩
                  ∈
                (internalOfExternalCause cause).backgroundIns
              from show
                cause.backgroundIns
                  ⟨pair (fromNat n) p, uniDefList.theSet⟩
              from
                eq ▸ h ▸ inBins)
              isOut
          else
            let isPos := isApp.backgroundInsIsOkNeq inBins h
            
            False.elim (isOut.isSound isPos))
        (fun cause _dd xx inBout isIns ihIns isApp =>
          if h: xx = uniDefList.theSet then
            let ⟨n, p, eq⟩ := isApp.backgroundOutIsOkEq inBout h
            let isIns := ihIns h n p eq
            blockedBackgroundOut
              (internalOfExternalCause cause)
              (show
                ⟨p, n⟩
                  ∈
                (internalOfExternalCause cause).backgroundOut
              from show
                cause.backgroundOut
                  ⟨pair (fromNat n) p, uniDefList.theSet⟩
              from
                eq ▸ h ▸ inBout)
              isIns
          else
            let notDef := isApp.backgroundOutIsOkNeq inBout h
            
            False.elim (notDef isIns.isSound))
        (fun _ _ inCycle isEmptyCycle xEq _ _ dEq =>
          inEmptyCycleExternalToOutInternal
            (xEq ▸ dEq ▸ inCycle)
            isEmptyCycle)
        rfl
        x
        d
        rfl
    
    def outExternalToOutInternal
      (out:
        Out
          pairSalgebra
          theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Out pairSalgebra theInternalDefList d x
    :=
      sorry -- TODO out.rec, like above
    
    
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
            Function.contraAB
              fun outValExternal =>
                let out := Out.isComplete _ _ outValExternal
                (outInternalToOutExternal out).isSound
      }
    
    def theInternalValuation.isLeWfm:
      theInternalValuation ⊑ theInternalWfm
    :=
      fun _ => {
        defLe :=
          fun _ insValInternal =>
            let ins := Ins.isComplete _ _ insValInternal
            (insExternalToInsInternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraAB
              fun outValInternal =>
                let out := Out.isComplete _ _ outValInternal
                (outExternalToOutInternal out).isSound
      }
    
    def theInternalValuation.eqWfm:
      theInternalValuation = theInternalWfm
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ isLeWfm isGeWfm
    
    def isUniversal
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨x, s3EqWfm⟩ := theInternalDefList.hasAllDefinable s3 isDef
      
      ⟨
        x,
        s3EqWfm ▸ theInternalValuation.eqWfm ▸ rfl
      ⟩
    
    -- TODO an explicit proof that `uniSet3` is definable?
    
    -- TODO roadmap to publishing the repo:
    -- 0. finish this volume
    -- 1. clean up the `HM` folder
    -- 2. and make it public :tada:
    
  end uniSet3
end Pair
