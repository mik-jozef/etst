/-
  The first section of Chapter 9. See the zeroth section.
-/

import UniSet3.Ch9_S0_InternalLe
import Utils.InwExternal


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    
    inductive MotiveIns
      (d: Pair)
      (x: Nat)
    :
      Prop
    |
      interp
        (xEq: x = uniDefList.interpretation)
        (insInternal:
          ∀ (boundVars: List (ValVar Pair))
            (expr: Expr)
            (dd: Pair)
          ,
            Eq
              d
              (pair
                (boundVarsEncoding boundVars)
                (pair (exprToEncoding expr) dd)) →
            (Set3.defMem
              (expr.interpretation
                pairSalgebra
                (theInternalWfm.withBoundVars boundVars)
                (theInternalWfm.withBoundVars boundVars))
              dd))
    |
      theSet
        (xEq: x = uniDefList.theSet)
        (insInternal:
          ∀ (dd: Pair) (xx: Nat),
           d = pair xx dd →
           Ins pairSalgebra theInternalDefList dd xx)
    |
      other
        (neqInterp: x ≠ uniDefList.interpretation)
        (neqSet: x ≠ uniDefList.theSet)
    
    inductive MotiveOut
      (d: Pair)
      (x: Nat)
    :
      Prop
    |
      interp
        (xEq: x = uniDefList.interpretation)
        (outInternal:
          ∀ (boundVars: List (ValVar Pair))
            (expr: Expr)
            (dd: Pair)
          ,
            Eq
              d
              (pair
                (boundVarsEncoding boundVars)
                (pair (exprToEncoding expr) dd)) →
            (Not
              (Set3.posMem
                (expr.interpretation
                  pairSalgebra
                  (theInternalWfm.withBoundVars boundVars)
                  (theInternalWfm.withBoundVars boundVars))
                dd)))
    |
      theSet
        (xEq: x = uniDefList.theSet)
        (outInternal:
          ∀ (dd: Pair) (xx: Nat),
           d = pair xx dd →
           Out pairSalgebra theInternalDefList dd xx)
    |
      other
        (neqInterp: x ≠ uniDefList.interpretation)
        (neqSet: x ≠ uniDefList.theSet)
    
    inductive MotiveInapplicable
      (externalCycle: Set (ValVar Pair))
      (externalCause: Cause Pair)
    :
      Prop
    |
      blockedCins
      {d x}
      (inContextIns: ⟨d, x⟩ ∈ externalCause.contextIns)
      (inCycle: ⟨d, x⟩ ∈ externalCycle)
    :
      MotiveInapplicable externalCycle externalCause
    |
      blockedBins
      {d x}
      (inBins: ⟨d, x⟩ ∈ externalCause.backgroundIns)
      (isOut:
        Out
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          d
          x)
      (motiveOut: MotiveOut d x)
    :
      MotiveInapplicable externalCycle externalCause
    |
      blockedBout
      {d x}
      (inBout: ⟨d, x⟩ ∈ externalCause.backgroundOut)
      (isIns:
        Ins
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          d
          x)
      (motiveIns: MotiveIns d x)
    :
      MotiveInapplicable externalCycle externalCause
    
    
    def internalOfExternalCycle
      (externalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    :=
      fun ⟨d, x⟩ =>
        externalCycle ⟨Pair.pair x d, uniDefList.theSet⟩
    
    
    def isCauseExternalToInsInternal.boundVar
      (isBound:
        IsGetBound (boundVarsEncoding boundVars) (fromNat x) d)
    :
      Set3.defMem
        (interpretation
          pairSalgebra
          (theInternalWfm.withBoundVars boundVars)
          (theInternalWfm.withBoundVars boundVars)
        (var x))
        d
    :=
      let boundVarsEnc := boundVarsEncoding boundVars
      let encEq: boundVarsEnc = boundVarsEncoding boundVars := rfl
      match h: boundVars, hEnc: boundVarsEnc, encEq ▸ isBound with
      | _ :: _, _, IsGetBound.InHead _ _ _ =>
        let encEq: _ = pair _ _ := h ▸ hEnc ▸ encEq
        let ⟨headEq, _⟩ := Pair.noConfusion encEq And.intro
        let ⟨xEqFromNat, dEq⟩ := Pair.noConfusion headEq And.intro
        let xEq := fromNat.injEq xEqFromNat
        xEq ▸ dEq ▸ insBound
      | _ :: _, _, IsGetBound.InTail isBoundTail _ neq =>
        let encEq: _ = pair _ _ := h ▸ hEnc ▸ encEq
        let ⟨headEq, tailEq⟩ := Pair.noConfusion encEq And.intro
        let ⟨xEqFromNat, _⟩ := Pair.noConfusion headEq And.intro
        insFree
          (boundVar (tailEq ▸ isBoundTail))
          (fun eq => neq (eq ▸ xEqFromNat))
    
    def isCauseExternalToInsInternal.freeVar
      (motiveIns:
        MotiveIns ((fromNat x).pair d) uniDefList.theSet)
      (notBound: ¬ IsBound boundVars x)
    :
      Set3.defMem
        (interpretation
          pairSalgebra
          (theInternalWfm.withBoundVars boundVars)
          (theInternalWfm.withBoundVars boundVars)
        (var x))
        d
    :=
      match boundVars, motiveIns with
      | [], MotiveIns.theSet _ ins => (ins d x rfl).isSound
      | ⟨dB, xB⟩ :: _, _ =>
        insFree
          (freeVar motiveIns (IsBound.Not.notBoundTail notBound))
          (fun eq =>
            let isBound :=
              IsGetBound.InHead (fromNat.isNatEncoding xB) _ _
            notBound ⟨dB, (eq ▸ isBound)⟩)
    
    def isCauseExternalToInsInternal.interp
      (isCauseExternal:
        IsStrongCause
          pairSalgebra
          externalCause
          (pair
            (boundVarsEncoding boundVars)
            (pair
              (exprToEncoding expr)
              d))
          (uniDefList.theExternalDefList.getDef
            uniDefList.interpretation))
      (externalCauseIsSat:
        externalCause.IsStronglySatisfiedBy
          uniDefList.theExternalWfm
          uniDefList.theExternalWfm)
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.contextIns →
          MotiveIns d x)
      (_binsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundIns →
          MotiveIns d x)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundOut →
          MotiveOut d x)
    :
      Set3.defMem
        (interpretation
          pairSalgebra
          (theInternalWfm.withBoundVars boundVars)
          (theInternalWfm.withBoundVars boundVars)
          expr)
        d
    :=
      match expr with
      | Expr.var _ =>
        let boundOrFree :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalVar
        boundOrFree.elim
          (fun isBoundInCause =>
            let insBound :=
              externalCauseIsSat.contextInsHold isBoundInCause
            let isBound := Inw.toIsGetBound insBound.toPos
            boundVar isBound)
          (fun ⟨insTheSet, notBound⟩ =>
            let notBound isBound :=
              let ⟨d, isGetBound⟩ := isBound
              notBound ⟨
                d,
                fun inBout =>
                  externalCauseIsSat.backgroundOutHold
                    inBout
                    (insGetBound isGetBound).toInw,
              ⟩
            freeVar (cinsIns insTheSet) notBound)
      | Expr.op pairSignature.Op.zero _ =>
        let dEqZero :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalZero
        dEqZero ▸ rfl
      | Expr.op pairSignature.Op.pair args =>
        let ⟨dL, dR, dEq, inCinsL, inCinsR⟩ :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalPair
        match cinsIns inCinsL, cinsIns inCinsR with
        | MotiveIns.interp _ insL, MotiveIns.interp _ insR =>
          dEq ▸
          insPair
            (insL boundVars (args ArityTwo.zth) dL rfl)
            (insR boundVars (args ArityTwo.fst) dR rfl)
      | Expr.un left rite =>
        let inCins :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalUn
        inCins.elim
          (fun inCinsL =>
            match cinsIns inCinsL with
            | MotiveIns.interp _ insL =>
              insUnL _ (insL boundVars left d rfl))
          (fun inCinsR =>
            match cinsIns inCinsR with
            | MotiveIns.interp _ insR =>
              insUnR _ (insR boundVars rite d rfl))
      | Expr.ir left rite =>
        let ⟨inCinsL, inCinsR⟩ :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalIr
        match cinsIns inCinsL, cinsIns inCinsR with
        | MotiveIns.interp _ insL, MotiveIns.interp _ insR =>
          insIr
            (insL boundVars left d rfl)
            (insR boundVars rite d rfl)
      | Expr.cpl expr =>
        let inBout :=
          Not.dne
            (isCauseExternal.hurrDurrElim
              externalCauseIsSat.toIsConsistent
              fun isDef => elimDefExternalCpl isDef)
        match boutOut inBout with
        | MotiveOut.interp _ inw =>
          inw boundVars expr d rfl
      | Expr.ifThen cond expr =>
        let ⟨⟨dC, inCinsCond⟩, inCinsExpr⟩ :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalIfThen
        match cinsIns inCinsCond, cinsIns inCinsExpr with
        | MotiveIns.interp _ insCond, MotiveIns.interp _ insExpr =>
          insIfThen
            (insCond boundVars cond dC rfl)
            (insExpr boundVars expr d rfl)
      | Expr.Un x body =>
        let ⟨dX, inCins⟩ :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalArbUn
        match cinsIns inCins with
        | MotiveIns.interp _ ins =>
          insArbUn dX (ins (⟨dX, x⟩ :: boundVars) body d rfl)
      | Expr.Ir x body =>
        let inCins :=
          isCauseExternal.hurrDurrElim
            externalCauseIsSat.toIsConsistent
            elimDefExternalArbIr
        insArbIr fun dX =>
          match cinsIns (inCins dX) with
          | MotiveIns.interp _ ins =>
            ins (⟨dX, x⟩ :: boundVars) body d rfl
    
    def isCauseExternalToInsInternal
      (isCauseExternal:
        IsStrongCause
          pairSalgebra
          externalCause
          d
          (uniDefList.theExternalDefList.getDef x))
      (externalCauseIsSat:
        externalCause.IsStronglySatisfiedBy
          uniDefList.theExternalWfm
          uniDefList.theExternalWfm)
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.contextIns →
          MotiveIns d x)
      (binsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundIns →
          MotiveIns d x)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ externalCause.backgroundOut →
          MotiveOut d x)
    :
      MotiveIns d x
    :=
      if hInterp: x = uniDefList.interpretation then
        MotiveIns.interp
          hInterp
          fun _boundVars _expr _dd dEq =>
            isCauseExternalToInsInternal.interp
              (hInterp ▸ dEq ▸ isCauseExternal)
              externalCauseIsSat
              cinsIns
              binsIns
              boutOut
      else if hSet: x = uniDefList.theSet then
        MotiveIns.theSet
          hSet
          fun dd xx dEq =>
            let isCause:
              IsStrongCause _ _ _ uniDefList.theSet.expr
            :=
              hSet ▸ dEq ▸ isCauseExternal
            
            let motiveInsInterp :=
              isCause.hurrDurrElim
                externalCauseIsSat.toIsConsistent
                fun ins =>
                  let ⟨_xxAlias, _, ins⟩ := insUnDomElim ins
                  let ⟨ins500, ins⟩ := insPairElim ins
                  let xxEq := insBoundElim ins500
                  let ⟨_exprXx, insFn, insArg⟩ :=
                    insCallExprElim ins
                  let ⟨_zeroAlias, insInterp, insZero⟩ :=
                    insCallExprElim insFn
                  let zeroEq := insZeroElim insZero
                  let insTheDefList :=
                    insCallElimBound insArg rfl nat502Neq500
                  let insWfmTheDefList :=
                    xxEq ▸
                    externalCauseIsSat.contextInsHold insTheDefList
                  let isDlExpr :=
                    Inw.toIsTheDefListExpr insWfmTheDefList.toPos
                  let exprXxEq :=
                    IsTheDefListExprPair.getNthExpr.eq isDlExpr rfl
                  zeroEq ▸
                  exprXxEq ▸
                  cinsIns insInterp
            match motiveInsInterp with
            | MotiveIns.interp _ isDef =>
              let insOfEq :=
                isDef [] (theInternalDefList.getDef xx) dd
              let exprEncEq := (theInternalDefList.eqEnc xx).symm
              let ins :=
                insOfEq (Pair.eq rfl (Pair.eq exprEncEq rfl))
              Ins.isComplete _ _ (insWfmDefToIns ins)
      else
        MotiveIns.other hInterp hSet
    
    
    def IsEmptyCycle
      (externalCycle: Set (ValVar Pair))
    :
      Prop
    :=
      {d: Pair} →
      {x: Nat} →
      ⟨d, x⟩ ∈ externalCycle →
      (externalCause: Cause Pair) →
      IsWeakCause
        pairSalgebra
        externalCause
        d
        (uniDefList.theExternalDefList.getDef x) →
      IsCauseInapplicable
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        externalCycle
        externalCause
    
    def IsEmptyCycleIh (externalCycle: Set (ValVar Pair)): Prop :=
      {d: Pair} →
      {x: Nat} →
      ⟨d, x⟩ ∈ externalCycle →
      (externalCause: Cause Pair) →
      IsWeakCause
        pairSalgebra
        externalCause
        d
        (uniDefList.theExternalDefList.getDef x) →
      MotiveInapplicable externalCycle externalCause
    
    
    def isInappOfInappWithBounds
      (isInapp:
        IsCauseInappExtended
          pairSalgebra
          theInternalDefList
          (internalOfExternalCycle externalCycle)
          (internalCause.union
            (Cause.ofValPos
              (theInternalWfm.withBoundVars boundVars)
              Valuation.empty)))
      (fulfillsBounds: internalCause.FulfillsBoundVars boundVars)
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        internalCause
    :=
      open IsCauseInappExtended in
      match isInapp with
      | cinsFailsCycle (Or.inl inCins) inCycle =>
        cinsFailsCycle inCins inCycle
      | cinsFailsOut (Or.inl inCins) out =>
        cinsFailsOut inCins out
      | binsFails (Or.inl inBins) out =>
        binsFails inBins out
      | @binsFails _ _ _ _ _ dd xx (Or.inr inBins) out =>
        if h: IsBound boundVars xx then
          let ⟨dBound, isGetBound⟩ := h
          let eqAtXx :=
            Valuation.withBoundVars.eqOfIsGetBound
              theInternalWfm isGetBound
          let dEq: (Set3.just dBound).posMem dd :=
            eqAtXx ▸ inBins
          let fulfillsBound := fulfillsBounds rfl isGetBound
          let dIn := dEq ▸ fulfillsBound.binsFulfills
          binsFails dIn out
        else
          let eqAtXx :=
            Valuation.withBoundVars.eqOrigOfIsFree
              theInternalWfm h
          let inBins: (theInternalWfm xx).posMem dd :=
            eqAtXx ▸ inBins
          out.nopePos inBins
      | boutFails (Or.inl inBout) ins =>
        boutFails inBout ins
      | @boutFails _ _ _ _ _ dd xx (Or.inr inBout) ins =>
        if h: IsBound boundVars xx then
          let ⟨dBound, isGetBound⟩ := h
          let eqAtXx :=
            Valuation.withBoundVars.eqOfIsGetBound
              theInternalWfm isGetBound
          let notDef: ¬ (Set3.just dBound).defMem dd :=
            eqAtXx ▸ inBout
          let fulfillsBound := fulfillsBounds rfl isGetBound
          let dIn := fulfillsBound.boutFulfills dd notDef
          boutFails dIn ins
        else
          let eqAtXx :=
            Valuation.withBoundVars.eqOrigOfIsFree
              theInternalWfm h
          let inBout: ¬ (theInternalWfm xx).defMem dd :=
            eqAtXx ▸ inBout
          ins.nopeNotDef inBout
    
    def allInternalInapplicableInterp
      (isEmptyCycle: IsEmptyCycle externalCycle)
      (isEmptyCycleIh: IsEmptyCycleIh externalCycle)
      (inCycle: externalCycle ⟨
        pair
          (boundVarsEncoding boundVars)
          (pair (exprToEncoding expr) d),
        uniDefList.interpretation
      ⟩)
      {internalCause: Cause Pair}
      (fulfillsBounds: internalCause.FulfillsBoundVars boundVars)
      (isCause: IsWeakCause pairSalgebra internalCause d expr)
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        internalCause
    :=
      open MotiveInapplicable in
      open IsCauseInappExtended in
      match expr with
      |
        Expr.var xx =>
        let dInCins := isCause.elimVar
        
        if h: IsBound boundVars xx then
          let ⟨dBound, isGetBound⟩ := h
          let satBound := fulfillsBounds rfl isGetBound
          let dEq: d = dBound := satBound.cinsSat _ dInCins rfl
          let out := Out.intro externalCycle isEmptyCycle inCycle
          out.nopePos (InwExternal.boundVar (dEq ▸ isGetBound))
        else
          let isInapp :=
            isEmptyCycleIh
              inCycle
              (InwExternal.causeFreeVar boundVars xx d)
              (InwExternal.causeFreeVarIsCause boundVars xx d)
          
          match isInapp with
          | blockedCins (Or.inl ⟨xEq, dNat⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopePos (xEq ▸ (insNatEncoding dNat).toPos)
          | blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
            cinsFailsCycle
              dInCins
              (show externalCycle _ from xEq ▸ dEq ▸ inCycle)
          | blockedBout ⟨xEq, ⟨dB, dEq⟩⟩ isIns _ =>
            let isIns := xEq ▸ dEq ▸ isIns
            let inwGetBound := isIns.isSound.toPos
            False.elim (h ⟨dB, Inw.toIsGetBound inwGetBound⟩)
      |
        Expr.op pairSignature.Op.zero _ =>
        let dEq := isCause.elimZeroExpr
        nomatch
          isEmptyCycleIh
            inCycle
            Cause.empty
            (dEq ▸ InwExternal.isCauseZero boundVars)
      |
        Expr.op pairSignature.Op.pair args =>
        let left := args ArityTwo.zth
        let rite := args ArityTwo.fst
        let ⟨dL, dR, dEq, isCauseL, isCauseR⟩ :=
          isCause.elimPairExprEx
        
        let isInapp :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causePair boundVars left rite dL dR)
            (dEq ▸
            InwExternal.isCausePair boundVars left rite dL dR)
        
        match isInapp with
        | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
          let out := Out.intro externalCycle isEmptyCycle inCycle
          out.nopePos (xEq ▸ (insExprEncoding isExpr).toPos)
        | blockedCins (Or.inr (Or.inl ⟨xEq, dEq⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEq ▸ inCycle)
            fulfillsBounds
            isCauseL
        | blockedCins (Or.inr (Or.inr ⟨xEq, dEq⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEq ▸ inCycle)
            fulfillsBounds
            isCauseR
      |
        Expr.un left rite =>
        let isInappL :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causeUn boundVars left d)
            (InwExternal.isCauseUnL boundVars left rite d)
        
        let isInappR :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causeUn boundVars rite d)
            (InwExternal.isCauseUnR boundVars left rite d)
        
        let inCycleL :=
          match isInappL with
          | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopePos (xEq ▸ (insExprEncoding isExpr).toPos)
          | blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
            xEq ▸ dEq ▸ inCycle
        
        let inCycleR :=
          match isInappR with
          | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopePos (xEq ▸ (insExprEncoding isExpr).toPos)
          | blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
            xEq ▸ dEq ▸ inCycle
        
        let updatedInternalWfm :=
          theInternalWfm.withBoundVars boundVars
        
        let isInapp :=
          match isCause.elimUn updatedInternalWfm with
          | Or.inl isCauseL =>
              allInternalInapplicableInterp
                isEmptyCycle
                isEmptyCycleIh
                inCycleL
                (fulfillsBounds.unionSat
                  (Cause.SatisfiesBoundVars.backgroundWithBoundsSat
                    _ boundVars))
                isCauseL
          | Or.inr isCauseR =>
              allInternalInapplicableInterp
                isEmptyCycle
                isEmptyCycleIh
                inCycleR
                (fulfillsBounds.unionSat
                  (Cause.SatisfiesBoundVars.backgroundWithBoundsSat
                    _ boundVars))
                isCauseR
        
        isInappOfInappWithBounds isInapp fulfillsBounds
      |
        Expr.ir left rite =>
        let ⟨isCauseL, isCauseR⟩ := isCause.elimIr
        
        let isInapp :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causeIr boundVars left rite d)
            (InwExternal.isCauseIr boundVars left rite d)
        
        match isInapp with
        | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
          let out := Out.intro externalCycle isEmptyCycle inCycle
          out.nopePos (xEq ▸ (insExprEncoding isExpr).toPos)
        | blockedCins (Or.inr (Or.inl ⟨xEq, dEqL⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEqL ▸ inCycle)
            fulfillsBounds
            isCauseL
        | blockedCins (Or.inr (Or.inr ⟨xEq, dEqR⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEqR ▸ inCycle)
            fulfillsBounds
            isCauseR
      |
        Expr.cpl expr =>
        sorry
      |
        Expr.ifThen cond expr =>
        sorry
      |
        Expr.Un x body =>
        sorry
      |
        Expr.Ir x body =>
        sorry
    
    def allInternalInapplicableTheSet
      (isEmptyCycle: IsEmptyCycle externalCycle)
      (isEmptyCycleIh: IsEmptyCycleIh externalCycle)
      (inCycle: ⟨d, x⟩ ∈ internalOfExternalCycle externalCycle)
      (isCause:
        IsWeakCause
          pairSalgebra
          internalCause
          d
          (theInternalDefList.getDef x))
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        internalCause
    :=
      let isInapp :=
        isEmptyCycleIh
          inCycle
          (InwExternal.causeTheSet x d)
          (InwExternal.causeTheSetIsCause x d)
      
      open MotiveInapplicable in
      match isInapp with
      | blockedCins (Or.inl ⟨xEq, dNat⟩) inCycle =>
        let out := Out.intro externalCycle isEmptyCycle inCycle
        out.nopePos (xEq ▸ (insNatEncoding dNat).toPos)
      | blockedCins (Or.inr (Or.inl ⟨xEq, dDlExpr⟩)) inCycle =>
        let out := Out.intro externalCycle isEmptyCycle inCycle
        out.nopePos (xEq ▸ (insTheDefListExpr dDlExpr).toPos)
      | blockedCins (Or.inr (Or.inr ⟨xEq, dEq⟩)) inCycle =>
        allInternalInapplicableInterp
          (boundVars := [])
          isEmptyCycle
          isEmptyCycleIh
          (theInternalDefList.eqEnc x ▸ xEq ▸ dEq ▸ inCycle)
          nofun
          isCause
    
    def isEmptyCycleExternalToOutInternal
      (isEmptyCycle: IsEmptyCycle externalCycle)
      (isEmptyCycleIh: IsEmptyCycleIh externalCycle)
      (inCycle: ⟨d, x⟩ ∈ externalCycle)
    :
      MotiveOut d x
    :=
      if hInterp: x = uniDefList.interpretation then
        MotiveOut.interp
          hInterp
          fun boundVars expr _dd dEq isPos =>
            sorry
      else if hSet: x = uniDefList.theSet then
        MotiveOut.theSet
          hSet
          fun dd xx dEq =>
            Out.intro4
              (internalOfExternalCycle externalCycle)
              (fun inCycle cause isCause =>
                allInternalInapplicableTheSet
                  isEmptyCycle
                  isEmptyCycleIh
                  inCycle
                  isCause)
              (show externalCycle _ from hSet ▸ dEq ▸ inCycle)
      else
        MotiveOut.other hInterp hSet
    
    def insExternalToInsInternal
      (ins:
        Ins
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Ins pairSalgebra theInternalDefList d x
    :=
      let insInternal :=
        ins.rec
          (motive_1 := fun d x _ => MotiveIns d x)
          (motive_2 :=
            fun cycle cause _ => MotiveInapplicable cycle cause)
          (motive_3 := fun d x _ => MotiveOut d x)
          (fun _ _ _ isCause cinsSat binsSat boutSat =>
            isCauseExternalToInsInternal isCause {
              contextInsHold := Ins.isSound ∘ cinsSat
              backgroundInsHold := Ins.isSound ∘ binsSat
              backgroundOutHold := Out.isSound ∘ boutSat
            })
          (fun _ _ _ inCins inCycle =>
            MotiveInapplicable.blockedCins inCins inCycle)
          (fun _ _ _ inBins isOut motiveOut =>
            MotiveInapplicable.blockedBins inBins isOut motiveOut)
          (fun _ _ _ inBout isIns motiveIns =>
            MotiveInapplicable.blockedBout inBout isIns motiveIns)
          (fun _ isEmptyCycle inCycle isEmptyCycleIh =>
            isEmptyCycleExternalToOutInternal
              isEmptyCycle isEmptyCycleIh inCycle)
      
      match insInternal with
      | MotiveIns.theSet _ insInternal => insInternal d x rfl
    
    def outExternalToOutInternal
      (out:
        Out
          pairSalgebra
          uniDefList.theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Out pairSalgebra theInternalDefList d x
    :=
      let outInternal :=
        out.rec
          (motive_1 := fun d x _ => MotiveIns d x)
          (motive_2 :=
            fun cycle cause _ => MotiveInapplicable cycle cause)
          (motive_3 := fun d x _ => MotiveOut d x)
          (fun _ _ _ isCause cinsSat binsSat boutSat =>
            isCauseExternalToInsInternal isCause {
              contextInsHold := Ins.isSound ∘ cinsSat
              backgroundInsHold := Ins.isSound ∘ binsSat
              backgroundOutHold := Out.isSound ∘ boutSat
            })
          (fun _ _ _ inCins inCycle =>
            MotiveInapplicable.blockedCins inCins inCycle)
          (fun _ _ _ inBins isOut motiveOut =>
            MotiveInapplicable.blockedBins inBins isOut motiveOut)
          (fun _ _ _ inBout isIns motiveIns =>
            MotiveInapplicable.blockedBout inBout isIns motiveIns)
          (fun _ isEmptyCycle inCycle isEmptyCycleIh =>
            isEmptyCycleExternalToOutInternal
              isEmptyCycle isEmptyCycleIh inCycle)
      
      match outInternal with
      | MotiveOut.theSet _ outInternal => outInternal d x rfl
    
    
    def theInternalWfmEncoding.isLeWfm:
      uniDefList.theInternalWfmEncoding ⊑ theInternalWfm
    :=
      fun _ => {
        defLe :=
          fun _ insValExternal =>
            let ins := Ins.isComplete _ _ insValExternal
            (insExternalToInsInternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraAB
              fun outValExternal =>
                let out := Out.isComplete _ _ outValExternal
                (outExternalToOutInternal out).isSound
      }
    
  end uniSet3
end Pair
