/-
  The first section of Chapter 9. See the zeroth section.
-/

import UniSet3.Ch9_S0_InternalLe
import Utils.InwExternal


-- TODO moveto Utils/Cause.lean when you fix IsGetBound.
def Cause.exceptBoundVars
  (cause: Cause Pair)
  (boundVars: List (ValVar Pair))
:
  Cause Pair
:=
  cause.except {
    contextIns := fun ⟨_, x⟩ => Pair.IsBound boundVars x,
    backgroundIns := fun ⟨_, x⟩ => Pair.IsBound boundVars x,
    backgroundOut := fun ⟨_, x⟩ => Pair.IsBound boundVars x,
  }

def Cause.exceptBoundVars.eqEmpty
  (cause: Cause Pair)
:
  cause.exceptBoundVars [] = cause
:=
  Cause.eq
    (Set.eqIffH (Iff.intro And.left (And.intro · nofun)))
    (Set.eqIffH (Iff.intro And.left (And.intro · nofun)))
    (Set.eqIffH (Iff.intro And.left (And.intro · nofun)))

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
    
    
    def isInappOfInappUn
      {internalCause: Cause Pair}
      (isInapp:
        IsCauseInappExtended
          pairSalgebra
          theInternalDefList
          (internalOfExternalCycle externalCycle)
          (Cause.exceptBoundVars
            (internalCause.union
              (Cause.ofValPos
                (theInternalWfm.withBoundVars boundVars)
                Valuation.empty))
              boundVars))
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        (internalCause.exceptBoundVars boundVars)
    :=
      open IsCauseInappExtended in
      match isInapp with
      | cinsFailsCycle ⟨Or.inl inCins, ninBounds⟩ inCycle =>
        cinsFailsCycle ⟨inCins, ninBounds⟩ inCycle
      | cinsFailsOut ⟨Or.inl inCins, ninBounds⟩ out =>
        cinsFailsOut ⟨inCins, ninBounds⟩ out
      | binsFails ⟨Or.inl inBins, ninBounds⟩ out =>
        binsFails ⟨inBins, ninBounds⟩ out
      | @binsFails
        _ _ _ _ _ dd xx ⟨Or.inr inBins, ninBounds⟩ out
      =>
        let eqAtXx :=
          Valuation.withBoundVars.eqOrigOfIsFree
            theInternalWfm ninBounds
        let inBins: (theInternalWfm xx).posMem dd :=
          eqAtXx ▸ inBins
        out.nopePos inBins
      | boutFails ⟨Or.inl inBout, ninBounds⟩ ins =>
        boutFails ⟨inBout, ninBounds⟩ ins
      | @boutFails
        _ _ _ _ _ dd xx ⟨Or.inr inBout, ninBounds⟩ ins
      =>
        let eqAtXx :=
          Valuation.withBoundVars.eqOrigOfIsFree
            theInternalWfm ninBounds
        let inBout: ¬ (theInternalWfm xx).defMem dd :=
          eqAtXx ▸ inBout
        ins.nopeNotDef inBout
    
    def isInappOfInappCpl
      {internalCause: Cause Pair}
      (satisfiesBounds: internalCause.SatisfiesBoundVars boundVars)
      (causeInapp:
        internalCause.IsInapplicable
          Valuation.full.nonmembers
          (theInternalWfm.withBoundVars boundVars))
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        (internalCause.exceptBoundVars boundVars)
    :=
      open IsCauseInappExtended in
      open Cause.IsInapplicable in
      match causeInapp with
      | blockedContextIns _ notInFull =>
        absurd trivial notInFull
      | @blockedBackgroundIns _ _ _ _ xx dd inBins notPos =>
        if h: IsBound boundVars xx then
          let ⟨dBound, isGetBound⟩ := h
          let satBound := satisfiesBounds rfl isGetBound
          let dEq := satBound.binsSat _ inBins rfl
          
          let dNeq: ¬ (Set3.just dBound).posMem dd :=
            Valuation.withBoundVars.eqOfIsGetBound
              theInternalWfm isGetBound ▸
            notPos
          
          absurd dEq dNeq
        else
          let eq := Valuation.withBoundVars.eqOrigOfIsFree
            theInternalWfm h
          let notPos: ¬ (theInternalWfm xx).posMem dd :=
            eq ▸ notPos
          let out := Out.isComplete _ _ notPos
          binsFails ⟨inBins, h⟩ out
      | @blockedBackgroundOut _ _ _ _ xx dd inBout isDef =>
        if h: IsBound boundVars xx then
          let ⟨dBound, isGetBound⟩ := h
          let satBound := satisfiesBounds rfl isGetBound
          let dNeq := satBound.boutSat _ inBout rfl
          
          let dEq: (Set3.just dBound).defMem dd :=
            Valuation.withBoundVars.eqOfIsGetBound
              theInternalWfm isGetBound ▸
            isDef
          
          absurd dEq dNeq
        else
          let eq := Valuation.withBoundVars.eqOrigOfIsFree
            theInternalWfm h
          let isDef: (theInternalWfm xx).defMem dd :=
            eq ▸ isDef
          let ins := Ins.isComplete _ _ isDef
          boutFails ⟨inBout, h⟩ ins
    
    def isInappOfInappArbUn
      {internalCause: Cause Pair}
      (isInapp:
        IsCauseInappExtended
          pairSalgebra
          theInternalDefList
          (internalOfExternalCycle externalCycle)
          (Cause.exceptBoundVars
            ((internalCause.withBound x dX).union
              (Cause.ofValPos
                (theInternalWfm.withBoundVars
                  (⟨dX, x⟩ :: boundVars))
                Valuation.empty))
            (⟨dX, x⟩ :: boundVars)))
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        (internalCause.exceptBoundVars boundVars)
    :=
      open IsCauseInappExtended in
      match isInapp with
      | cinsFailsCycle
        ⟨Or.inl (Or.inl ⟨inCins, _⟩), ninBounds⟩
        inCycle
      =>
        let ninBoundsTail := IsBound.Not.notBoundTail ninBounds
        cinsFailsCycle ⟨inCins, ninBoundsTail⟩ inCycle
      |
        cinsFailsCycle ⟨Or.inl (Or.inr ⟨_, xEq⟩), ninBounds⟩ _
      =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        False.elim (ninBounds ⟨dX, isGetBound⟩)
      |
        cinsFailsOut ⟨Or.inl (Or.inl ⟨inCins, _⟩), ninBins⟩ out
      =>
        let ninBinsTail := IsBound.Not.notBoundTail ninBins
        cinsFailsOut ⟨inCins, ninBinsTail⟩ out
      |
        cinsFailsOut ⟨Or.inl (Or.inr ⟨_, xEq⟩), ninBins⟩ _ =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        False.elim (ninBins ⟨dX, isGetBound⟩)
      |
        binsFails ⟨Or.inl (Or.inl ⟨inBins, _⟩), ninBounds⟩ out =>
        let ninBoundsTail := IsBound.Not.notBoundTail ninBounds
        binsFails ⟨inBins, ninBoundsTail⟩ out
      |
        binsFails ⟨Or.inl (Or.inr ⟨_, xEq⟩), ninBounds⟩ _ =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        
        False.elim (ninBounds ⟨dX, isGetBound⟩)
      |
        @binsFails _ _ _ _ _ dd xx ⟨Or.inr inBins, ninBounds⟩ out
      =>
        let isPos: (theInternalWfm xx).posMem dd :=
          Valuation.withBoundVars.eqOrigOfIsFree
            theInternalWfm ninBounds ▸
          inBins
        
        out.nopePos isPos
      |
        boutFails ⟨Or.inl (Or.inl ⟨inBout, _⟩), ninBounds⟩ ins =>
        let ninBoundsTail := IsBound.Not.notBoundTail ninBounds
        boutFails ⟨inBout, ninBoundsTail⟩ ins
      |
        boutFails ⟨Or.inl (Or.inr ⟨_, xEq⟩), ninBounds⟩ _ =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        False.elim (ninBounds ⟨dX, isGetBound⟩)
      |
        @boutFails _ _ _ _ _ dd xx ⟨Or.inr inBout, ninBounds⟩ ins
      =>
        let isNotDef: ¬ (theInternalWfm xx).defMem dd :=
          Valuation.withBoundVars.eqOrigOfIsFree
            theInternalWfm ninBounds ▸
          inBout
        
        ins.nopeNotDef isNotDef
    
    def isInappOfInappArbIr
      {internalCause: Cause Pair}
      (isInapp:
        IsCauseInappExtended
          pairSalgebra
          theInternalDefList
          (internalOfExternalCycle externalCycle)
          (Cause.exceptBoundVars
            (internalCause.withBound x dX)
            (⟨dX, x⟩ :: boundVars)))
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        (internalCause.exceptBoundVars boundVars)
    :=
      open IsCauseInappExtended in
      match isInapp with
      | cinsFailsCycle ⟨Or.inl ⟨inCins, _⟩, ninBounds⟩ inCycle
      =>
        let ninBoundsTail := IsBound.Not.notBoundTail ninBounds
        cinsFailsCycle ⟨inCins, ninBoundsTail⟩ inCycle
      |
        cinsFailsCycle ⟨Or.inr ⟨_, xEq⟩, ninBounds⟩ _
      =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        False.elim (ninBounds ⟨dX, isGetBound⟩)
      |
        cinsFailsOut ⟨Or.inl ⟨inCins, _⟩, ninBins⟩ out
      =>
        let ninBinsTail := IsBound.Not.notBoundTail ninBins
        cinsFailsOut ⟨inCins, ninBinsTail⟩ out
      |
        cinsFailsOut ⟨Or.inr ⟨_, xEq⟩, ninBins⟩ _ =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        False.elim (ninBins ⟨dX, isGetBound⟩)
      |
        binsFails ⟨Or.inl ⟨inBins, _⟩, ninBounds⟩ out =>
        let ninBoundsTail := IsBound.Not.notBoundTail ninBounds
        binsFails ⟨inBins, ninBoundsTail⟩ out
      |
        binsFails ⟨Or.inr ⟨_, xEq⟩, ninBounds⟩ _ =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        
        False.elim (ninBounds ⟨dX, isGetBound⟩)
      |
        boutFails ⟨Or.inl ⟨inBout, _⟩, ninBounds⟩ ins =>
        let ninBoundsTail := IsBound.Not.notBoundTail ninBounds
        boutFails ⟨inBout, ninBoundsTail⟩ ins
      |
        boutFails ⟨Or.inr ⟨_, xEq⟩, ninBounds⟩ _ =>
        let isGetBound :=
          xEq ▸ IsGetBound.InHead (fromNat.isNatEncoding x) _ _
        False.elim (ninBounds ⟨dX, isGetBound⟩)
    
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
      (satisfiesBounds: internalCause.SatisfiesBoundVars boundVars)
      (isCause: IsWeakCause pairSalgebra internalCause d expr)
    :
      IsCauseInappExtended
        pairSalgebra
        theInternalDefList
        (internalOfExternalCycle externalCycle)
        (internalCause.exceptBoundVars boundVars)
    :=
      let updatedInternalWfm :=
        theInternalWfm.withBoundVars boundVars
      
      open MotiveInapplicable in
      open IsCauseInappExtended in
      match expr with
      |
        Expr.var xx =>
        let dInCins := isCause.elimVar
        
        if h: IsBound boundVars xx then
          let ⟨dBound, isGetBound⟩ := h
          let satBound := satisfiesBounds rfl isGetBound
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
            out.nopeDef (xEq ▸ (insNatEncoding dNat))
          | blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
            cinsFailsCycle
              ⟨dInCins, h⟩
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
          out.nopeDef (xEq ▸ (insExprEncoding isExpr))
        | blockedCins (Or.inr (Or.inl ⟨xEq, dEq⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEq ▸ inCycle)
            satisfiesBounds
            isCauseL
        | blockedCins (Or.inr (Or.inr ⟨xEq, dEq⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEq ▸ inCycle)
            satisfiesBounds
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
            out.nopeDef (xEq ▸ (insExprEncoding isExpr))
          | blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
            xEq ▸ dEq ▸ inCycle
        
        let inCycleR :=
          match isInappR with
          | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopeDef (xEq ▸ (insExprEncoding isExpr))
          | blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
            xEq ▸ dEq ▸ inCycle
        
        let isInapp :=
          match isCause.elimUn updatedInternalWfm with
          | Or.inl isCauseL =>
              allInternalInapplicableInterp
                isEmptyCycle
                isEmptyCycleIh
                inCycleL
                (satisfiesBounds.union
                  (Cause.SatisfiesBoundVars.bWithBoundsSatBoundVars
                    _ boundVars))
                isCauseL
          | Or.inr isCauseR =>
              allInternalInapplicableInterp
                isEmptyCycle
                isEmptyCycleIh
                inCycleR
                (satisfiesBounds.union
                  (Cause.SatisfiesBoundVars.bWithBoundsSatBoundVars
                    _ boundVars))
                isCauseR
        
        isInappOfInappUn isInapp
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
          out.nopeDef (xEq ▸ (insExprEncoding isExpr))
        | blockedCins (Or.inr (Or.inl ⟨xEq, dEqL⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEqL ▸ inCycle)
            satisfiesBounds
            isCauseL
        | blockedCins (Or.inr (Or.inr ⟨xEq, dEqR⟩)) inCycle =>
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            (xEq ▸ dEqR ▸ inCycle)
            satisfiesBounds
            isCauseR
      |
        Expr.cpl expr =>
        let isInappIh :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causeCpl boundVars expr d)
            (InwExternal.isCauseCpl boundVars expr d)
        
        let isDefExpr:
          Set3.defMem
            (expr.interpretation
              pairSalgebra
              (theInternalWfm.withBoundVars boundVars)
              (theInternalWfm.withBoundVars boundVars))
            d
        :=
          open MotiveIns in
          match isInappIh with
          | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopeDef (xEq ▸ (insExprEncoding isExpr))
          | blockedBout (Or.inr ⟨xEq, dEq⟩) _ (interp _ toIsDef) =>
            toIsDef boundVars expr d dEq
        
        let causeInapp :=
          isCause.isInapplicableOfIsNonmember
            (c := Valuation.full)
            (Not.dni isDefExpr)
        
        isInappOfInappCpl satisfiesBounds causeInapp
      |
        Expr.ifThen cond expr =>
        sorry
      |
        Expr.Un x body =>
        let ⟨dX, isCauseBody⟩ :=
          isCause.elimArbUn updatedInternalWfm
        
        let isInappIh :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causeArbUn boundVars x dX body d)
            (InwExternal.isCauseArbUn boundVars x dX body d)
        
        let inCycle :=
          match isInappIh with
          | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopeDef (xEq ▸ (insExprEncoding isExpr))
          | blockedCins (Or.inr (Or.inl ⟨xEq, dEq⟩)) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopeDef (xEq ▸ (insNatEncoding dEq))
          | blockedCins (Or.inr (Or.inr ⟨xEq, dEq⟩)) inCycle =>
            xEq ▸ dEq ▸ inCycle
        
        let isInapp :=
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            inCycle
            (Cause.SatisfiesBoundVars.union
              satisfiesBounds.satWithBound
              (Cause.SatisfiesBoundVars.bWithBoundsSatBoundVars
                theInternalWfm
                (⟨dX, x⟩ :: boundVars)))
            isCauseBody
        
        isInappOfInappArbUn isInapp
      |
        Expr.Ir x body =>
        let isInappIh :=
          isEmptyCycleIh
            inCycle
            (InwExternal.causeArbIr boundVars x body d)
            (InwExternal.isCauseArbIr boundVars x body d)
        
        let ⟨dX, inCycle⟩: ∃ dX, _ :=
          match isInappIh with
          | blockedCins (Or.inl ⟨xEq, isExpr⟩) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopeDef (xEq ▸ (insExprEncoding isExpr))
          | blockedCins (Or.inr (Or.inl ⟨xEq, dEq⟩)) inCycle =>
            let out := Out.intro externalCycle isEmptyCycle inCycle
            out.nopeDef (xEq ▸ (insNatEncoding dEq))
          | blockedCins (Or.inr (Or.inr ⟨d, xEq, dEq⟩)) inCycle => ⟨
            d,
            xEq ▸ dEq ▸ inCycle,
          ⟩
        
        let isInapp :=
          allInternalInapplicableInterp
            isEmptyCycle
            isEmptyCycleIh
            inCycle
            satisfiesBounds.satWithBound
            (isCause.elimArbIr dX)
        
        isInappOfInappArbIr isInapp
    
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
        out.nopeDef (xEq ▸ (insNatEncoding dNat))
      | blockedCins (Or.inr (Or.inl ⟨xEq, dDlExpr⟩)) inCycle =>
        let out := Out.intro externalCycle isEmptyCycle inCycle
        out.nopeDef (xEq ▸ (insTheDefListExpr dDlExpr))
      | blockedCins (Or.inr (Or.inr ⟨xEq, dEq⟩)) inCycle =>
        Cause.exceptBoundVars.eqEmpty internalCause ▸
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
          fun boundVars _expr _dd dEq isPos =>
            let isInapp :=
              allInternalInapplicableInterp
                isEmptyCycle
                isEmptyCycleIh
                (hInterp ▸ dEq ▸ inCycle)
                (Cause.SatisfiesBoundVars.withBoundsSatBoundVars
                  boundVars theInternalWfm)
                (IsWeakCause.ofValPos isPos)
            
            open IsCauseInappExtended in
            match isInapp with
            | @cinsFailsCycle
              _ _ _ _ _ d x ⟨inCins, ninBounds⟩ inCycle
            =>
              let eqOfFree := Valuation.withBoundVars.eqOrigOfIsFree
              let isPos: (theInternalWfm x).posMem d :=
                eqOfFree theInternalWfm ninBounds ▸ inCins
              
              let out :=
                Out.intro4
                  (salg := pairSalgebra)
                  (internalOfExternalCycle externalCycle)
                  (fun inCycle _ isCause =>
                    allInternalInapplicableTheSet
                      isEmptyCycle
                      isEmptyCycleIh
                      inCycle
                      isCause)
                  inCycle
              
              out.nopePos isPos
            | @cinsFailsOut
              _ _ _ _ _ d x ⟨inCins, ninBounds⟩ out
            =>
              let eqOfFree := Valuation.withBoundVars.eqOrigOfIsFree
              let isPos: (theInternalWfm x).posMem d :=
                eqOfFree theInternalWfm ninBounds ▸ inCins
              out.nopePos isPos
            | @binsFails
              _ _ _ _ _ d x ⟨inBins, ninBounds⟩ out
            =>
              let eqOfFree := Valuation.withBoundVars.eqOrigOfIsFree
              let isPos: (theInternalWfm x).posMem d :=
                eqOfFree theInternalWfm ninBounds ▸ inBins
              out.nopePos isPos
            | @boutFails
              _ _ _ _ _ d x ⟨inBout, ninBounds⟩ ins
            =>
              let eqOfFree := Valuation.withBoundVars.eqOrigOfIsFree
              let isNotDef: ¬ (theInternalWfm x).defMem d :=
                eqOfFree theInternalWfm ninBounds ▸ inBout
              ins.nopeNotDef isNotDef
      else if hSet: x = uniDefList.theSet then
        MotiveOut.theSet
          hSet
          fun _dd _xx dEq =>
            Out.intro4
              (internalOfExternalCycle externalCycle)
              (fun inCycle _cause isCause =>
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
