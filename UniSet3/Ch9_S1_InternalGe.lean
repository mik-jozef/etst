/-
  The first section of Chapter 9. See the zeroth section.
-/

import UniSet3.Ch9_S0_InternalLe


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
    
    -- TODO
    inductive MotiveInapplicable
      (externalCycle: Set (ValVar Pair))
      (externalCause: Cause Pair)
    :
      Prop
    
    
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
      (binsIns:
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
      | Expr.var x =>
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
      | Expr.cpl expr => sorry
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
    
    def isEmptyCycleExternalToOutInternal
    :
      MotiveOut d x
    :=
      if hInterp: x = uniDefList.interpretation then
        sorry
      else if hSet: x = uniDefList.theSet then
        MotiveOut.theSet
          hSet
          fun dd xx dEq =>
            sorry
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
          (fun cause _ _ inCins inCycle =>
            sorry)
          (fun cause _ _ inBins isOut motiveOut =>
            sorry)
          (fun cause _ _ inBout isIns motiveIns =>
            sorry)
          (fun cycle isEmptyCycle inCycle ihEmptyCycle =>
            isEmptyCycleExternalToOutInternal)
      
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
      sorry
    
    
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
