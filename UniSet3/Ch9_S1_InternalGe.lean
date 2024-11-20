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
        sorry
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
                  let ⟨xxAlias, _, ins⟩ := insUnDomElim ins
                  let ⟨ins500, ins⟩ := insPairElim ins
                  let xxEq := insBoundElim ins500
                  let ⟨exprXx, insFn, insArg⟩ :=
                    insCallExprElim ins
                  let ⟨zeroAlias, insInterp, insZero⟩ :=
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
            fun cycle cause _ => sorry)
          (motive_3 := fun d x _ => MotiveOut d x)
          (fun _ _ _ isCause cinsSat binsSat boutSat =>
            isCauseExternalToInsInternal isCause {
              contextInsHold := Ins.isSound ∘ cinsSat
              backgroundInsHold := Ins.isSound ∘ binsSat
              backgroundOutHold := Out.isSound ∘ boutSat
            })
          sorry
          sorry
          sorry
          sorry
      
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
