import DefListDefEq
import UniSet3.DefListToEncoding
import UniSet3.TheDefList


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
:
  Set3 Pair
:= {
  defMem := fun p => fn.defMem (Pair.pair arg p)
  posMem := fun p => fn.posMem (Pair.pair arg p)
  defLePos := fun _ pInDef => fn.defLePos pInDef
}


namespace Pair
  noncomputable def uniSet3 := uniDefList.wfModel uniDefList.theSet
  
  namespace uniSet3
    open Expr
    open PairExpr
    
    def theSetAsValuation: Valuation Pair :=
      fun n => Set3.pairCallJust uniSet3 (fromNat n)
    
    noncomputable def addBoundVars
      (v: Valuation Pair)
      (boundVarsEnc: Pair)
    :
      Valuation Pair
    :=
      match boundVarsEnc with
      | zero => v
      | pair zero _ => v
      | pair (pair x val) rest =>
        -- Breaks an if_pos below :/
        -- have := isNatEncoding.decidable x
        if IsNatEncoding x then
          (addBoundVars v rest).update x.depth val
        else
          addBoundVars v rest
    
    noncomputable def interp
      (boundVars exprEnc: Pair)
    :=
      interpretation
          pairSalgebra
          (addBoundVars theSetAsValuation boundVars)
          (addBoundVars theSetAsValuation boundVars)
          exprEnc.encodingToExpr
    
    def interp.inDefOfIsBoundHead
      (isNat: IsNatEncoding xEnc)
    :
      (interp ((xEnc.pair p).pair tail) (pair zero xEnc)).defMem p
    :=
      let encEq := exprToEncoding.toEqEncodingToExpr
          xEnc.depth (exprToEncoding.eqVarDepth isNat)
      
      by
        unfold interp
        rw [encEq.symm]
        unfold interpretation addBoundVars
        rw [if_pos isNat]
        rw [Valuation.update.eqBound _ _ _]
        rfl
    
    def interp.inDefOfIsBoundTail
      (inDefTail: (interp tail (pair zero xEnc)).defMem p)
      (neq: hA ≠ xEnc)
      (isNat: IsNatEncoding xEnc)
    :
      (interp (pair (pair hA hB) tail) (pair zero xEnc)).defMem p
    :=
      let encEq := exprToEncoding.toEqEncodingToExpr
        xEnc.depth (exprToEncoding.eqVarDepth isNat)
      
      let inTail:
        Set3.defMem
          (Expr.interpretation
            pairSalgebra
            (addBoundVars theSetAsValuation tail)
            (addBoundVars theSetAsValuation tail)
            (Expr.var xEnc.depth))
          p
      :=
        encEq ▸ inDefTail
      
      if h: IsNatEncoding hA then
        let neqDepth := depth.nat.injNeq h isNat neq
        by
          unfold interp
          rw [encEq.symm]
          unfold addBoundVars interpretation
          rw [if_pos h]
          rw [Valuation.update.eqOrig _ neqDepth _]
          exact inTail
      else
        by
          unfold interp
          rw [encEq.symm]
          unfold addBoundVars
          rw [if_neg h]
          exact inTail
    
    
    def inInterpOfIns.ReturnType
      (boundVars exprEnc p: Pair)
    :=
      (interp boundVars exprEnc).defMem p
    
    def inInterpOfIns.ofInsBoundVars
      (ins:
        Ins
          uniDefList.getBound
          (pair bv (pair xEnc p)))
    :
      And
        ((interp bv (pair zero xEnc)).defMem p)
        (IsNatEncoding xEnc)
    :=
      (insUnElim (insWfm.toInsWfmDef ins)).elim
        (fun ins =>
          let ins := insWfm.toInsWfmDef ins
          let ⟨xEncAlias, ⟨insDomain, ins⟩⟩ := insUnDomElim ins
          let ⟨pAlias, ins⟩ := insArbUnElim ins
          let ⟨insL, insR⟩ := insPairElim ins
          let ⟨insXEnc, insP⟩ := insPairElim insR
          
          let eqXEnc :=
            insBoundElim (insFreeElim insXEnc nat501Neq500)
          let eqP := insBoundElim insP
          
          let isNat: IsNatEncoding xEnc :=
            eqXEnc ▸ Inw.toIsNatEncoding insDomain.toInw
          
          match bv with
          | zero => insPairElim.nope insL
          | pair zero _ =>
            insPairElim.nope (insPairElim insL).insL
          | pair (pair hA hB) tail =>
            let ⟨insH, _⟩ := insPairElim insL
            let ⟨insHa, insHb⟩ := insPairElim insH
            
            let eqHa :=
              insBoundElim (insFreeElim insHa nat501Neq500)
            let eqHb := insBoundElim insHb
            
            eqHa ▸ eqHb ▸ eqXEnc ▸ eqP ▸
            And.intro (interp.inDefOfIsBoundHead isNat) isNat)
        (fun ins =>
          let ⟨xEncAlias, ins⟩ := insArbUnElim ins
          let ⟨tail, ins⟩ := insArbUnElim ins
          -- Renaming `ins_c` to `ins` triggers a Lean bug.
          let ⟨insBv, ins_c⟩ := insPairElim ins
          
          match bv with
          | zero => insPairElim.nope insBv
          | pair zero _ =>
            insPairElim.nope (insPairElim insBv).insL
          | pair (pair hA hB) t =>
            let ⟨insBvH, insBvT⟩ := insPairElim insBv
            let ⟨insHa, _⟩ := insPairElim insBvH
            
            let ninwHa := insCplElim insHa
            let neq: hA ≠ xEncAlias := fun eq =>
              ninwHa (inwFree (eq ▸ inwBound) nat501Neq500)
            let eqT := insBoundElim insBvT
            
            let ⟨insXEnc, ins⟩ := insPairElim ins_c
            let ins := insCallElimBound ins rfl nat502Neq500
            let ins := insCallElimBound ins rfl nat503Neq501
            let ⟨ih, isNat⟩ := ofInsBoundVars ins
            
            let eqXEnc :=
              insBoundElim (insFreeElim insXEnc nat501Neq500)
            
            eqT ▸ eqXEnc ▸
            And.intro
              (interp.inDefOfIsBoundTail ih neq isNat)
              isNat)
    
    
    def inInterpOfIns.exprVar
      (ins:
        Ins
          uniDefList.interpretation.exprVar
          (pair boundVars (pair exprEnc p)))
    :
      ReturnType boundVars exprEnc p
    :=
      let ⟨xEnc, ⟨isNat, ins⟩⟩ := insUnDomElim ins
      let ⟨boundVarsAlias, ins⟩ := insArbUnElim ins
      let ⟨insBoundVars, ins⟩ := insPairElim ins
      -- Renaming `ins_b` to `ins` triggers a Lean bug.
      let ⟨insExpr, ins_b⟩ := insPairElim ins
      
      match exprEnc with
      | zero => insPairElim.nope insExpr
      | pair z xAlias =>
        let ⟨insZ, insXAlias⟩ := insPairElim insExpr
        
        (insBoundElim insBoundVars) ▸
        (insBoundElim (insFreeElim insXAlias nat501Neq500)) ▸
        insZeroElim insZ ▸
        (insUnElim ins_b).elim
          (fun ins =>
            let ins := insCallElimBound ins rfl nat502Neq500
            let ins := insCallElimBound ins rfl nat503Neq501
            
            (ofInsBoundVars ins).left)
          (fun ins =>
            let ⟨exIns, ins⟩ := insIfThenElim ins
            let ins := insCallElimBound ins rfl nat502Neq500
            sorry)
    
    def interpretationOfIns
      (ins:
        Ins uniDefList.interpretation
          (pair boundVars (pair exprEnc p)))
    :
      inInterpOfIns.ReturnType boundVars exprEnc p
    :=
      insFinUnElim (insWfm.toInsWfmDef ins)
        inInterpOfIns.exprVar
        sorry
        sorry
        sorry
        sorry
        sorry
        sorry
        sorry
        sorry
    
    def interpretationOfInw
      (ins:
        Inw uniDefList.interpretation
          (pair boundVars (pair expr p)))
    :
      (interpretation
        pairSalgebra
        (addBoundVars theSetAsValuation boundVars)
        (addBoundVars theSetAsValuation boundVars)
        expr.encodingToExpr).posMem p
    :=
      sorry
    
    
    def freeInterpretationOfIns
      (ins: Ins uniDefList.freeInterpretation (pair expr p))
    :
      (interpretation
        pairSalgebra
        theSetAsValuation
        theSetAsValuation
        expr.encodingToExpr).defMem p
    :=
      let ⟨_z, ⟨insFn, insArg⟩⟩ :=
        insCallExprElim (insWfm.toInsWfmDef ins)
      
      let zEq := insZeroElim insArg
      
      show
        (interpretation
          pairSalgebra
          (addBoundVars theSetAsValuation zero)
          (addBoundVars theSetAsValuation zero)
          expr.encodingToExpr).defMem
        p
      from
        zEq ▸ interpretationOfIns insFn
    
    def freeInterpretationOfInw
      (ins: Inw uniDefList.freeInterpretation (pair expr p))
    :
      (interpretation
        pairSalgebra
        theSetAsValuation
        theSetAsValuation
        expr.encodingToExpr).posMem p
    :=
      let ⟨_z, ⟨insFn, insArg⟩⟩ :=
        inwCallExprElim (inwWfm.toInwWfmDef ins)
      
      let zEq := inwZeroElim insArg
      
      show
        (interpretation
          pairSalgebra
          (addBoundVars theSetAsValuation zero)
          (addBoundVars theSetAsValuation zero)
          expr.encodingToExpr).posMem
        p
      from
        zEq ▸ interpretationOfInw insFn
    
    
    def insNthOfInsTheSet
      (ins: Ins uniDefList.theSet (pair (fromNat x) p))
    :
      Set3.defMem
        (Expr.interpretation
          pairSalgebra
          theSetAsValuation
          theSetAsValuation
          (encodingToExpr
            (IsTheDefListExprPair.getNthExpr x).expr))
        p
    :=
      let ⟨_xEnc, ⟨_insNatXEnc, ins⟩⟩ :=
        insUnDomElim (insWfm.toInsWfmDef ins)
      
      let ⟨insL, insR⟩ := insPairElim ins
      
      let xEncEqX := (insBoundElim insL).symm
      
      let ⟨_expr, ⟨insFn, insArg⟩⟩ := insCallExprElim insR
      
      let isTheDefListExpr :=
        Inw.toIsTheDefListExpr
          (insCallElimBound insArg rfl nat502Neq500).toInw
      
      let exprEq :=
        IsTheDefListExprPair.getNthExpr.eq
          isTheDefListExpr xEncEqX
      
      exprEq ▸
      freeInterpretationOfIns insFn
    
    def inwNthOfInwTheSet
      (inw: Inw uniDefList.theSet (pair (fromNat x) p))
    :
      Set3.posMem
        (Expr.interpretation
          pairSalgebra
          theSetAsValuation
          theSetAsValuation
          (encodingToExpr
            (IsTheDefListExprPair.getNthExpr x).expr))
        p
    :=
      let ⟨_xEnc, ⟨_inwNatXEnc, inw⟩⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      
      let ⟨inwL, inwR⟩ := inwPairElim inw
      
      let xEncEqX := (inwBoundElim inwL).symm
      
      let ⟨_expr, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim inwR
      
      let isTheDefListExpr :=
        Inw.toIsTheDefListExpr
          (inwCallElimBound inwArg rfl nat502Neq500)
      
      let exprEq :=
        IsTheDefListExprPair.getNthExpr.eq
          isTheDefListExpr xEncEqX
      
      exprEq ▸
      freeInterpretationOfInw inwFn
    
  end uniSet3
end Pair
