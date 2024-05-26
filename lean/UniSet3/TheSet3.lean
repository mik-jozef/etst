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
    
    def inwTheSet.toIsNat
      (inw: Inw uniDefList.theSet (pair xEnc p))
    :
      IsNatEncoding xEnc
    :=
      let ⟨_xEncAlias, ⟨inwDomain, inw⟩⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      let ⟨inwL, _⟩ := inwPairElim inw
      
      inwBoundElim inwL ▸
      Inw.toIsNatEncoding inwDomain
    
    def insTheSet.toIsNat
      (ins: Ins uniDefList.theSet (pair xEnc p))
    :
      IsNatEncoding xEnc
    :=
      inwTheSet.toIsNat ins.toInw
    
    
    def InsGetBound bv xEnc p :=
      Ins uniDefList.getBound (pair bv (pair xEnc p))
    
    def InwGetBound bv xEnc p :=
      Inw uniDefList.getBound (pair bv (pair xEnc p))
    
    
    def inwGetBound.toIsNat
      (inw: InwGetBound boundVars xEnc p)
    :
      IsNatEncoding xEnc
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          let ⟨xEncAlias, ⟨inwDomain, inw⟩⟩ :=
            inwUnDomElim inw
          let ⟨_, inw⟩ := inwArbUnElim inw
          let ⟨_, inw⟩ := inwPairElim inw
          let ⟨inw, _⟩ := inwPairElim inw
          
          inwBoundElim (inwFreeElim inw nat501Neq500) ▸
          Inw.toIsNatEncoding inwDomain)
        (fun inw =>
          let ⟨xEncAlias, inw⟩ := inwArbUnElim inw
          let ⟨_, inw⟩ := inwArbUnElim inw
          let ⟨inwB, inw⟩ := inwPairElim inw
          let ⟨inwXEnc, inwCall⟩ := inwPairElim inw
          
          let inwXEnc :=
            inwBoundElim (inwFreeElim inwXEnc nat501Neq500)
          
          match boundVars with
          | zero => inwPairElim.nope inwB
          | pair bH bT =>
            -- How exactly does this prove termination? Lol.
            let ⟨_, _⟩ := inwPairElim inwB
            
            let inw :=
              inwCallElimBound inwCall rfl nat502Neq500
            let inw :=
              inwCallElimBound inw rfl nat503Neq501
            
            inwXEnc ▸ toIsNat inw)
    termination_by boundVars
    
    
    def insGetBound.head
      (isNat: IsNatEncoding hA)
      (hB tail: Pair)
    :
      InsGetBound (pair (pair hA hB) tail) hA hB
    :=
      insWfmDef.toInsWfm
        (insUnL
          (by
            exact
              insUnDom
                (insNatEncoding isNat)
                (insArbUn
                  hB
                  (insPair
                    (insPair
                      (insPair
                        (insFree
                          insBound
                          nat501Neq500)
                      insBound)
                    insAny)
                  (insPair
                    (insFree
                      insBound
                      nat501Neq500)
                    insBound))))
          _)
    
    def inwGetBound.head
      (isNat: IsNatEncoding hA)
      (hB tail: Pair)
    :
      InwGetBound (pair (pair hA hB) tail) hA hB
    :=
      inwWfmDef.toInwWfm
        (inwUnL
          (by
            exact
              inwUnDom
                (insNatEncoding isNat).toInw
                (inwArbUn
                  hB
                  (inwPair
                    (inwPair
                      (inwPair
                        (inwFree
                          inwBound
                          nat501Neq500)
                        inwBound)
                      inwAny)
                    (inwPair
                      (inwFree
                        inwBound
                        nat501Neq500)
                      inwBound))))
          _)
    
    
    def inwGetBound.ofInwTail
      (inw: InwGetBound tail xEnc p)
    :
      ∃ bv, InwGetBound (pair (pair hA hB) tail) xEnc bv
    :=
      if h: hA = xEnc then ⟨
        hB,
        let isNatX: IsNatEncoding xEnc :=
          inwGetBound.toIsNat inw
        
        inwWfmDef.toInwWfm
          (inwUnL
            (by -- Wtf why is this necessary?
              exact
                inwUnDom
                  (insNatEncoding isNatX).toInw
                  (inwArbUn
                    hB
                    (inwPair
                      (inwPair
                        (inwPair
                          (inwFree
                            (h ▸ inwBound)
                            nat501Neq500)
                          inwBound)
                        inwAny)
                      (inwPair
                        (inwFree
                          inwBound
                          nat501Neq500)
                        inwBound))))
            _),
      ⟩ else ⟨
        p,
        inwWfmDef.toInwWfm
          (inwUnR _
            (inwArbUn
              xEnc
              (inwArbUn
                tail
                (inwPair
                  (inwPair
                    (inwPair
                      (inwCpl
                        (fun ins =>
                          h
                            (insBoundElim
                              (insFreeElim
                                ins
                                nat501Neq500))))
                      inwAny)
                    inwBound)
                  (inwPair
                    (inwFree
                      inwBound
                      nat501Neq500)
                    (inwCallExpr
                      (inwCallExpr
                        inw
                        (inwFree
                          (inwFree
                            inwBound
                            nat502Neq501)
                          nat503Neq501))
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500))))))),
      ⟩
    
    def insGetBound.ofInsTail
      (ins: InsGetBound tail xEnc p)
    :
      ∃ bv, InsGetBound (pair (pair hA hB) tail) xEnc bv
    :=
      if h: hA = xEnc then ⟨
        hB,
        let isNatX: IsNatEncoding xEnc :=
          inwGetBound.toIsNat ins.toInw
        
        insWfmDef.toInsWfm
          (insUnL
            (by
              exact
                insUnDom
                  (insNatEncoding isNatX)
                  (insArbUn
                    hB
                    (insPair
                      (insPair
                        (insPair
                          (insFree
                            (h ▸ insBound)
                            nat501Neq500)
                          insBound)
                        insAny)
                      (insPair
                        (insFree
                          insBound
                          nat501Neq500)
                        insBound))))
            _),
      ⟩ else ⟨
        p,
        insWfmDef.toInsWfm
          (insUnR _
            (insArbUn
              xEnc
              (insArbUn
                tail
                (insPair
                  (insPair
                    (insPair
                      (insCpl
                        (fun inw =>
                          h
                            (inwBoundElim
                              (inwFreeElim
                                inw
                                nat501Neq500))))
                      insAny)
                    insBound)
                  (insPair
                    (insFree
                      insBound
                      nat501Neq500)
                    (insCallExpr
                      (insCallExpr
                        ins
                        (insFree
                          (insFree
                            insBound
                            nat502Neq501)
                          nat503Neq501))
                      (insFree
                        (insFree
                          insBound
                          nat501Neq500)
                        nat502Neq500))))))),
      ⟩
    
    
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
    
    def addBoundVars.updateEq
      (v: Valuation Pair)
      (isNat: IsNatEncoding xEnc)
      (val boundVars: Pair)
    :
      addBoundVars v (pair (pair xEnc val) boundVars)
        =
      (addBoundVars v boundVars).update xEnc.depth val
    := by
      conv => lhs; unfold addBoundVars
      rw [if_pos isNat]
    
    
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
      by
        unfold interp
        rw [encodingToExpr.varEncEq isNat]
        unfold interpretation
        rw [addBoundVars.updateEq _ isNat _ _]
        rw [Valuation.update.eqBound _ _ _]
        rfl
    
    def interp.inPosOfIsBoundHead
      (isNat: IsNatEncoding xEnc)
    :
      (interp ((xEnc.pair p).pair tail) (pair zero xEnc)).posMem p
    :=
      by
        unfold interp
        rw [encodingToExpr.varEncEq isNat]
        unfold interpretation
        rw [addBoundVars.updateEq _ isNat _ _]
        rw [Valuation.update.eqBound _ _ _]
        rfl
    
    
    def interp.inDefOfIsBoundTail
      (inDefTail: (interp tail (pair zero xEnc)).defMem p)
      (neq: hA ≠ xEnc)
      (isNat: IsNatEncoding xEnc)
    :
      (interp (pair (pair hA hB) tail) (pair zero xEnc)).defMem p
    :=
      let inTail:
        Set3.defMem
          (Expr.interpretation
            pairSalgebra
            (addBoundVars theSetAsValuation tail)
            (addBoundVars theSetAsValuation tail)
            (Expr.var xEnc.depth))
          p
      :=
        encodingToExpr.varEncEq isNat ▸ inDefTail
      
      if h: IsNatEncoding hA then
        let neqDepth := depth.nat.injNeq h isNat neq
        by
          unfold interp
          rw [encodingToExpr.varEncEq isNat]
          unfold addBoundVars interpretation
          rw [if_pos h]
          rw [Valuation.update.eqOrig _ neqDepth _]
          exact inTail
      else
        by
          unfold interp
          rw [encodingToExpr.varEncEq isNat]
          unfold addBoundVars
          rw [if_neg h]
          exact inTail
    
    def interp.inPosOfIsBoundTail
      (inPosTail: (interp tail (pair zero xEnc)).posMem p)
      (neq: hA ≠ xEnc)
      (isNat: IsNatEncoding xEnc)
    :
      (interp (pair (pair hA hB) tail) (pair zero xEnc)).posMem p
    :=
      let inTail:
        Set3.posMem
          (Expr.interpretation
            pairSalgebra
            (addBoundVars theSetAsValuation tail)
            (addBoundVars theSetAsValuation tail)
            (Expr.var xEnc.depth))
          p
      :=
        encodingToExpr.varEncEq isNat ▸ inPosTail
      
      if h: IsNatEncoding hA then
        let neqDepth := depth.nat.injNeq h isNat neq
        by
          unfold interp
          rw [encodingToExpr.varEncEq isNat]
          unfold addBoundVars interpretation
          rw [if_pos h]
          rw [Valuation.update.eqOrig _ neqDepth _]
          exact inTail
      else
        by
          unfold interp
          rw [encodingToExpr.varEncEq isNat]
          unfold addBoundVars
          rw [if_neg h]
          exact inTail
    
    
    def inInterpOfIns.ofInsBoundVars
      (ins: InsGetBound bv xEnc p)
    :
      (interp bv (pair zero xEnc)).defMem p
    :=
      (insUnElim (insWfm.toInsWfmDef ins)).elim
        (fun ins =>
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
            interp.inDefOfIsBoundHead isNat)
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
            let ih := ofInsBoundVars ins
            
            let eqXEnc :=
              insBoundElim (insFreeElim insXEnc nat501Neq500)
            
            let isNat := inwGetBound.toIsNat ins.toInw
            
            eqT ▸ eqXEnc ▸
            interp.inDefOfIsBoundTail ih neq isNat)
    
    def inInterpOfInw.ofInwBoundVars
      (inw:
        Inw
          uniDefList.getBound
          (pair bv (pair xEnc p)))
    :
      (interp bv (pair zero xEnc)).posMem p
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          let ⟨xEncAlias, ⟨inwDomain, inw⟩⟩ := inwUnDomElim inw
          let ⟨pAlias, inw⟩ := inwArbUnElim inw
          let ⟨inwL, inwR⟩ := inwPairElim inw
          let ⟨inwXEnc, inwP⟩ := inwPairElim inwR
          
          let eqXEnc :=
            inwBoundElim (inwFreeElim inwXEnc nat501Neq500)
          let eqP := inwBoundElim inwP
          
          let isNat: IsNatEncoding xEnc :=
            eqXEnc ▸ Inw.toIsNatEncoding inwDomain
          
          match bv with
          | zero => inwPairElim.nope inwL
          | pair zero _ =>
            inwPairElim.nope (inwPairElim inwL).inwL
          | pair (pair hA hB) tail =>
            let ⟨inwH, _⟩ := inwPairElim inwL
            let ⟨inwHa, inwHb⟩ := inwPairElim inwH
            
            let eqHa :=
              inwBoundElim (inwFreeElim inwHa nat501Neq500)
            let eqHb := inwBoundElim inwHb
            
            eqHa ▸ eqHb ▸ eqXEnc ▸ eqP ▸
            interp.inPosOfIsBoundHead isNat)
        (fun inw =>
          let ⟨xEncAlias, inw⟩ := inwArbUnElim inw
          let ⟨tail, inw⟩ := inwArbUnElim inw
          -- Renaming `inw_c` to `inw` triggers a Lean bug.
          let ⟨inwBv, inw_c⟩ := inwPairElim inw
          
          match bv with
          | zero => inwPairElim.nope inwBv
          | pair zero _ =>
            inwPairElim.nope (inwPairElim inwBv).inwL
          | pair (pair hA hB) t =>
            let ⟨inwBvH, inwBvT⟩ := inwPairElim inwBv
            let ⟨inwHa, _⟩ := inwPairElim inwBvH
            
            let ninsHa := inwCplElim inwHa
            let neq: hA ≠ xEncAlias := fun eq =>
              ninsHa (insFree (eq ▸ insBound) nat501Neq500)
            let eqT := inwBoundElim inwBvT
            
            let ⟨inwXEnc, inw⟩ := inwPairElim inw_c
            let inw := inwCallElimBound inw rfl nat502Neq500
            let inw := inwCallElimBound inw rfl nat503Neq501
            let ih := ofInwBoundVars inw
            
            let eqXEnc :=
              inwBoundElim (inwFreeElim inwXEnc nat501Neq500)
            
            let isNat := inwGetBound.toIsNat inw
            
            eqT ▸ eqXEnc ▸
            interp.inPosOfIsBoundTail ih neq isNat)
    
    
    def inInterpOfIns.ofFree
      (ins: Ins uniDefList.theSet (pair xEnc p))
      (notBound: ¬∃ bv, InwGetBound boundVars xEnc bv)
    :
      (interp boundVars (pair zero xEnc)).defMem p
    :=
      let isNat := insTheSet.toIsNat ins
      
      match boundVars with
      | zero =>
        by
          unfold interp
          rw [encodingToExpr.varEncEq isNat]
          unfold interpretation theSetAsValuation addBoundVars
          rw [fromNat.eqOfDepth isNat]
          exact ins
      | pair zero tail =>
        by
          unfold interp addBoundVars
          rw [encodingToExpr.varEncEq isNat]
          unfold interpretation theSetAsValuation
          rw [fromNat.eqOfDepth isNat]
          exact ins
      | pair (pair hA hB) tail =>
        let notBoundTail: ¬∃ bv, InwGetBound tail xEnc bv :=
          fun ⟨bv, inw⟩ =>
            notBound (inwGetBound.ofInwTail inw)
        
        let inTail: (interp tail (zero.pair xEnc)).defMem p :=
          ofFree ins notBoundTail
        
        let neq (eq: hA = xEnc) :=
          notBound ⟨
            hB,
            eq ▸ inwGetBound.head isNat hB tail
          ⟩
        
        interp.inDefOfIsBoundTail inTail neq isNat
    
    def inInterpOfInw.ofFree
      (inw: Inw uniDefList.theSet (pair xEnc p))
      (notBound: ¬∃ bv, InsGetBound boundVars xEnc bv)
    :
      (interp boundVars (pair zero xEnc)).posMem p
    :=
      let isNat := inwTheSet.toIsNat inw
      
      match boundVars with
      | zero =>
        by
          unfold interp
          rw [encodingToExpr.varEncEq isNat]
          unfold interpretation theSetAsValuation addBoundVars
          rw [fromNat.eqOfDepth isNat]
          exact inw
      | pair zero tail =>
        by
          unfold interp addBoundVars
          rw [encodingToExpr.varEncEq isNat]
          unfold interpretation theSetAsValuation
          rw [fromNat.eqOfDepth isNat]
          exact inw
      | pair (pair hA hB) tail =>
        let notBoundTail: ¬∃ bv, InsGetBound tail xEnc bv :=
          fun ⟨bv, ins⟩ =>
            notBound (insGetBound.ofInsTail ins)
        
        let inTail: (interp tail (zero.pair xEnc)).posMem p :=
          ofFree inw notBoundTail
        
        let neq (eq: hA = xEnc) :=
          notBound ⟨
            hB,
            eq ▸ insGetBound.head isNat hB tail
          ⟩
        
        interp.inPosOfIsBoundTail inTail neq isNat
    
    
    def inInterpOfIns.exprVar
      (ins:
        Ins
          uniDefList.interpretation.exprVar
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let ⟨xEnc, ⟨_, ins⟩⟩ := insUnDomElim ins
      let ⟨boundVarsAlias, ins⟩ := insArbUnElim ins
      let ⟨insBoundVars, ins⟩ := insPairElim ins
      -- Renaming `ins_b` to `ins` triggers a Lean bug.
      let ⟨insExpr, ins_b⟩ := insPairElim ins
      
      match exprEnc with
      | zero => insPairElim.nope insExpr
      | pair _z _xAlias =>
        let ⟨insZ, insXAlias⟩ := insPairElim insExpr
        
        let eqBound := (insBoundElim insBoundVars)
        
        eqBound ▸
        (insBoundElim (insFreeElim insXAlias nat501Neq500)) ▸
        insZeroElim insZ ▸
        (insUnElim ins_b).elim
          (fun ins =>
            let ins := insCallElimBound ins rfl nat502Neq500
            let ins := insCallElimBound ins rfl nat503Neq501
            
            ofInsBoundVars ins)
          (fun ins =>
            let ⟨⟨_bv, exIns⟩, ins⟩ := insIfThenElim ins
            let ninwIfThen := insCplElim exIns
            let ninw:
              ¬∃ bv, InwGetBound boundVarsAlias xEnc bv
            :=
              fun ⟨_, inw⟩ =>
                ninwIfThen
                  (inwIfThen
                    (inwCallExpr
                      (inwCallExpr
                        inw
                        (inwFree
                          (inwFree
                            inwBound
                            nat502Neq501)
                          nat503Neq501))
                      (inwFree
                        (inwFree
                          inwBound
                          nat501Neq500)
                        nat502Neq500))
                    inwAny)
            
            let ins := insCallElimBound ins rfl nat502Neq500
            
            ofFree ins ninw)
    
    def inInterpOfInw.exprVar
      (inw:
        Inw
          uniDefList.interpretation.exprVar
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).posMem p
    :=
      let ⟨xEnc, ⟨_, inw⟩⟩ := inwUnDomElim inw
      let ⟨boundVarsAlias, inw⟩ := inwArbUnElim inw
      let ⟨inwBoundVars, inw⟩ := inwPairElim inw
      let ⟨inwExpr, inw_b⟩ := inwPairElim inw
      
      match exprEnc with
      | zero => inwPairElim.nope inwExpr
      | pair _z _xAlias =>
        let ⟨inwZ, inwXAlias⟩ := inwPairElim inwExpr
        
        let eqBound := (inwBoundElim inwBoundVars)
        
        eqBound ▸
        (inwBoundElim (inwFreeElim inwXAlias nat501Neq500)) ▸
        inwZeroElim inwZ ▸
        (inwUnElim inw_b).elim
          (fun inw =>
            let inw := inwCallElimBound inw rfl nat502Neq500
            let inw := inwCallElimBound inw rfl nat503Neq501
            
            ofInwBoundVars inw)
          (fun inw =>
            let ⟨⟨_bv, exInw⟩, inw⟩ := inwIfThenElim inw
            let ninsIfThen := inwCplElim exInw
            let nins:
              ¬∃ bv, InsGetBound boundVarsAlias xEnc bv
            :=
              fun ⟨_, inw⟩ =>
                ninsIfThen
                  (insIfThen
                    (insCallExpr
                      (insCallExpr
                        inw
                        (insFree
                          (insFree
                            insBound
                            nat502Neq501)
                          nat503Neq501))
                      (insFree
                        (insFree
                          insBound
                          nat501Neq500)
                        nat502Neq500))
                    insAny)
            
            let inw := inwCallElimBound inw rfl nat502Neq500
            
            ofFree inw nins)
    
    
    def inInterpOfIns.exprZero
      (ins:
        Ins
          uniDefList.interpretation.exprZero
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let ⟨bvAlias, ins⟩ := insArbUnElim ins
      let ⟨_, ins⟩ := insPairElim ins
      let ⟨insExpr, insZ⟩ := insPairElim ins
      
      match exprEnc with
      | zero => insPairElim.nope insExpr
      | pair nat1Enc z =>
        let ⟨insEa, insEb⟩ := insPairElim insExpr
        
        let eqP := insZeroElim insZ
        let eqNat1Enc := insNatExprElim insEa
        let eqZ := insZeroElim insEb
        
        eqNat1Enc ▸ eqZ ▸ eqP.symm ▸
        by
          unfold interp
          rw [encodingToExpr.zeroEncEq] 
          exact
            @insZero (addBoundVars theSetAsValuation boundVars)
    
    structure inInterpOfIns.exprPair.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      exprEncA: Pair
      exprEncB: Pair
      pA: Pair
      pB: Pair
      eqP: p = Pair.pair pA pB
      eqExprEnc: exprEnc = pair (fromNat 2) (pair exprEncA exprEncB)
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        pairExpr exprEncA.encodingToExpr exprEncB.encodingToExpr
      insA:
        Ins
          uniDefList.interpretation
          (pair boundVars (pair exprEncA pA))
      insB:
        Ins
          uniDefList.interpretation
          (pair boundVars (pair exprEncB pB))
    
    -- The mutual block below strains Lean a lot
    -- (performance-wise). Hopefully putting some
    -- parts out will make it better.
    noncomputable def inInterpOfIns.exprPair.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprPair
          (pair boundVars (pair exprEnc p)))
    :
      InsOfIns boundVars exprEnc p
    :=
      let ⟨exprEncA, ⟨insDomainA, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨exprEncB, ⟨insDomainB, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc, p with
      | zero, _ => insPairElim.nope insEnc
      | pair _ zero, _ =>
        insPairElim.nope (insPairElim insEnc).insR
      | _, zero => insPairElim.nope insP
      | pair _fromNat2 (pair _exprAliasA _exprAliasB),
        pair pA pB
      =>
        let ⟨insFn2, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let ⟨insPa, insPb⟩ := insPairElim insP
        
        let insA := insCallElimBound insPa rfl nat503Neq500
        let insA := insCallElimBound insA rfl nat504Neq502
        
        let insB := insCallElimBound insPb rfl nat503Neq501
        let insB := insCallElimBound insB rfl nat504Neq502
        
        let eqFn2 := insNatExprElim insFn2
        let eqBv := insBoundElim insBv
        
        let eqExprA :=
          insBoundElim
            (insFreeElim
              (insFreeElim insExprA nat502Neq500)
              nat501Neq500)
        
        let eqExprB :=
          insBoundElim (insFreeElim insExprB nat502Neq501)
        
        eqFn2 ▸ eqBv ▸ eqExprA ▸ eqExprB ▸
        {
          exprEncA,
          exprEncB,
          pA,
          pB,
          eqP := rfl,
          eqExprEnc := rfl,
          eqExprEncExpr :=
            encodingToExpr.pairEncEq isExprA isExprB
          insA := insA,
          insB := insB
        }
    
    structure inInterpOfIns.exprUn.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      exprEncA: Pair
      exprEncB: Pair
      eqExprEnc: exprEnc = pair (fromNat 3) (pair exprEncA exprEncB)
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        Expr.un exprEncA.encodingToExpr exprEncB.encodingToExpr
      ins:
        Or
          (Ins
            uniDefList.interpretation
            (pair boundVars (pair exprEncA p)))
          (Ins
            uniDefList.interpretation
            (pair boundVars (pair exprEncB p)))
    
    noncomputable def inInterpOfIns.exprUn.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprUnion
          (pair boundVars (pair exprEnc p)))
    :
      InsOfIns boundVars exprEnc p
    :=
      let ⟨_exprEncA, ⟨insDomainA, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_exprEncB, ⟨insDomainB, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair _fromNat3 (pair exprAliasA exprAliasB) =>
        let ⟨insFn3, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let eqFn3 := insNatExprElim insFn3
        let eqBv := insBoundElim insBv
        
        let eqExprA :=
          insBoundElim
            (insFreeElim
              (insFreeElim insExprA nat502Neq500)
              nat501Neq500)
        
        let eqExprB :=
          insBoundElim (insFreeElim insExprB nat502Neq501)
        
        eqFn3 ▸ eqBv ▸
        {
          exprEncA := exprAliasA,
          exprEncB := exprAliasB,
          eqExprEnc := rfl,
          eqExprEncExpr :=
            encodingToExpr.unEncEq
              (eqExprA ▸ isExprA) (eqExprB ▸ isExprB),
          ins :=
            (insUnElim insP).elim
              (fun ins =>
                let ins := insCallElimBound ins rfl nat503Neq500
                let ins := insCallElimBound ins rfl nat504Neq502
                Or.inl (eqExprA ▸ ins))
              (fun ins =>
                let ins := insCallElimBound ins rfl nat503Neq501
                let ins := insCallElimBound ins rfl nat504Neq502
                Or.inr (eqExprB ▸ ins))
        }
    
    structure inInterpOfIns.exprIr.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      exprEncA: Pair
      exprEncB: Pair
      eqExprEnc: exprEnc = pair (fromNat 4) (pair exprEncA exprEncB)
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        Expr.ir exprEncA.encodingToExpr exprEncB.encodingToExpr
      insA:
        Ins
          uniDefList.interpretation
          (pair boundVars (pair exprEncA p))
      insB:
        Ins
          uniDefList.interpretation
          (pair boundVars (pair exprEncB p))
    
    noncomputable def inInterpOfIns.exprIr.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprIntersection
          (pair boundVars (pair exprEnc p)))
    :
      InsOfIns boundVars exprEnc p
    :=
      let ⟨_exprEncA, ⟨insDomainA, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_exprEncB, ⟨insDomainB, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair _fromNat4 (pair exprAliasA exprAliasB) =>
        let ⟨insFn4, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let ⟨insA, insB⟩ := insIrElim insP
        
        let insA := insCallElimBound insA rfl nat503Neq500
        let insA := insCallElimBound insA rfl nat504Neq502
        
        let insB := insCallElimBound insB rfl nat503Neq501
        let insB := insCallElimBound insB rfl nat504Neq502
        
        let eqFn4 := insNatExprElim insFn4
        let eqBv := insBoundElim insBv
        
        let eqExprA :=
          insBoundElim
            (insFreeElim
              (insFreeElim insExprA nat502Neq500)
              nat501Neq500)
        
        let eqExprB :=
          insBoundElim (insFreeElim insExprB nat502Neq501)
        
        eqFn4 ▸ eqBv ▸
        {
          exprEncA := exprAliasA,
          exprEncB := exprAliasB,
          eqExprEnc := rfl,
          eqExprEncExpr :=
            encodingToExpr.irEncEq
              (eqExprA ▸ isExprA) (eqExprB ▸ isExprB),
          insA := eqExprA ▸ insA,
          insB := eqExprB ▸ insB
        }
    
    structure inInterpOfIns.exprCpl.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      exprEncInner: Pair
      eqExprEnc: exprEnc = pair (fromNat 5) exprEncInner
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        Expr.cpl exprEncInner.encodingToExpr
      ninw:
        ¬Inw
          (var uniDefList.interpretation)
          (boundVars.pair (pair exprEncInner p))

    
    noncomputable def inInterpOfIns.exprCpl.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprCpl
          (pair boundVars (pair cplEnc p)))
    :
      InsOfIns boundVars cplEnc p
    :=
      let ⟨exprEnc, ⟨insDomain, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insCplEnc, insP⟩ := insPairElim ins
      
      let isExpr := Inw.toIsExprEncoding insDomain.toInw
      
      match cplEnc with
      | zero => insPairElim.nope insCplEnc
      | pair _fromNat5 exprAlias =>
        let ⟨insFn5, insExpr⟩ := insPairElim insCplEnc
        
        let eqFn5 := insNatExprElim insFn5
        let eqBv := insBoundElim insBv
        let eqExpr := insBoundElim
          (insFreeElim insExpr nat502Neq500)
        
        let ninw
          (inw: Inw uniDefList.interpretation
            (pair boundVars (pair exprEnc p)))
        :=
          insCplElim
            insP
            (inwCallExpr
              (inwCallExpr
                inw
                (inwFree
                  (inwFree
                    (eqBv ▸ inwBound)
                    nat503Neq502)
                  nat504Neq502))
              (inwFree
                (inwFree
                  inwBound
                  nat502Neq500)
                nat503Neq500))
        
        eqFn5 ▸
        {
          exprEncInner := exprAlias,
          eqExprEnc := rfl,
          eqExprEncExpr :=
            encodingToExpr.cplEncEq (eqExpr ▸ isExpr),
          ninw := eqExpr ▸ ninw,
        }
    
    structure inInterpOfIns.exprIfThen.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      exprEncCond: Pair
      exprEncBody: Pair
      c: Pair
      eqExprEnc: exprEnc = pair (fromNat 6) (pair exprEncCond exprEncBody)
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        Expr.ifThen exprEncCond.encodingToExpr exprEncBody.encodingToExpr
      insCond:
        Ins
          uniDefList.interpretation
          (pair boundVars (pair exprEncCond c))
      insBody:
        Ins
          uniDefList.interpretation
          (pair boundVars (pair exprEncBody p))
    
    noncomputable def inInterpOfIns.exprIfThen.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprIfThen
          (pair boundVars (pair exprEnc p)))
    :
      InsOfIns boundVars exprEnc p
    :=
      let ⟨_exprEncA, ⟨insDomainA, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_exprEncB, ⟨insDomainB, ins⟩⟩ := (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair _fromNat6 (pair exprAliasA exprAliasB) =>
        let ⟨insFn6, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let ⟨exInCond, insBody⟩ := insIfThenElim insP
        let ⟨c, insCond⟩ := exInCond.unwrap
        
        let insCond := insCallElimBound insCond rfl nat503Neq500
        let insCond := insCallElimBound insCond rfl nat504Neq502
        
        let insBody := insCallElimBound insBody rfl nat503Neq501
        let insBody := insCallElimBound insBody rfl nat504Neq502
        
        let eqFn6 := insNatExprElim insFn6
        let eqBv := insBoundElim insBv
        
        let eqExprA :=
          insBoundElim
            (insFreeElim
              (insFreeElim insExprA nat502Neq500)
              nat501Neq500)
        
        let eqExprB :=
          insBoundElim (insFreeElim insExprB nat502Neq501)
        
        eqFn6 ▸ eqBv ▸
        {
          exprEncCond := exprAliasA,
          exprEncBody := exprAliasB,
          c := c,
          eqExprEnc := rfl,
          eqExprEncExpr :=
            encodingToExpr.ifThenEncEq
              (eqExprA ▸ isExprA) (eqExprB ▸ isExprB),
          insCond := eqExprA ▸ insCond,
          insBody := eqExprB ▸ insBody
        }
    
    structure inInterpOfIns.exprArbUn.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      varEnc: Pair
      isVarNat: IsNatEncoding varEnc
      exprEncBody: Pair
      boundValue: Pair
      eqExprEnc: exprEnc = pair (fromNat 7) (pair varEnc exprEncBody)
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        Expr.Un varEnc.depth exprEncBody.encodingToExpr
      ins:
        Ins
          uniDefList.interpretation
          (pair
            (pair (pair varEnc boundValue) boundVars)
            (pair exprEncBody p))
    
    noncomputable def inInterpOfIns.exprArbUn.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprArbUnion
          (pair boundVars (pair exprEnc p)))
    :
      InsOfIns boundVars exprEnc p
    :=
      let ⟨_varEnc, ⟨insDomainVar, ins⟩⟩ :=
        (insUnDomElim ins).unwrap
      let ⟨_bodyEnc, ⟨insDomainBody, ins⟩⟩ :=
        (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isVar := Inw.toIsNatEncoding insDomainVar.toInw
      let isBody := Inw.toIsExprEncoding insDomainBody.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair _fromNat7 (pair varAlias bodyAlias) =>
        let ⟨insFn7, insExpr⟩ := insPairElim insEnc
        let ⟨insVar, insBody⟩ := insPairElim insExpr
        
        let ⟨boundValue, ins⟩ := (insArbUnElim insP).unwrap
        let ins := insCallElimBound ins rfl nat504Neq501
        let ⟨arg, ⟨insFn, insArg⟩⟩ := (insCallExprElim ins).unwrap
        
        match arg with
        | zero => insPairElim.nope insArg
        | pair zero _ => insPairElim.nope (insPairElim insArg).insL
        | pair (pair _hA _hB) _tail =>
          let ⟨insArgH, insArgT⟩ := insPairElim insArg
          let ⟨insHa, insHb⟩ := insPairElim insArgH
          
          let eqFn7 := insNatExprElim insFn7
          let eqBv := insBoundElim insBv
          
          let eqVar :=
            insBoundElim
              (insFreeElim
                (insFreeElim
                  insVar
                  nat502Neq500)
                nat501Neq500)
          
          let eqBody :=
            insBoundElim (insFreeElim insBody nat502Neq501)
          
          let eqHa :=
            insBoundElim
              (insFreeElim
                (insFreeElim
                  (insFreeElim
                    (insFreeElim
                      (insFreeElim insHa nat505Neq500)
                      nat504Neq500)
                    nat503Neq500)
                  nat502Neq500)
                nat501Neq500)
          
          let eqHb :=
            insBoundElim
              (insFreeElim
                (insFreeElim insHb nat505Neq503)
                nat504Neq503)
          
          let eqTail :=
            insBoundElim
              (insFreeElim
                (insFreeElim
                  (insFreeElim insArgT nat505Neq502)
                  nat504Neq502)
                nat503Neq502)
          
          eqFn7 ▸ eqBv ▸
          {
            varEnc := varAlias,
            isVarNat := eqVar ▸ isVar,
            exprEncBody := bodyAlias,
            boundValue := boundValue,
            eqExprEnc := rfl,
            eqExprEncExpr :=
              encodingToExpr.arbUnEncEq
                (eqVar ▸ isVar) (eqBody ▸ isBody),
            ins :=
              eqBody ▸ eqVar ▸ eqHa ▸ eqHb ▸ eqTail ▸
              insFn
          }
    
    structure inInterpOfIns.exprArbIr.InsOfIns
      (boundVars exprEnc p: Pair)
    where
      varEnc: Pair
      isVarNat: IsNatEncoding varEnc
      exprEncBody: Pair
      eqExprEnc: exprEnc = pair (fromNat 8) (pair varEnc exprEncBody)
      eqExprEncExpr:
        exprEnc.encodingToExpr
          =
        Expr.Ir varEnc.depth exprEncBody.encodingToExpr
      ins:
        ∀ boundValue,
          Ins
            uniDefList.interpretation
            (pair
              (pair (pair varEnc boundValue) boundVars)
              (pair exprEncBody p))
    
    noncomputable def inInterpOfIns.exprArbIr.insOfIns
      (ins:
        Ins
          uniDefList.interpretation.exprArbIntersection
          (pair boundVars (pair exprEnc p)))
    :
      InsOfIns boundVars exprEnc p
    :=
      let ⟨_varEnc, ⟨insDomainVar, ins⟩⟩ :=
        (insUnDomElim ins).unwrap
      let ⟨_bodyEnc, ⟨insDomainBody, ins⟩⟩ :=
        (insUnDomElim ins).unwrap
      let ⟨_bvAlias, ins⟩ := (insArbUnElim ins).unwrap
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isVar := Inw.toIsNatEncoding insDomainVar.toInw
      let isBody := Inw.toIsExprEncoding insDomainBody.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair _fromNat8 (pair varAlias bodyAlias) =>
        let ⟨insFn8, insExpr⟩ := insPairElim insEnc
        let ⟨insVar, insBody⟩ := insPairElim insExpr
        
        let eqFn8 := insNatExprElim insFn8
        let eqBv := insBoundElim insBv
        
        let eqVar :=
          insBoundElim
            (insFreeElim
              (insFreeElim
                insVar
                nat502Neq500)
              nat501Neq500)
        
        let eqBody :=
          insBoundElim (insFreeElim insBody nat502Neq501)
        
        eqFn8 ▸ eqBv ▸
        {
          varEnc := varAlias,
          isVarNat := eqVar ▸ isVar,
          exprEncBody := bodyAlias,
          eqExprEnc := rfl,
          eqExprEncExpr :=
            encodingToExpr.arbIrEncEq
              (eqVar ▸ isVar) (eqBody ▸ isBody),
          ins :=
            fun boundValue =>
              let ins := insArbIrElim insP boundValue
              let ins := insCallElimBound ins rfl nat504Neq501
              let ⟨arg, ⟨insFn, insArg⟩⟩ :=
                (insCallExprElim ins).unwrap
              
              match arg with
              | zero => insPairElim.nope insArg
              | pair zero _ => insPairElim.nope (insPairElim insArg).insL
              | pair (pair _hA _hB) _tail =>
                let ⟨insArgH, insArgT⟩ := insPairElim insArg
                let ⟨insHa, insHb⟩ := insPairElim insArgH
                
                let eqHa :=
                  insBoundElim
                    (insFreeElim
                      (insFreeElim
                        (insFreeElim
                          (insFreeElim
                            (insFreeElim insHa nat505Neq500)
                            nat504Neq500)
                          nat503Neq500)
                        nat502Neq500)
                      nat501Neq500)
                
                let eqHb :=
                  insBoundElim
                    (insFreeElim
                      (insFreeElim insHb nat505Neq503)
                      nat504Neq503)
                
                let eqTail :=
                  insBoundElim
                    (insFreeElim
                      (insFreeElim
                        (insFreeElim insArgT nat505Neq502)
                        nat504Neq502)
                      nat503Neq502)
                
                eqBody ▸ eqVar ▸ eqHa ▸ eqHb ▸ eqTail ▸
                insFn
        }
    
    
    mutual
    def inInterpOfIns.exprPair
      (ins:
        Ins
          uniDefList.interpretation.exprPair
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        exprEncA,
        exprEncB,
        pA,
        pB,
        eqP,
        eqExprEnc,
        eqExprEncExpr,
        insA,
        insB
      } :=
        inInterpOfIns.exprPair.insOfIns ins
      
      let inDefA := interpretationOfIns insA
      let inDefB := interpretationOfIns insB
      
      eqP ▸
      by unfold interp; exact eqExprEncExpr ▸
      insPair inDefA inDefB
    
    def inInterpOfIns.exprUn
      (ins:
        Ins
          uniDefList.interpretation.exprUnion
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        exprEncA,
        exprEncB,
        eqExprEnc,
        eqExprEncExpr,
        ins
      } :=
        inInterpOfIns.exprUn.insOfIns ins
      
      match ins with
      | Or.inl insA =>
        let inDefA := interpretationOfIns insA
        
        by
          unfold interp
          exact eqExprEncExpr ▸ insUnL inDefA _
      | Or.inr insB =>
        let inDefB := interpretationOfIns insB
        
        by
          unfold interp
          exact eqExprEncExpr ▸ insUnR _ inDefB
    
    def inInterpOfIns.exprIr
      (ins:
        Ins
          uniDefList.interpretation.exprIntersection
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        exprEncA,
        exprEncB,
        eqExprEnc,
        eqExprEncExpr,
        insA,
        insB
      } :=
        inInterpOfIns.exprIr.insOfIns ins
      
      let inDefA := interpretationOfIns insA
      let inDefB := interpretationOfIns insB
      
      by
        unfold interp
        exact eqExprEncExpr ▸ insIr inDefA inDefB
    
    def inInterpOfIns.exprCpl
      (ins:
        Ins
          uniDefList.interpretation.exprCpl
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        exprEncInner,
        eqExprEnc,
        eqExprEncExpr,
        ninw
      } :=
        inInterpOfIns.exprCpl.insOfIns ins
      
      let ninPos inPos := ninw (inwOfInterpretation inPos)
      
      by
        unfold interp
        exact eqExprEncExpr ▸ insCpl ninPos
    
    def inInterpOfIns.exprIfThen
      (ins:
        Ins
          uniDefList.interpretation.exprIfThen
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        exprEncCond,
        exprEncBody,
        c,
        eqExprEnc,
        eqExprEncExpr,
        insCond,
        insBody
      } :=
        inInterpOfIns.exprIfThen.insOfIns ins
      
      let inDefCond := interpretationOfIns insCond
      let inDefBody := interpretationOfIns insBody
      
      by
        unfold interp
        exact eqExprEncExpr ▸ insIfThen inDefCond inDefBody
    
    def inInterpOfIns.exprArbUn
      (ins:
        Ins
          uniDefList.interpretation.exprArbUnion
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        varEnc,
        isVarNat,
        exprEncBody,
        boundValue,
        eqExprEnc,
        eqExprEncExpr,
        ins
      } :=
        inInterpOfIns.exprArbUn.insOfIns ins
      
      let inDef := interpretationOfIns ins
      
      by
        unfold interp
        exact eqExprEncExpr ▸ insArbUn boundValue
          (addBoundVars.updateEq _ isVarNat _ _ ▸
          inDef)
    
    def inInterpOfIns.exprArbIr
      (ins:
        Ins
          uniDefList.interpretation.exprArbIntersection
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let {
        varEnc,
        isVarNat,
        exprEncBody,
        eqExprEnc,
        eqExprEncExpr,
        ins
      } :=
        inInterpOfIns.exprArbIr.insOfIns ins
      
      let inDef boundValue:
        Expr.Ins
          pairSalgebra
          ((addBoundVars theSetAsValuation boundVars).update
            varEnc.depth boundValue)
          exprEncBody.encodingToExpr
          p
      :=
        addBoundVars.updateEq _ isVarNat _ _ ▸
        interpretationOfIns (ins boundValue)
      
      by
        unfold interp
        exact eqExprEncExpr ▸ insArbIr inDef
    
    def interpretationOfIns
      (ins:
        Ins uniDefList.interpretation
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      insFinUnElim (insWfm.toInsWfmDef ins)
        inInterpOfIns.exprVar
        inInterpOfIns.exprZero
        inInterpOfIns.exprPair
        inInterpOfIns.exprUn
        inInterpOfIns.exprIr
        inInterpOfIns.exprCpl
        inInterpOfIns.exprIfThen
        inInterpOfIns.exprArbUn
        inInterpOfIns.exprArbIr
    
    def interpretationOfInw
      (inw:
        Inw uniDefList.interpretation
          (pair boundVars (pair expr p)))
    :
      (interp boundVars expr).posMem p
    :=
      inwFinUnElim (inwWfm.toInwWfmDef inw)
        inInterpOfInw.exprVar
        sorry
        sorry
        sorry
        sorry
        sorry
        sorry
        sorry
        sorry
    
    def insOfInterpretation
      (inDef: (interp boundVars expr).defMem p)
    :
      Ins
        uniDefList.interpretation
        (pair boundVars (pair expr p))
    :=
      sorry
    
    def inwOfInterpretation
      (inPos: (interp boundVars expr).posMem p)
    :
      Inw
        uniDefList.interpretation
        (pair boundVars (pair expr p))
    :=
      sorry
    end
    
    
    def freeInterpretationOfIns
      (ins: Ins uniDefList.freeInterpretation (pair expr p))
    :
      (interp zero expr).defMem p
    :=
      let ⟨_z, ⟨insFn, insArg⟩⟩ :=
        insCallExprElim (insWfm.toInsWfmDef ins)
      
      let zEq := insZeroElim insArg
      
      zEq ▸ interpretationOfIns insFn
    
    def freeInterpretationOfInw
      (ins: Inw uniDefList.freeInterpretation (pair expr p))
    :
      (interp zero expr).posMem p
    :=
      let ⟨_z, ⟨insFn, insArg⟩⟩ :=
        inwCallExprElim (inwWfm.toInwWfmDef ins)
      
      let zEq := inwZeroElim insArg
      
      zEq ▸ interpretationOfInw insFn
    
    
    def insOfFreeInterpretation
      (inDef: (interp zero expr).defMem p)
    :
      Ins uniDefList.freeInterpretation (pair expr p)
    :=
      insWfmDef.toInsWfm
        (insCallExpr
          (insOfInterpretation inDef)
          insZero)
    
    def inwOfFreeInterpretation
      (inPos: (interp zero expr).posMem p)
    :
      Inw uniDefList.freeInterpretation (pair expr p)
    :=
      inwWfmDef.toInwWfm
        (inwCallExpr
          (inwOfInterpretation inPos)
          inwZero)
    
    
    def inDefNthOfInsTheSet
      (ins: Ins uniDefList.theSet (pair (fromNat x) p))
    :
      Set3.defMem
        (interp zero (IsTheDefListExprPair.getNthExpr x).expr)
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
    
    def inPosNthOfInwTheSet
      (inw: Inw uniDefList.theSet (pair (fromNat x) p))
    :
      Set3.posMem
        (interp zero (IsTheDefListExprPair.getNthExpr x).expr)
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
    
    
    def insTheSetOfInDefNth
      (inDef:
        Set3.defMem
          (interp zero (IsTheDefListExprPair.getNthExpr x).expr)
          p)
    :
      Ins uniDefList.theSet (pair (fromNat x) p)
    :=
      insWfmDef.toInsWfm
        (insUnDom
          (insNatEncoding
            (fromNat.isNatEncoding x))
          (insPair
            insBound
            (insCallExpr
              (insOfFreeInterpretation inDef)
              (insCallExpr
                (insTheDefListExpr
                  (IsTheDefListExprPair.getNthExpr x).isNth)
                (insFree
                  (insFree
                    insBound
                    nat501Neq500)
                  nat502Neq500)))))
    
    def inwTheSetOfInPosNth
      (inPos:
        Set3.posMem
          (interp zero (IsTheDefListExprPair.getNthExpr x).expr)
          p)
    :
      Inw uniDefList.theSet (pair (fromNat x) p)
    :=
      inwWfmDef.toInwWfm
        (inwUnDom
          (insNatEncoding
            (fromNat.isNatEncoding x)).toInw
          (inwPair
            inwBound
            (inwCallExpr
              (inwOfFreeInterpretation inPos)
              (inwCallExpr
                (insTheDefListExpr
                  (show
                    -- Why is this necessary?
                    IsTheDefListExpr (pair _ _)
                  from
                    (IsTheDefListExprPair.getNthExpr x).isNth)).toInw
                (inwFree
                  (inwFree
                    inwBound
                    nat501Neq500)
                  nat502Neq500)))))
    
  end uniSet3
end Pair
