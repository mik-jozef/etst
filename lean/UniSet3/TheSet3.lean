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
    
    def insTheSet.toIsNat
      (ins: Ins uniDefList.theSet (pair xEnc p))
    :
      IsNatEncoding xEnc
    :=
      let ⟨_xEncAlias, ⟨insDomain, ins⟩⟩ :=
        insUnDomElim (insWfm.toInsWfmDef ins)
      let ⟨insL, _⟩ := insPairElim ins
      
      insBoundElim insL ▸
      Inw.toIsNatEncoding insDomain.toInw
    
    
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
      by
        unfold interp
        rw [encodingToExpr.varEncEq isNat]
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
            
            (ofInsBoundVars ins).left)
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
    
    mutual
    def inInterpOfIns.exprPair
      (ins:
        Ins
          uniDefList.interpretation.exprPair
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let ⟨exprEncA, ⟨insDomainA, ins⟩⟩ := insUnDomElim ins
      let ⟨exprEncB, ⟨insDomainB, ins⟩⟩ := insUnDomElim ins
      let ⟨bvAlias, ins⟩ := insArbUnElim ins
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc, p with
      | zero, _ => insPairElim.nope insEnc
      | pair _ zero, _ =>
        insPairElim.nope (insPairElim insEnc).insR
      | _, zero => insPairElim.nope insP
      | pair fromNat2 (pair exprAliasA exprAliasB),
        pair pA pB
      =>
        let ⟨insFn2, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let ⟨insPa, insPb⟩ := insPairElim insP
        
        let insA := insCallElimBound insPa rfl nat503Neq500
        let insA := insCallElimBound insA rfl nat504Neq502
        let inDefA := interpretationOfIns insA
        
        let insB := insCallElimBound insPb rfl nat503Neq501
        let insB := insCallElimBound insB rfl nat504Neq502
        let inDefB := interpretationOfIns insB
        
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
        by
          unfold interp
          rw [encodingToExpr.pairEncEq isExprA isExprB]
          exact insPair inDefA inDefB
    
    def inInterpOfIns.exprUn
      (ins:
        Ins
          uniDefList.interpretation.exprUnion
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let ⟨exprEncA, ⟨insDomainA, ins⟩⟩ := insUnDomElim ins
      let ⟨exprEncB, ⟨insDomainB, ins⟩⟩ := insUnDomElim ins
      let ⟨bvAlias, ins⟩ := insArbUnElim ins
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair fromNat3 (pair exprAliasA exprAliasB) =>
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
        
        eqFn3 ▸ eqBv ▸ eqExprA ▸ eqExprB ▸
        by
          unfold interp
          rw [encodingToExpr.unEncEq isExprA isExprB]
          exact
            (insUnElim insP).elim
              (fun ins =>
                let ins := insCallElimBound ins rfl nat503Neq500
                let ins := insCallElimBound ins rfl nat504Neq502
                insUnL (interpretationOfIns ins) _)
              (fun ins =>
                let ins := insCallElimBound ins rfl nat503Neq501
                let ins := insCallElimBound ins rfl nat504Neq502
                insUnR _ (interpretationOfIns ins))
    
    def inInterpOfIns.exprIr
      (ins:
        Ins
          uniDefList.interpretation.exprIntersection
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let ⟨exprEncA, ⟨insDomainA, ins⟩⟩ := insUnDomElim ins
      let ⟨exprEncB, ⟨insDomainB, ins⟩⟩ := insUnDomElim ins
      let ⟨bvAlias, ins⟩ := insArbUnElim ins
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair fromNat4 (pair exprAliasA exprAliasB) =>
        let ⟨insFn4, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let ⟨insA, insB⟩ := insIrElim insP
        
        let insA := insCallElimBound insA rfl nat503Neq500
        let insA := insCallElimBound insA rfl nat504Neq502
        let inDefA := interpretationOfIns insA
        
        let insB := insCallElimBound insB rfl nat503Neq501
        let insB := insCallElimBound insB rfl nat504Neq502
        let inDefB := interpretationOfIns insB
        
        let eqFn4 := insNatExprElim insFn4
        let eqBv := insBoundElim insBv
        
        let eqExprA :=
          insBoundElim
            (insFreeElim
              (insFreeElim insExprA nat502Neq500)
              nat501Neq500)
        
        let eqExprB :=
          insBoundElim (insFreeElim insExprB nat502Neq501)
        
        eqFn4 ▸ eqBv ▸ eqExprA ▸ eqExprB ▸
        by
          unfold interp
          rw [encodingToExpr.irEncEq isExprA isExprB]
          exact insIr inDefA inDefB
    
    def inInterpOfIns.exprCpl
      (ins:
        Ins
          uniDefList.interpretation.exprCpl
          (pair boundVars (pair cplEnc p)))
    :
      (interp boundVars cplEnc).defMem p
    :=
      let ⟨exprEnc, ⟨insDomain, ins⟩⟩ := insUnDomElim ins
      let ⟨bvAlias, ins⟩ := insArbUnElim ins
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insCplEnc, insP⟩ := insPairElim ins
      
      let isExpr := Inw.toIsExprEncoding insDomain.toInw
      
      match cplEnc with
      | zero => insPairElim.nope insCplEnc
      | pair fromNat5 exprAlias =>
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
        
        let ninPos
          (inPos: (interp boundVars exprEnc).posMem p)
        :=
          ninw (inwOfInterpretation inPos)
        
        eqFn5 ▸ eqExpr ▸
        by
          unfold interp
          rw [encodingToExpr.cplEncEq isExpr]
          exact ninPos
    
    def inInterpOfIns.exprIfThen
      (ins:
        Ins
          uniDefList.interpretation.exprIfThen
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      let ⟨exprEncA, ⟨insDomainA, ins⟩⟩ := insUnDomElim ins
      let ⟨exprEncB, ⟨insDomainB, ins⟩⟩ := insUnDomElim ins
      let ⟨bvAlias, ins⟩ := insArbUnElim ins
      let ⟨insBv, ins⟩ := insPairElim ins
      let ⟨insEnc, insP⟩ := insPairElim ins
      
      let isExprA := Inw.toIsExprEncoding insDomainA.toInw
      let isExprB := Inw.toIsExprEncoding insDomainB.toInw
      
      match exprEnc with
      | zero => insPairElim.nope insEnc
      | pair _ zero =>
        insPairElim.nope (insPairElim insEnc).insR
      | pair fromNat6 (pair exprAliasA exprAliasB) =>
        let ⟨insFn6, insExpr⟩ := insPairElim insEnc
        let ⟨insExprA, insExprB⟩ := insPairElim insExpr
        
        let ⟨⟨c, insCond⟩, insBody⟩ := insIfThenElim insP
        
        let insCond := insCallElimBound insCond rfl nat503Neq500
        let insCond := insCallElimBound insCond rfl nat504Neq502
        let inDefCond := interpretationOfIns insCond
        
        let insBody := insCallElimBound insBody rfl nat503Neq501
        let insBody := insCallElimBound insBody rfl nat504Neq502
        let inDefBody := interpretationOfIns insBody
        
        let eqFn6 := insNatExprElim insFn6
        let eqBv := insBoundElim insBv
        
        let eqExprA :=
          insBoundElim
            (insFreeElim
              (insFreeElim insExprA nat502Neq500)
              nat501Neq500)
        
        let eqExprB :=
          insBoundElim (insFreeElim insExprB nat502Neq501)
        
        eqFn6 ▸ eqBv ▸ eqExprA ▸ eqExprB ▸
        by
          unfold interp
          rw [encodingToExpr.ifThenEncEq isExprA isExprB]
          exact insIfThen inDefCond inDefBody
    
    def inInterpOfIns.exprArbUn
      (ins:
        Ins
          uniDefList.interpretation.exprArbUnion
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      sorry
    
    def inInterpOfIns.exprArbIr
      (ins:
        Ins
          uniDefList.interpretation.exprArbIntersection
          (pair boundVars (pair exprEnc p)))
    :
      (interp boundVars exprEnc).defMem p
    :=
      sorry
    
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
