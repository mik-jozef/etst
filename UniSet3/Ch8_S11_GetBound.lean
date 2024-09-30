-- The eleventh section of chapter 8. See the zeroth section.

import UniSet3.Ch8_S10_TheDefList


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def InsGetBound bv xEnc p :=
      InsEdl uniDefList.getBound (pair bv (pair xEnc p))
    
    def InwGetBound bv xEnc p :=
      InwEdl uniDefList.getBound (pair bv (pair xEnc p))
    
    
    def insGetBound.head
      (isNat: IsNatEncoding hA)
      (hB tail: Pair)
    :
      InsGetBound (pair (pair hA hB) tail) hA hB
    :=
      insWfmDefToIns
        (insUnL _
          (insUnDom
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
                insBound)))))
    
    def insGetBound.ofInsTailNeqHead
      (ins: InsGetBound tail xEnc p)
      (neq: hA ≠ xEnc)
    :
      InsGetBound (pair (pair hA hB) tail) xEnc p
    :=
      insWfmDefToIns
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
                        neq
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
                      nat502Neq500)))))))
    
    def insGetBound
      (isGetBound: IsGetBound boundVars xEnc p)
    :
      InsGetBound boundVars xEnc p
    :=
      match isGetBound with
      | IsGetBound.InHead isNat hB tail =>
        insGetBound.head isNat hB tail
      | IsGetBound.InTail isGetTail hB neq =>
        insGetBound.ofInsTailNeqHead (insGetBound isGetTail) neq
    
    
    def Inw.toIsGetBound
      (inw: InwGetBound boundVars xEnc p)
    :
      IsGetBound boundVars xEnc p
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
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
          
          match boundVars with
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
            IsGetBound.InHead isNat _ _)
        (fun inw =>
          let ⟨xEncAlias, inw⟩ := inwArbUnElim inw
          let ⟨tail, inw⟩ := inwArbUnElim inw
          -- Renaming `inw_c` to `inw` triggers a Lean bug.
          let ⟨inwBv, inw_c⟩ := inwPairElim inw
          
          match boundVars with
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
            let ih := toIsGetBound inw
            
            let eqXEnc :=
              inwBoundElim (inwFreeElim inwXEnc nat501Neq500)
            
            eqT ▸ eqXEnc ▸
            IsGetBound.InTail ih _ neq)
    
    def Inw.toInsGetBound
      (inw: InwGetBound boundVars xEnc p)
    :
      InsGetBound boundVars xEnc p
    :=
      insGetBound (Inw.toIsGetBound inw)
    
  end uniSet3
end Pair
