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
      (isNat: IsNatEncoding x)
      {d tail: Pair}
    :
      InsGetBound (pair (pair x d) tail) x d
    :=
      insWfmDefToIns
        (insUnL _
          (insUnDom
            (insNatEncoding isNat)
            (insArbUn
              d
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
      (neq: headX ≠ xEnc)
    :
      InsGetBound (pair (pair headX headD) tail) xEnc p
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
                    (insCpl _
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
      (isBoundTo: IsBoundTo boundVars x d)
    :
      InsGetBound (boundVarsEncoding boundVars) (fromNat x) d
    :=
      match isBoundTo with
      | IsBoundTo.InHead =>
        insGetBound.head (fromNat.isNatEncoding x)
      | IsBoundTo.InTail isGetTail neq _ =>
        insGetBound.ofInsTailNeqHead
          (insGetBound isGetTail)
          (fromNat.injNeq neq.symm)
    
    
    def Inw.toIsBoundTo
      (inw:
        InwGetBound (boundVarsEncoding boundVars) (fromNat x) d)
    :
      IsBoundTo boundVars x d
    :=
      (inwUnElim (inwWfmToInwDef inw)).elim
        (fun inw =>
          let ⟨_, ⟨_, inw⟩⟩ := inwUnDomElim inw
          let ⟨_, inw⟩ := inwArbUnElim inw
          let ⟨inwL, inwR⟩ := inwPairElim inw
          let ⟨inwXEnc, inwD⟩ := inwPairElim inwR
          
          let eqXR :=
            inwBoundElim (inwFreeElim inwXEnc nat501Neq500)
          let eqD := inwBoundElim inwD
          
          match boundVars with
          | ⟨_, _⟩ :: _ =>
            let ⟨inwHead, _⟩ := inwPairElim inwL
            let ⟨inwHeadX, inwHeadD⟩ := inwPairElim inwHead
            
            let eqHeadD := inwBoundElim inwHeadD
            let eqHeadXL :=
              inwBoundElim (inwFreeElim inwHeadX nat501Neq500)
            
            let eqHeadX :=
              fromNat.injEq (eqHeadXL.trans eqXR.symm)
            
            eqHeadD ▸ eqHeadX ▸ eqD ▸ IsBoundTo.InHead)
        (fun inw =>
          let ⟨_, inw⟩ := inwArbUnElim inw
          let ⟨_, inw⟩ := inwArbUnElim inw
          -- Renaming `inw_c` to `inw` triggers a Lean bug.
          let ⟨inwBv, inw_c⟩ := inwPairElim inw
          
          match boundVars with
          | ⟨_, headX⟩ :: _ =>
            let ⟨inwBvH, inwBvT⟩ := inwPairElim inwBv
            let ⟨inwHeadX, _⟩ := inwPairElim inwBvH
            
            let ninsHeadX := inwCplElim inwHeadX
            let eqT := inwBoundElim inwBvT
            
            let ⟨inwXEnc, inw⟩ := inwPairElim inw_c
            let eqXEnc :=
              inwBoundElim (inwFreeElim inwXEnc nat501Neq500)
            
            let inw := inwCallElimBound inw rfl nat502Neq500
            let inw := inwCallElimBound inw rfl nat503Neq501
            let ih := toIsBoundTo (eqT ▸ eqXEnc ▸ inw)
            
            let neq: x ≠ headX :=
              fun eq =>
                let ins500 := eqXEnc ▸ eq ▸ insBound
                ninsHeadX (insFree ins500 nat501Neq500)
            
            IsBoundTo.InTail ih neq _)
    
    def Inw.toInsGetBound
      (inw:
        InwGetBound
          (boundVarsEncoding boundVars)
          (fromNat x)
          d)
    :
      InsGetBound
        (boundVarsEncoding boundVars)
        (fromNat x)
        d
    :=
      insGetBound (Inw.toIsBoundTo inw)
    
  end uniSet3
end Pair
