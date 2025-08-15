-- The first section of chapter 8. See the zeroth section.

import old.UniSet3.Ch8_S00_Defs


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insNatEncoding (isPn: IsNatEncoding pn): InsEdl nat pn :=
      match pn with
      | Pair.zero =>
        insWfmDefToIns (insUnL _ insZero)
      
      | Pair.pair a b =>
        let insA: InsEdl nat a := insNatEncoding isPn.left
        let insExpr: InsEdl nat.expr (Pair.pair a b) :=
          insUnR _ (insPair insA (isPn.right ▸ insZero))
        
        insWfmDefToIns insExpr
    
    def Inw.toIsNatEncoding (w: InwEdl nat pn): IsNatEncoding pn :=
      let inwNatDef: InwEdl nat.expr pn :=
        inwWfmToInwDef w
      
      inwNatDef.elim
        (fun (pnInwZero: InwEdl zeroExpr pn) =>
          let pnEqZero: pn = Pair.zero := inwZeroElim pnInwZero
          pnEqZero ▸ trivial)
        (fun (w: InwEdl (pairExpr nat zeroExpr) pn) =>
          match pn with
          | zero => trivial
          | pair _a _b =>
            And.intro
              (Inw.toIsNatEncoding (inwPairElim w).inwL)
              (inwPairElim w).inwR)
    
    def ninwNat: ¬IsNatEncoding pn → ¬InwEdl nat pn :=
      Inw.toIsNatEncoding.contra
    
    
    def insNatPairAA (isPnaa: IsNatPairAA p): InsEdl natPairAA p :=
      match p with
      | zero => isPnaa.elim
      | pair _ _ =>
        isPnaa.eq ▸
        insWfmDefToIns
          (insUnDom
            (insFree
              (insNatEncoding
                isPnaa.isNatA)
              Nat.noConfusion)
            (insPair insBound insBound))
    
    def Inw.toIsNatPairAA (w: InwEdl natPairAA p): IsNatPairAA p :=
      let inwDef := inwWfmToInwDef w
      let ⟨n, ⟨inwDomain, inw⟩⟩ := inwUnDomElim inwDef
      
      let inwNatN: InwEdl nat n :=
        inwFreeElim inwDomain Nat.noConfusion
      
      let ⟨_pairL, ⟨_pairR, ⟨eq, inwL, inwR⟩⟩⟩ := inwPairElim.ex inw
      
      let eqL := inwBoundElim inwL
      let eqR := inwBoundElim inwR
      
      eq ▸
      {
        isNatA := eqL ▸ Inw.toIsNatEncoding inwNatN
        eq := eqL.trans eqR.symm
      }
    
    
    def insNatLe.ab (isNatLe: IsNatLe (pair a b)): InsEdl natLe (pair a b) :=
      let ⟨isNatA, isNatB, abLe⟩ := isNatLe
      
      if h: a = b then
        let isNatPairAA: IsNatPairAA (pair a b) :=
          {
            isNatA := isNatA
            eq := h ▸ rfl
          }
        
        insWfmDefToIns
          (insUnL _ (insNatPairAA isNatPairAA))
      else
        let natNeq: a.depth ≠ b.depth :=
          depth.nat.injNeq isNatA isNatB h
        let abLt := Nat.lt_of_le_of_ne abLe natNeq
        let abPredLe := Nat.le_pred_of_lt abLt
        
        match hB: b with
        | zero =>
          let nope: _ < 0 := depth.zeroEq ▸ hB ▸ abLt
          False.elim (Nat.not_lt_zero _ nope)
        | pair bA _bB =>
          let abPredLe:
            a.depth ≤ Nat.pred (Nat.succ (bA.depth))
          := (depth.nat.eqSuccDepthPred isNatB) ▸ hB ▸ abPredLe
          
          let insNatLePred: InsEdl natLe (pair a bA) := ab {
            isNatA,
            isNatB := isNatB.left,
            isLe := abPredLe
          }
          
          insWfmDefToIns
            (insUnR _
              (insUnDom
                (insFree insNatLePred nat500NeqNatLe)
                (insPair
                  (insZthMember (insFree insBound nat501Neq500))
                  (insPair
                    (insFstMember (insFree insBound nat501Neq500))
                    isNatB.right))))
    
    def insNatLe (isNat: IsNatLe p): InsEdl natLe p :=
      match p with
      | zero => False.elim isNat
      | pair _ _ => insNatLe.ab isNat
    
    
    def Inw.toIsNatLe.ab
      (w: InwEdl natLe (Pair.pair a b))
    :
      IsNatLe (Pair.pair a b)
    :=
      (inwWfmToInwDef w).elim
        (fun inwPairAA =>
          (Inw.toIsNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨pInner, inwDomain, inwBody⟩ := inwUnDomElim inwR
          let ⟨_inwA, inwB⟩ := inwPairElim inwBody
          let ⟨aZth500, bInwSucc⟩ := inwPairElim inwBody
          match b with
          | zero => inwPairElim.nope bInwSucc
          | pair bA _bB =>
            let ⟨bAFst500, bBInwZeroExpr⟩ := inwPairElim inwB
            let inw500ABA :=
              inwZthFstElim aZth500 bAFst500 nat501Neq500 rfl
            let pInnerEq: pair a bA = pInner := inwBoundElim inw500ABA
            let isNatLeABA: IsNatLe (pair a bA) :=
              ab (pInnerEq ▸ inwDomain)
            {
              isNatA := isNatLeABA.isNatA
              isNatB := And.intro
                isNatLeABA.isNatB
                (inwZeroElim bBInwZeroExpr)
              isLe := (isNatLeABA.isLe.trans (depthLeL _ _))
            })
    
    def Inw.toIsNatLe (w: InwEdl natLe p): IsNatLe p :=
      (inwWfmToInwDef w).elim
        (fun inwPairAA =>
          (Inw.toIsNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨_pInner, _inwDomain, inwBody⟩ := inwUnDomElim inwR
          match p with
          | zero => inwPairElim.nope inwBody
          | pair _ _ => Inw.toIsNatLe.ab w)
    
    
    def insNatLeFn (isNatLeFn: IsNatLeFn p): InsEdl natLeFn p :=
      match p with
      | zero => isNatLeFn.elim
      | pair a b =>
        let isNatLeReverse: IsNatLe (pair b a) := {
          isNatA := isNatLeFn.isNatB
          isNatB := isNatLeFn.isNatA
          isLe := isNatLeFn.isLe
        }
        
        insWfmDefToIns
          (insUnDom
            (insNatLe isNatLeReverse)
            (insPair
              (insFstMember (insFree insBound nat501Neq500))
              (insZthMember (insFree insBound nat501Neq500))))
    
    def Inw.toIsNatLeFn (inw: InwEdl natLeFn p):
      IsNatLeFn p
    :=
      let ⟨_pBound, inwDomain, inwBody⟩ :=
        inwUnDomElim (inwWfmToInwDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair a b =>
        let ⟨l, r⟩ := inwPairElim inwBody
        
        let eq := inwBoundElim (inwZthFstElim r l nat501Neq500 rfl)
        
        let ⟨isNatB, isNatA, isLe⟩: IsNatLe (pair b a) :=
          eq ▸ Inw.toIsNatLe inwDomain
        
        { isNatA, isNatB, isLe }
    
    
    def insNatLt (isNatLt: IsNatLt p):
      InsEdl natLt p
    :=
      match p with
      | zero => isNatLt.elim
      | pair a b =>
        let ⟨isNatA, isNatB, isLt⟩ := isNatLt
        let isLe := Nat.le_of_lt isLt
        let neq: a ≠ b := fun eq => isLt.ne (congr rfl eq)
        
        insWfmDefToIns
          (insIr
            (insNatLe { isNatA, isNatB, isLe })
            (insCpl _
              (fun inw =>
                let ⟨_, inw⟩ := inwArbUnElim inw
                let ⟨inwA, inwB⟩ := inwPairElim inw
                
                let aEq := inwBoundElim inwA
                let bEq := inwBoundElim inwB
                
                neq (aEq.trans bEq.symm))))
    
    def Inw.toIsNatLt (inw: InwEdl natLt p):
      IsNatLt p
    :=
      let ⟨inwNatLe, inwNotRefl⟩ := inwIrElim (inwWfmToInwDef inw)
      
      match p with
      | zero => Inw.toIsNatLe inwNatLe
      | pair a b =>
        let ⟨isNatA, isNatB, isLe⟩ := Inw.toIsNatLe inwNatLe
        
        let neq: a ≠ b :=
          fun eq =>
            inwCplElim
              inwNotRefl
              (insArbUn a (insPair insBound (eq ▸ insBound)))
        
        let neqDepth := depth.nat.injNeq isNatA isNatB neq
        let isLt := Nat.lt_of_le_of_ne isLe neqDepth
        
        { isNatA, isNatB, isLt }
    
  end uniSet3
end Pair
