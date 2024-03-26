import UniSet3.Defs


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def insNatEncoding (isPn: IsNatEncoding pn): Ins nat pn :=
      match pn with
      | Pair.zero =>
        insWfmDef.toInsWfm (insUnL insZero _)
      
      | Pair.pair a b =>
        let insA: Ins nat a := insNatEncoding isPn.left
        let insExpr: Ins nat.expr (Pair.pair a b) :=
          insUnR _ (insPair insA (isPn.right ▸ insZero))
        
        insWfmDef.toInsWfm insExpr
    
    def Inw.toIsNatEncoding (w: Inw nat pn): IsNatEncoding pn :=
      let inwNatDef: Inw nat.expr pn :=
        inwWfm.toInwWfmDef w
      
      inwNatDef.elim
        (fun (pnInwZero: Inw zeroExpr pn) =>
          let pnEqZero: pn = Pair.zero := inwZeroElim pnInwZero
          pnEqZero ▸ trivial)
        (fun (w: Inw (pairExpr nat zeroExpr) pn) =>
          match pn with
          | zero => trivial
          | pair _a _b =>
            And.intro
              (Inw.toIsNatEncoding (inwPairElim w).inwL)
              (inwPairElim w).inwR)
    
    def ninwNat: ¬IsNatEncoding pn → ¬Inw nat pn :=
      Inw.toIsNatEncoding.contra
    
    
    def insNatPairAA (isPnaa: IsNatPairAA p): Ins natPairAA p :=
      match p with
      | zero => isPnaa.elim
      | pair _ _ =>
        isPnaa.eq ▸
        insWfmDef.toInsWfm
          (insUnDom
            (insFree
              (insNatEncoding
                isPnaa.isNatA)
              Nat.noConfusion)
            (insPair insBound insBound))
    
    def Inw.toIsNatPairAA (w: Inw natPairAA p): IsNatPairAA p :=
      let inwDef := inwWfm.toInwWfmDef w
      let ⟨n, ⟨inwDomain, inw⟩⟩ := inwUnDomElim inwDef
      
      let inwNatN: Inw nat n :=
        inwFreeElim inwDomain Nat.noConfusion
      
      let ⟨_pairL, ⟨_pairR, ⟨eq, inwL, inwR⟩⟩⟩ := inwPairElim.ex inw
      
      let eqL := inwBoundElim inwL
      let eqR := inwBoundElim inwR
      
      eq ▸
      {
        isNatA := eqL ▸ Inw.toIsNatEncoding inwNatN
        eq := eqL.trans eqR.symm
      }
    
    
    def insNatLe.ab (isNatLe: IsNatLe (pair a b)): Ins natLe (pair a b) :=
      let ⟨isNatA, isNatB, abLe⟩ := isNatLe
      
      if h: a = b then
        let isNatPairAA: IsNatPairAA (pair a b) :=
          {
            isNatA := isNatA
            eq := h ▸ rfl
          }
        
        insWfmDef.toInsWfm
          (insUnL (insNatPairAA isNatPairAA) _)
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
          
          let insNatLePred: Ins natLe (pair a bA) := ab {
            isNatA,
            isNatB := isNatB.left,
            isLe := abPredLe
          }
          
          insWfmDef.toInsWfm
            (insUnR _
              (insUnDom
                (insFree insNatLePred nat500NeqNatLe)
                (insPair
                  (insZthMember (insFree insBound nat501Neq500))
                  (insPair
                    (insFstMember (insFree insBound nat501Neq500))
                    isNatB.right))))
    
    def insNatLe (isNat: IsNatLe p): Ins natLe p :=
      match p with
      | zero => False.elim isNat
      | pair _ _ => insNatLe.ab isNat
    
    
    def Inw.toIsNatLe.ab
      (w: Inw natLe (Pair.pair a b))
    :
      IsNatLe (Pair.pair a b)
    :=
      (inwWfm.toInwWfmDef w).elim
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
    
    def Inw.toIsNatLe (w: Inw natLe p): IsNatLe p :=
      (inwWfm.toInwWfmDef w).elim
        (fun inwPairAA =>
          (Inw.toIsNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨_pInner, _inwDomain, inwBody⟩ := inwUnDomElim inwR
          match p with
          | zero => inwPairElim.nope inwBody
          | pair _ _ => Inw.toIsNatLe.ab w)
    
    
    def insNatLeFn (isNatLeFn: IsNatLeFn p): Ins natLeFn p :=
      match p with
      | zero => isNatLeFn.elim
      | pair a b =>
        let isNatLeReverse: IsNatLe (pair b a) := {
          isNatA := isNatLeFn.isNatB
          isNatB := isNatLeFn.isNatA
          isLe := isNatLeFn.isLe
        }
        
        insWfmDef.toInsWfm
          (insUnDom
            (insNatLe isNatLeReverse)
            (insPair
              (insFstMember (insFree insBound nat501Neq500))
              (insZthMember (insFree insBound nat501Neq500))))
    
    def Inw.toIsNatLeFn (inw: Inw natLeFn p):
      IsNatLeFn p
    :=
      let ⟨_pBound, inwDomain, inwBody⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair a b =>
        let ⟨l, r⟩ := inwPairElim inwBody
        
        let eq := inwBoundElim (inwZthFstElim r l nat501Neq500 rfl)
        
        let ⟨isNatB, isNatA, isLe⟩: IsNatLe (pair b a) :=
          eq ▸ Inw.toIsNatLe inwDomain
        
        { isNatA, isNatB, isLe }
    
    
    def insNatLt (isNatLt: IsNatLt p):
      Ins natLt p
    :=
      match p with
      | zero => isNatLt.elim
      | pair a b =>
        let ⟨isNatA, isNatB, isLt⟩ := isNatLt
        let isLe := Nat.le_of_lt isLt
        let neq: a ≠ b := fun eq => isLt.ne (congr rfl eq)
        
        insWfmDef.toInsWfm
          (insIr
            (insNatLe { isNatA, isNatB, isLe })
            (insCpl
              (fun inw =>
                let ⟨_, inw⟩ := inwArbUnElim inw
                let ⟨inwA, inwB⟩ := inwPairElim inw
                
                let aEq := inwBoundElim inwA
                let bEq := inwBoundElim inwB
                
                neq (aEq.trans bEq.symm))))
    
    def Inw.toIsNatLt (inw: Inw natLt p):
      IsNatLt p
    :=
      let ⟨inwNatLe, inwNotRefl⟩ := inwIrElim (inwWfm.toInwWfmDef inw)
      
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
