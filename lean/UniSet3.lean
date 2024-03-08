import UniDefList
import Wfm

namespace Pair
  namespace uniSet
    open Expr
    open PairExpr
    open uniDefList
    
    def IsNatEncoding: Set Pair
    | zero => True
    | pair a b => (IsNatEncoding a) ∧ b = zero
    
    def NatEncoding := { p // IsNatEncoding p }
    
    
    def natDecode: (p: Pair) → Nat
    | zero => 0
    | pair a _ => Nat.succ (natDecode a)
    
    def natDecode.eq (eq: a = b):
      natDecode a = natDecode b
    :=
      congr rfl eq
    
    def natDecode.zeroEq: natDecode Pair.zero = 0 := rfl
    def natDecode.eqZero (eqZ: p = Pair.zero):
      natDecode p = 0
    :=
      eqZ ▸ natDecode.zeroEq
    
    def natDecode.succPredEq
      (a b: Pair)
    :
      natDecode (pair a b)
        =
      Nat.succ (natDecode a)
    :=
      rfl
    
    def natDecode.injEq
      (isNatA: IsNatEncoding a)
      (isNatB: IsNatEncoding b)
      (eq: natDecode a = natDecode b)
    :
      a = b
    :=
      match a, b with
      | zero, zero => rfl
      | zero, pair bA bB =>
        let eqL: 0 = natDecode (pair bA bB) :=
          natDecode.zeroEq.symm.trans eq
        let eqR := natDecode.succPredEq bA bB
        
        Nat.noConfusion (eqL.trans eqR)
      | pair aA aB, zero =>
        let eqL: 0 = natDecode (pair aA aB) :=
          natDecode.zeroEq.symm.trans eq.symm
        let eqR := natDecode.succPredEq aA aB
        
        Nat.noConfusion (eqL.trans eqR)
      | pair aA aB, pair bA bB =>
        let eqPred: natDecode aA = natDecode bA :=
          Nat.noConfusion eq id
        let eqA: aA = bA :=
          natDecode.injEq isNatA.left isNatB.left eqPred
        let eqB: aB = bB :=
          isNatA.right.trans isNatB.right.symm
        
        congr (congr rfl eqA) eqB
    
    def natDecode.injNeq
      (isNatA: IsNatEncoding a)
      (isNatB: IsNatEncoding b)
      (neq: a ≠ b)
    :
      natDecode a ≠ natDecode b
    :=
      (natDecode.injEq isNatA isNatB).contra neq
    
    def ins := wfm.insWfm pairSalgebra uniDefList.defList
    def inw := wfm.inwWfm pairSalgebra uniDefList.defList
    
    def insV := Expr.ins pairSalgebra
    def inwV := Expr.ins pairSalgebra
    
    
    def insNat (isPn: IsNatEncoding pn): ins nat pn :=
      match pn with
      | Pair.zero =>
        wfm.insWfmDef.toInsWfm (insUnL (insZero _) _)
      
      | Pair.pair a b =>
        let insA: ins nat a := insNat isPn.left
        let insExpr: ins nat.expr (Pair.pair a b) :=
          insUnR _ (insPair
            insA
            ((insZeroIff _ _).mpr isPn.right))
        wfm.insWfmDef.toInsWfm insExpr
    
    def inwNat.isNatEncoding (w: inw nat pn): IsNatEncoding pn :=
      let inwNatDef: inw nat.expr pn :=
        wfm.inwWfm.toInwWfmDef w
      
      inwNatDef.elim
        (fun (pnInwZero: inw zeroExpr pn) =>
          let pnEqZero: pn = Pair.zero := (inwZeroIff _ _).mp pnInwZero
          pnEqZero ▸ trivial)
        (fun (w: inw (pairExpr nat zeroExpr) pn) =>
          match pn with
          | zero => trivial
          | pair _a _b =>
            And.intro
              (inwNat.isNatEncoding (inwPairElim _ w).inwL)
              (inwPairElim _ w).inwR)
    
    def ninwNat: ¬IsNatEncoding pn → ¬inw nat pn :=
      inwNat.isNatEncoding.contra
    
    
    structure IsNatPairAA.Str (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = Pair.pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAA.Str p n
    def NatPairAA := { p // IsNatPairAA p }
    
    def insNatPairAA (isPnaa: IsNatPairAA p): ins natPairAA p :=
      let np := isPnaa.unwrap
      
      let insD := insFree (insNat np.property.isNat) Nat.noConfusion
      let insPairAA := insPair insBound insBound
      
      np.property.eq ▸
        wfm.insWfmDef.toInsWfm (insUnDom insD insPairAA)
    
    def inwNatPairAA.isNatPairAA (w: inw natPairAA p): IsNatPairAA p :=
      let inwDef := wfm.inwWfm.toInwWfmDef w
      let n := (inwUnDomElim inwDef).unwrap
      
      let inwNatN: inw nat n :=
        inwFreeElim n.property.insDomain Nat.noConfusion
      
      let ⟨pairL, exR⟩ := inwPairElim.ex _ n.property.insBody
      let ⟨pairR, ⟨eq, insL, insR⟩⟩ := exR.unwrap
      
      let eqL := inwBoundEq insL
      let eqR := inwBoundEq insR
      let eqN := eqR.trans eqL.symm
      
      ⟨n.val, {
        isNat := inwNat.isNatEncoding inwNatN
        eq := eq ▸ (inwBoundEq insL) ▸ eqN ▸ rfl
      }⟩
    
    structure IsNatLe.Pair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: natDecode a ≤ natDecode b
    
    def IsNatLe: Pair → Prop
    | zero => False
    | pair a b => IsNatLe.Pair a b
    
    def nat501Neq500: 501 ≠ 500 := by simp
    def nat500Neq2: 500 ≠ 2 := by simp
    def insNatLe.abEq (isNatLe: IsNatLe (pair a b)): ins natLe (pair a b) :=
      let ⟨isNatA, isNatB, abLe⟩ := isNatLe
      
      if h: a = b then
        let isNatPairAA: IsNatPairAA (pair a b) :=
          ⟨a, {
            isNat := isNatA
            eq := h ▸ rfl
          }⟩
        
        wfm.insWfmDef.toInsWfm
          (insUnL (insNatPairAA isNatPairAA) _)
      else
        let natNeq: natDecode a ≠ natDecode b :=
          natDecode.injNeq isNatA isNatB h
        let abLt := Nat.lt_of_le_of_ne abLe natNeq
        let abPredLe := Nat.le_pred_of_lt abLt
        
        match hB: b with
        | zero =>
          let nope: _ < 0 := (natDecode.eqZero hB) ▸ abLt
          False.elim (Nat.not_lt_zero _ nope)
        | pair bA bB =>
          let abPredLe:
            natDecode a ≤ Nat.pred (Nat.succ (natDecode bA))
          := (natDecode.succPredEq bA bB) ▸ hB ▸ abPredLe
          
          let insNatLePred: ins natLe (pair a bA) := abEq {
            isNatA,
            isNatB := isNatB.left,
            isLe := abPredLe
          }
          
          let insL:
            insV (wfModel.update 500 (pair a bA)) (zthMember 501 500) a
          :=
            insZthMember
              insBound
              (fun isFree => nat501Neq500 isFree.left)
          
          let insR:
            insV (wfModel.update 500 (pair a bA)) (fstMember 501 500) bA
          :=
            insFstMember
              insBound
              (fun isFree => nat501Neq500 isFree.left)
          
          let insRSucc:
            insV
              (wfModel.update 500 (pair a bA))
              (succExpr (fstMember 501 500))
              (pair bA bB)
          :=
            isNatB.right ▸ insPair insR rfl
          
          wfm.insWfmDef.toInsWfm
            (insUnR _
              (insUnDom
                (insFree insNatLePred nat500Neq2)
                (insPair insL insRSucc)))
    
    def insNatLe (isNat: IsNatLe p): ins natLe p :=
      match p with
      | zero => False.elim isNat
      | pair _ _ => insNatLe.abEq isNat
    
    def IsNatPairAA.toIsNatLe (isAA: IsNatPairAA p): IsNatLe p :=
      let ⟨_n, isAA⟩ := isAA.unwrap
      isAA.eq ▸ {
        isNatA := isAA.isNat,
        isNatB := isAA.isNat
        isLe := Nat.le_refl _,
      }
    
    def inwNatLe.isNatLe.abEq
      (w: inw natLe (Pair.pair a b))
    :
      IsNatLe (Pair.pair a b)
    :=
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwPairAA =>
          (inwNatPairAA.isNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨pInner, inwDomain, inwBody⟩ := inwUnDomElim inwR
          let ⟨_inwA, inwB⟩ := inwPairElim _ inwBody
          let ⟨aZth500, bInwSucc⟩ := inwPairElim _ inwBody
          match b with
          | zero =>
            False.elim (inwPairElim.notZero _ bInwSucc rfl)
          | pair bA bB =>
            let ⟨bAFst500, bBInwZeroExpr⟩ := inwPairElim _ inwB
            let bBEqZero: bB = Pair.zero :=
              (insZeroIff wfModel bB).mp bBInwZeroExpr
            let inw500ABA :=
              inwZthFstElim _ aZth500 bAFst500 nat501Neq500 rfl
            let pInnerEq: pair a bA = pInner := inwBoundEq inw500ABA
            let isNatLeABA: IsNatLe (pair a bA) :=
              abEq (pInnerEq ▸ inwDomain)
            bBEqZero ▸ {
              isNatA := isNatLeABA.isNatA
              isNatB := And.intro isNatLeABA.isNatB rfl
              isLe := Nat.le_succ_of_le isNatLeABA.isLe
            })
    
    def inwNatLe.isNatLe (w: inw natLe p): IsNatLe p :=
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwPairAA =>
          (inwNatPairAA.isNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨_pInner, _inwDomain, inwBody⟩ := inwUnDomElim inwR
          match p with
          | zero => False.elim (inwPairElim.notZero _ inwBody rfl)
          | pair _ _ => isNatLe.abEq w)
    
  end uniSet
end Pair
