import UniDefList
import Wfm

namespace Pair
  namespace uniSet
    open Expr
    open PairExpr
    open uniDefList
    
    
    def Ins := wfm.InsWfm pairSalgebra uniDefList.defList
    def Inw := wfm.InwWfm pairSalgebra uniDefList.defList
    
    def InsV := Expr.Ins pairSalgebra
    def InwV := Expr.Inw pairSalgebra
    
    
    def insNat (isPn: IsNatEncoding pn): Ins nat pn :=
      match pn with
      | Pair.zero =>
        wfm.insWfmDef.toInsWfm (insUnL (insZero _) _)
      
      | Pair.pair a b =>
        let insA: Ins nat a := insNat isPn.left
        let insExpr: Ins nat.expr (Pair.pair a b) :=
          insUnR _ (insPair
            insA
            ((insZeroIff _ _).mpr isPn.right))
        wfm.insWfmDef.toInsWfm insExpr
    
    def inwNat.isNatEncoding (w: Inw nat pn): IsNatEncoding pn :=
      let inwNatDef: Inw nat.expr pn :=
        wfm.inwWfm.toInwWfmDef w
      
      inwNatDef.elim
        (fun (pnInwZero: Inw zeroExpr pn) =>
          let pnEqZero: pn = Pair.zero := (inwZeroIff _ _).mp pnInwZero
          pnEqZero ▸ trivial)
        (fun (w: Inw (pairExpr nat zeroExpr) pn) =>
          match pn with
          | zero => trivial
          | pair _a _b =>
            And.intro
              (inwNat.isNatEncoding (inwPairElim _ w).inwL)
              (inwPairElim _ w).inwR)
    
    def ninwNat: ¬IsNatEncoding pn → ¬Inw nat pn :=
      inwNat.isNatEncoding.contra
    
    
    structure IsNatPairAA.Str (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = Pair.pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAA.Str p n
    def NatPairAA := { p // IsNatPairAA p }
    
    def insNatPairAA (isPnaa: IsNatPairAA p): Ins natPairAA p :=
      let np := isPnaa.unwrap
      
      let insD := insFree (insNat np.property.isNat) Nat.noConfusion
      let insPairAA := insPair insBound insBound
      
      np.property.eq ▸
        wfm.insWfmDef.toInsWfm (insUnDom insD insPairAA)
    
    def inwNatPairAA.isNatPairAA (w: Inw natPairAA p): IsNatPairAA p :=
      let inwDef := wfm.inwWfm.toInwWfmDef w
      let n := (inwUnDomElim inwDef).unwrap
      
      let inwNatN: Inw nat n :=
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
    def nat500Neq0: 500 ≠ 0 := by simp
    def nat500Neq2: 500 ≠ 2 := by simp
    def insNatLe.abEq (isNatLe: IsNatLe (pair a b)): Ins natLe (pair a b) :=
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
          
          let insNatLePred: Ins natLe (pair a bA) := abEq {
            isNatA,
            isNatB := isNatB.left,
            isLe := abPredLe
          }
          
          let insL:
            InsV (wfModel.update 500 (pair a bA)) (zthMember 501 500) a
          :=
            insZthMember
              insBound
              (fun isFree => nat501Neq500 isFree.left)
          
          let insR:
            InsV (wfModel.update 500 (pair a bA)) (fstMember 501 500) bA
          :=
            insFstMember
              insBound
              (fun isFree => nat501Neq500 isFree.left)
          
          let insRSucc:
            InsV
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
    
    def insNatLe (isNat: IsNatLe p): Ins natLe p :=
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
      (w: Inw natLe (Pair.pair a b))
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
    
    def inwNatLe.isNatLe (w: Inw natLe p): IsNatLe p :=
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwPairAA =>
          (inwNatPairAA.isNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨_pInner, _inwDomain, inwBody⟩ := inwUnDomElim inwR
          match p with
          | zero => False.elim (inwPairElim.notZero _ inwBody rfl)
          | pair _ _ => isNatLe.abEq w)
    
    
    def IsExprEncoding.Var: Pair → Prop
    | Pair.zero => False
    | Pair.pair (Pair.pair _ _) _ => False
    | Pair.pair zero x => IsNatEncoding x
    
    def insExprEncoding.Var (isEEV: IsExprEncoding.Var p):
      Ins exprEncoding.var p
    :=
      match p with
      | Pair.zero => False.elim isEEV
      | Pair.pair (Pair.pair _ _) _ => False.elim isEEV
      | Pair.pair zero _ =>
        wfm.insWfmDef.toInsWfm
          (insUnDom
            (insFree (insNat isEEV) nat500Neq0)
            (insPair (insZero _) insBound))
    
    def inwExprEncodingVar.IsExprEncodingVar
      (w: Inw exprEncoding.var p)
    :
      IsExprEncoding.Var p
    :=
      let ⟨_pBound, ⟨inwNatPBound, inwPairP⟩⟩ :=
        inwUnDomElim (wfm.inwWfm.toInwWfmDef w)
      match p with
      | zero => inwPairElim.nope _ inwPairP
      | pair (pair _ _) _ =>
        inwZeroElim.nope _ (inwPairElim _ inwPairP).inwL
      | pair zero _b =>
        let ⟨_, bInw500⟩ := inwPairElim _ inwPairP
        let eq := inwBoundEq bInw500
        eq ▸ (inwNat.isNatEncoding inwNatPBound)
    
    
    inductive IsExprEncoding.Bin (p: Pair): Prop :=
    | Is2 (eq: p = fromNat 2)
    | Is3 (eq: p = fromNat 3)
    | Is4 (eq: p = fromNat 4)
    | Is6 (eq: p = fromNat 6)
    
    def insExprEncoding.Binary (isEEB: IsExprEncoding.Bin p):
      Ins exprEncoding.binary p
    :=
      open IsExprEncoding.Bin in
      wfm.insWfmDef.toInsWfm
        (match isEEB with
        | Is2 eq => eq ▸ insUnL (insNatExpr _ _) _
        | Is3 eq => eq ▸ insUnR _ (insUnL (insNatExpr _ _) _)
        | Is4 eq => eq ▸ insUnR _ (insUnR _ (insUnL (insNatExpr _ _) _))
        | Is6 eq => eq ▸ insUnR _ (insUnR _ (insUnR _ (insNatExpr _ _))))
    
    def inwExprEncodingBinary.IsExprEncodingBinary
      (w: Inw exprEncoding.binary p)
    :
      IsExprEncoding.Bin p
    :=
      open IsExprEncoding.Bin in
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwNatExpr2 => Is2 (inwNatElim inwNatExpr2))
        (fun un => un.elim
          (fun inwNatExpr3 => Is3 (inwNatElim inwNatExpr3))
          (fun un => un.elim
            (fun inwNatExpr4 => Is4 (inwNatElim inwNatExpr4))
            (fun inwNatExpr6 => Is6 (inwNatElim inwNatExpr6))))
    
    
    inductive IsExprEncoding.Quantifier (p: Pair): Prop :=
    | Is7 (eq: p = fromNat 7)
    | Is8 (eq: p = fromNat 8)
    
    def insExprEncoding.Quantifier (isEEB: IsExprEncoding.Quantifier p):
      Ins exprEncoding.quantifier p
    :=
      open IsExprEncoding.Quantifier in
      wfm.insWfmDef.toInsWfm
        (match isEEB with
        | Is7 eq => eq ▸ insUnL (insNatExpr _ _) _
        | Is8 eq => eq ▸ insUnR _ (insNatExpr _ _))
    
    def inwExprEncodingQuantifier.IsExprEncodingQuantifier
      (w: Inw exprEncoding.quantifier p)
    :
      IsExprEncoding.Quantifier p
    :=
      open IsExprEncoding.Quantifier in
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwNatExpr7 => Is7 (inwNatElim inwNatExpr7))
        (fun inwNatExpr8 => Is8 (inwNatElim inwNatExpr8))
    
    
    inductive IsExprEncoding: Pair → Prop where
    | IsVar: IsNatEncoding x → IsExprEncoding (pair zero x)
    | IsZero: IsExprEncoding (pair (fromNat 1) zero)
    | IsBin:
      IsExprEncoding.Bin n →
      IsExprEncoding a →
      IsExprEncoding b →
      IsExprEncoding (pair n (pair a b))
    | IsCpl: IsExprEncoding p → IsExprEncoding (pair (fromNat 5) p)
    | IsQuantifier:
      IsExprEncoding.Quantifier n →
      IsNatEncoding x →
      IsExprEncoding body →
      IsExprEncoding (pair n (pair x body))
    
    def insExprEncoding (isEE: IsExprEncoding p):
      Ins exprEncoding p
    :=
      wfm.insWfmDef.toInsWfm
        (match isEE with
        | IsExprEncoding.IsVar isNatX =>
          let inList:
            Expr.var exprEncoding.var ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn inList (insExprEncoding.Var isNatX)
        | IsExprEncoding.IsZero =>
          let inList:
            Expr.var exprEncoding.zero ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn inList (wfm.insWfmDef.toInsWfm
            (insPair (insNatExpr _ _) (insZero _)))
        | IsExprEncoding.IsBin nBin aExpr bExpr =>
          let inList:
            exprEncoding.binExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair
              (insExprEncoding.Binary nBin)
              (insPair
                (insExprEncoding aExpr)
                (insExprEncoding bExpr)))
        | IsExprEncoding.IsCpl isExpr =>
          let inList:
            exprEncoding.cplExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair (insNatExpr _ 5) (insExprEncoding isExpr))
        | IsExprEncoding.IsQuantifier isQ isNat isExpr =>
          let inList:
            exprEncoding.quantifierExpr ∈ exprEncoding.exprList
          :=
            by unfold exprEncoding.exprList; simp
          
          insFinUn
            inList
            (insPair
              (insExprEncoding.Quantifier isQ)
              (insPair (insNat isNat) (insExprEncoding isExpr))))
  end uniSet
end Pair
