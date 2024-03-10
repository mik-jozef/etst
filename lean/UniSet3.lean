import UniDefList
import Wfm
import PairDictOrder

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
        wfm.insWfmDef.toInsWfm (insUnL insZero _)
      
      | Pair.pair a b =>
        let insA: Ins nat a := insNat isPn.left
        let insExpr: Ins nat.expr (Pair.pair a b) :=
          insUnR _ (insPair insA (isPn.right ▸ insZero))
        
        wfm.insWfmDef.toInsWfm insExpr
    
    def Inw.toIsNatEncoding (w: Inw nat pn): IsNatEncoding pn :=
      let inwNatDef: Inw nat.expr pn :=
        wfm.inwWfm.toInwWfmDef w
      
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
    
    
    structure IsNatPairAAOfN (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = Pair.pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAAOfN p n
    def NatPairAA := { p // IsNatPairAA p }
    
    def insNatPairAA (isPnaa: IsNatPairAA p): Ins natPairAA p :=
      let np := isPnaa.unwrap
      
      let insD := insFree (insNat np.property.isNat) Nat.noConfusion
      let insPairAA := insPair insBound insBound
      
      np.property.eq ▸
        wfm.insWfmDef.toInsWfm (insUnDom insD insPairAA)
    
    def Inw.toIsNatPairAA (w: Inw natPairAA p): IsNatPairAA p :=
      let inwDef := wfm.inwWfm.toInwWfmDef w
      let n := (inwUnDomElim inwDef).unwrap
      
      let inwNatN: Inw nat n :=
        inwFreeElim n.property.insDomain Nat.noConfusion
      
      let ⟨pairL, exR⟩ := inwPairElim.ex n.property.insBody
      let ⟨pairR, ⟨eq, insL, insR⟩⟩ := exR.unwrap
      
      let eqL := inwBoundEq insL
      let eqR := inwBoundEq insR
      let eqN := eqR.trans eqL.symm
      
      ⟨n.val, {
        isNat := Inw.toIsNatEncoding inwNatN
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
    def nat502Neq500: 502 ≠ 500 := by simp
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
          
          wfm.insWfmDef.toInsWfm
            (insUnR _
              (insUnDom
                (insFree insNatLePred nat500Neq2)
                (insPair insL (isNatB.right ▸ insPair insR rfl))))
    
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
    
    def Inw.toIsNatLe.abEq
      (w: Inw natLe (Pair.pair a b))
    :
      IsNatLe (Pair.pair a b)
    :=
      (wfm.inwWfm.toInwWfmDef w).elim
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
            let pInnerEq: pair a bA = pInner := inwBoundEq inw500ABA
            let isNatLeABA: IsNatLe (pair a bA) :=
              abEq (pInnerEq ▸ inwDomain)
            {
              isNatA := isNatLeABA.isNatA
              isNatB := And.intro
                isNatLeABA.isNatB
                (inwZeroElim bBInwZeroExpr)
              isLe := Nat.le_succ_of_le isNatLeABA.isLe
            })
    
    def Inw.toIsNatLe (w: Inw natLe p): IsNatLe p :=
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwPairAA =>
          (Inw.toIsNatPairAA inwPairAA).toIsNatLe)
        (fun inwR =>
          let ⟨_pInner, _inwDomain, inwBody⟩ := inwUnDomElim inwR
          match p with
          | zero => False.elim (inwPairElim.notZero inwBody rfl)
          | pair _ _ => Inw.toIsNatLe.abEq w)
    
    
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
            (insPair insZero insBound))
    
    def Inw.toIsExprEncoding.Var
      (w: Inw exprEncoding.var p)
    :
      IsExprEncoding.Var p
    :=
      let ⟨_pBound, ⟨inwNatPBound, inwPairP⟩⟩ :=
        inwUnDomElim (wfm.inwWfm.toInwWfmDef w)
      match p with
      | zero => inwPairElim.nope inwPairP
      | pair (pair _ _) _ =>
        inwZeroElim.nope (inwPairElim inwPairP).inwL
      | pair zero _b =>
        let ⟨_, bInw500⟩ := inwPairElim inwPairP
        let eq := inwBoundEq bInw500
        eq ▸ (Inw.toIsNatEncoding inwNatPBound)
    
    
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
    
    def Inw.toIsExprEncoding.Binary
      (w: Inw exprEncoding.binary p)
    :
      IsExprEncoding.Bin p
    :=
      open IsExprEncoding.Bin in
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwNatExpr2 => Is2 (inwNatExprElim inwNatExpr2))
        (fun un => un.elim
          (fun inwNatExpr3 => Is3 (inwNatExprElim inwNatExpr3))
          (fun un => un.elim
            (fun inwNatExpr4 => Is4 (inwNatExprElim inwNatExpr4))
            (fun inwNatExpr6 => Is6 (inwNatExprElim inwNatExpr6))))
    
    
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
    
    def Inw.toIsExprEncoding.Quantifier
      (w: Inw exprEncoding.quantifier p)
    :
      IsExprEncoding.Quantifier p
    :=
      open IsExprEncoding.Quantifier in
      (wfm.inwWfm.toInwWfmDef w).elim
        (fun inwNatExpr7 => Is7 (inwNatExprElim inwNatExpr7))
        (fun inwNatExpr8 => Is8 (inwNatExprElim inwNatExpr8))
    
    
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
            (insPair (insNatExpr _ _) insZero))
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
    
    def Inw.toIsExprEncoding
      (w: Inw exprEncoding p)
    :
      IsExprEncoding p
    :=
      open IsExprEncoding in
      inwFinUnElim (wfm.inwWfm.toInwWfmDef w)
        (fun inwVar =>
          match p with
          | Pair.zero =>
            let isVar := Inw.toIsExprEncoding.Var inwVar
            False.elim isVar
          | Pair.pair (Pair.pair _ _) _ =>
            let isVar := Inw.toIsExprEncoding.Var inwVar
            False.elim isVar
          | Pair.pair zero _ =>
            IsVar (Inw.toIsExprEncoding.Var inwVar))
        (fun inwZero =>
          let ⟨_l, _r, ⟨eq, inwL, inwR⟩⟩ :=
            inwPairElim.ex (wfm.inwWfm.toInwWfmDef inwZero)
          
          eq ▸ (inwNatExprElim inwL) ▸ (inwZeroElim inwR) ▸ IsZero)
        (fun inwBin =>
          match p with
          | Pair.zero => inwPairElim.nope inwBin
          | Pair.pair _l r =>
            let ⟨inwL, inwR⟩ := inwPairElim inwBin
            
            match r with
            | Pair.zero => inwPairElim.nope inwR
            | Pair.pair _ _ =>
              let ⟨rInwL, rInwR⟩ := inwPairElim inwR
              
              IsBin
                (Inw.toIsExprEncoding.Binary inwL)
                (Inw.toIsExprEncoding rInwL)
                (Inw.toIsExprEncoding rInwR))
        (fun inwCpl =>
          match p with
          | Pair.zero => inwPairElim.nope inwCpl
          | Pair.pair _ _ =>
            let ⟨l, r⟩ := inwPairElim inwCpl
            (inwNatExprElim l) ▸ IsCpl (toIsExprEncoding r))
        (fun inwQuant =>
          match p with
          | Pair.zero => inwPairElim.nope inwQuant
          | Pair.pair _l r =>
            let ⟨inwL, inwR⟩ := inwPairElim inwQuant
            
            match r with
            | Pair.zero => inwPairElim.nope inwR
            | Pair.pair _ _ =>
              let ⟨rInwL, rInwR⟩ := inwPairElim inwR
              
              IsQuantifier
                (Inw.toIsExprEncoding.Quantifier inwL)
                (Inw.toIsNatEncoding rInwL)
                (Inw.toIsExprEncoding rInwR))
    
    
    -- Encodes a prefix of a definition list
    def IsDefEncoding: Pair → Prop
    | Pair.zero => True
    | Pair.pair a b => IsExprEncoding a ∧ IsDefEncoding b
    
    def insDefEncoding (isDefEnc: IsDefEncoding p):
      Ins defEncoding p
    :=
      wfm.insWfmDef.toInsWfm
        (match p with
        | Pair.zero => insUnL insZero _
        | Pair.pair _ _ =>
          insUnR
            _
            (insPair
              (insExprEncoding isDefEnc.left)
              (insDefEncoding isDefEnc.right)))
    
    def Inw.toIsDefEncoding (w: Inw defEncoding p):
      IsDefEncoding p
    :=
      match p with
      | Pair.zero => trivial
      | Pair.pair _ _ =>
        (wfm.inwWfm.toInwWfmDef w).elim
          (fun inwL => inwZeroElim.nope inwL)
          (fun inwR =>
            let ⟨l, r⟩ := inwPairElim inwR
            
            And.intro
              (Inw.toIsExprEncoding l)
              (Inw.toIsDefEncoding r))
    
    
    def IsPairDictLt: Pair → Prop
    | zero => False
    | pair a b => a < b
    
    def insPairDictLt (isPD: IsPairDictLt p):
      Ins pairDictLt p
    :=
      let inListZeroPair:
        pairDictLt.zeroPair ∈ pairDictLt.list
      :=
        by unfold pairDictLt.list; simp
      
      let inListLtLeft:
        pairDictLt.ltLeft ∈ pairDictLt.list
      :=
        by unfold pairDictLt.list; simp
      
      let inListEqLeft:
        pairDictLt.eqLeft ∈ pairDictLt.list
      :=
        by unfold pairDictLt.list; simp
      
      match p with
      | zero => isPD.elim
      | pair zero zero => isPD.elim
      | pair zero (pair _ _) =>
        wfm.insWfmDef.toInsWfm
          (insFinUn
            inListZeroPair
            (insPair insZero (insPair insAny insAny)))
      | pair (pair aA aB) zero => isPD.elim
      | pair (pair aA aB) (pair bA bB) =>
        
        open Pair.dictOrder.LtTotal in
        match Pair.dictOrder.ltTotal aA bA with
        | IsLt ab =>
          let ipd: IsPairDictLt (pair aA bA) := ab
          let aInsAB := insPairDictLt ipd
          
          wfm.insWfmDef.toInsWfm
            (insFinUn
              inListLtLeft
              (insUnDom aInsAB
                (insPair
                  (insPair
                    (insZthMember
                      insBound
                      (fun isFree => nat502Neq500 isFree.left))
                    insAny)
                  (insPair
                    (insFstMember
                      insBound
                      (fun isFree => nat502Neq500 isFree.left))
                    insAny))))
        | IsGt ba =>
          isPD.elim
            (fun ab => dictOrder.ltAntisymm ab ba)
            (fun ⟨eq, _⟩ => dictOrder.ltIrefl (eq ▸ ba))
        | IsEq eq =>
          let ipd: IsPairDictLt (pair aB bB) :=
            isPD.elim
              (fun ab => dictOrder.ltIrefl (eq ▸ ab))
              (fun ⟨_, lt⟩ => lt)
          let bInsAB := insPairDictLt ipd
          
          wfm.insWfmDef.toInsWfm
            (insFinUn
              inListEqLeft
              (insUnDom bInsAB
                (insArbUn aA
                  (insPair
                    (insPair
                      insBound
                      (insZthMember
                        (insFree insBound nat501Neq500)
                        (fun isFree => nat502Neq500 isFree.left)))
                    (insPair
                      (eq ▸ insBound)
                      (insFstMember
                        (insFree insBound nat501Neq500)
                        (fun isFree => nat502Neq500 isFree.left)))))))
    
    def Inw.toIsPairDictLt (inw: Inw pairDictLt p):
      IsPairDictLt p
    :=
      inwFinUnElim (wfm.inwWfm.toInwWfmDef inw)
        (fun inwZeroPair =>
          let lb := inwPairElim inwZeroPair
          sorry)
        sorry
        sorry
  end uniSet
end Pair
