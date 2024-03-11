import UniDefList
import Wfm
import PairDictOrder
import PairDepthDictOrder

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
      
      let eqL := inwBoundElim insL
      let eqR := inwBoundElim insR
      let eqN := eqR.trans eqL.symm
      
      ⟨n.val, {
        isNat := Inw.toIsNatEncoding inwNatN
        eq := eq ▸ (inwBoundElim insL) ▸ eqN ▸ rfl
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
    def nat503Neq500: 504 ≠ 500 := by simp
    def nat504Neq500: 503 ≠ 500 := by simp
    
    def nat500NeqNat: 500 ≠ 0 := by simp
    def nat500NeqNatLe: 500 ≠ 2 := by simp
    def nat500NeqPairDictLt: 500 ≠ 9 := by simp
    
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
          
          wfm.insWfmDef.toInsWfm
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
            let pInnerEq: pair a bA = pInner := inwBoundElim inw500ABA
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
          | zero => inwPairElim.nope inwBody
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
            (insFree (insNat isEEV) nat500NeqNat)
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
        let eq := inwBoundElim bInw500
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
                    (insZthMember (insFree insBound nat502Neq500))
                    insAny)
                  (insPair
                    (insFstMember (insFree insBound nat502Neq500))
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
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)))
                    (insPair
                      (eq ▸ insBound)
                      (insFstMember
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500)))))))
    
    def Inw.toIsPairDictLt p (inw: Inw pairDictLt p):
      IsPairDictLt p
    :=
      inwFinUnElim (wfm.inwWfm.toInwWfmDef inw)
        (fun inwZeroPair =>
          match p with
          | zero => inwPairElim.nope inwZeroPair
          | pair a b =>
            let ⟨l, r⟩ := inwPairElim inwZeroPair
            match b with
            | zero => inwPairElim.nope r
            | pair _ _ =>
              (inwZeroElim l) ▸ trivial)
        (fun inwLtLeft =>
          let ⟨pBound, inwDomain, inwBody⟩ := inwUnDomElim inwLtLeft
          match p with
          | zero => inwPairElim.nope inwBody
          | pair a b =>
            let ⟨l, r⟩ := inwPairElim inwBody
            match a, b with
            | zero, _ => inwPairElim.nope l
            | _, zero => inwPairElim.nope r
            | pair aA aB, pair bA bB =>
              let ⟨inwZth, _⟩ := inwPairElim l
              let ⟨inwFst, _⟩ := inwPairElim r
              
              let ⟨fst, inw500A⟩ := inwZthMemberElim inwZth nat502Neq500
              let ⟨zth, inw500B⟩ := inwFstMemberElim inwFst nat502Neq500
              
              let eqA := inwBoundElim inw500A
              let eqB := inwBoundElim inw500B
              
              let eq: pair aA bA = pBound :=
                Pair.noConfusion (eqA.trans eqB.symm)
                (fun eqZth _ => eqZth ▸ eqB)
              
              let inwA: Inw pairDictLt (pair aA bA) :=
                eq ▸ inwFreeElim inwDomain nat500NeqPairDictLt
              
              have:
                (pair aA bA).depth
                  <
                (pair (pair aA aB) (pair bA bB)).depth
              :=
                let leSA := Pair.depthSuccLeL aA aB
                let leSB := Pair.depthSuccLeL bA bB
                (Pair.depth.casesEq aA bA).elim
                  (fun eq => eq ▸ (leSA.trans_lt (Pair.depthLtL _ _)))
                  (fun eq => eq ▸ (leSB.trans_lt (Pair.depthLtR _ _)))
              
              Or.inl (toIsPairDictLt (pair aA bA) inwA))
        (fun inwEqLeft =>
          let ⟨pRBound, inwDomain, inwBody⟩ := inwUnDomElim inwEqLeft
          let ⟨pLBound, inwBody⟩ := inwArbUnElim inwBody
          
          match p with
          | zero => inwPairElim.nope inwBody
          | pair a b =>
            let ⟨l, r⟩ := inwPairElim inwBody
            match a, b with
            | zero, _ => inwPairElim.nope l
            | _, zero => inwPairElim.nope r
            | pair aA aB, pair bA bB =>
              let ⟨inw501A, inwZth⟩ := inwPairElim l
              let ⟨inw501B, inwFst⟩ := inwPairElim r
              
              let ⟨fst, inw500ABFst⟩ := inwZthMemberElim inwZth nat502Neq500
              let ⟨zth, inw500ZthBB⟩ := inwFstMemberElim inwFst nat502Neq500
              
              let eqRA := inwBoundElim
                (inwFreeElim (inw500ABFst) nat501Neq500)
              let eqRB := inwBoundElim
                (inwFreeElim (inw500ZthBB) nat501Neq500)
              
              let eq: pair aB bB = pRBound :=
                Pair.noConfusion (eqRA.trans eqRB.symm)
                (fun eqZth _ => eqZth ▸ eqRB)
              
              let inwB: Inw pairDictLt (pair aB bB) :=
                eq ▸ inwFreeElim inwDomain nat500NeqPairDictLt
              
              have:
                (pair aB bB).depth
                  <
                (pair (pair aA aB) (pair bA bB)).depth
              :=
                let leSL := Pair.depthSuccLeR aA aB
                let leSR := Pair.depthSuccLeR bA bB
                (Pair.depth.casesEq aB bB).elim
                  (fun eq => eq ▸ (leSL.trans_lt (Pair.depthLtL _ _)))
                  (fun eq => eq ▸ (leSR.trans_lt (Pair.depthLtR _ _)))
              
              let r := toIsPairDictLt (pair aB bB) inwB
              
              Or.inr
                (And.intro
                  ((inwBoundElim inw501A).trans (inwBoundElim inw501B).symm)
                  r))
    termination_by Inw.toIsPairDictLt p inw => p.depth
    
    structure IsNatLeFn.Pair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: natDecode b ≤ natDecode a
    
    def IsNatLeFn: Pair → Prop
    | zero => False
    | pair a b => IsNatLeFn.Pair a b
    
    def insNatLeFn (isNatLeFn: IsNatLeFn p): Ins natLeFn p :=
      match p with
      | zero => isNatLeFn.elim
      | pair a b =>
        let isNatLeReverse: IsNatLe (pair b a) := {
          isNatA := isNatLeFn.isNatB
          isNatB := isNatLeFn.isNatA
          isLe := isNatLeFn.isLe
        }
        
        wfm.insWfmDef.toInsWfm
          (insUnDom
            (insNatLe isNatLeReverse)
            (insPair
              (insFstMember (insFree insBound nat501Neq500))
              (insZthMember (insFree insBound nat501Neq500))))
    
    def Inw.toIsNatLeFn (inw: Inw natLeFn p):
      IsNatLeFn p
    :=
      let ⟨pBound, inwDomain, inwBody⟩ :=
        inwUnDomElim (wfm.inwWfm.toInwWfmDef inw)
      
      match p with
      | zero => inwPairElim.nope inwBody
      | pair a b =>
        let ⟨l, r⟩ := inwPairElim inwBody
        
        let ⟨_zth, inw500A⟩ := inwFstMemberElim l nat501Neq500
        let ⟨_fst, inw500B⟩ := inwZthMemberElim r nat501Neq500
        
        let eqA := inwBoundElim inw500A
        let eqB := inwBoundElim inw500B
        
        let eq: pair b a = pBound :=
          Pair.noConfusion (eqA.trans eqB.symm)
            (fun zthEq _ => zthEq ▸ eqA)
        
        let ⟨isNatB, isNatA, isLe⟩: IsNatLe (pair b a) :=
          eq ▸ Inw.toIsNatLe inwDomain
        
        { isNatA, isNatB, isLe }
    
    
  end uniSet
end Pair
