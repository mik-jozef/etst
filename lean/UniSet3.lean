import UniDefList
import Wfm
import PairDictOrderInstance
import PairDepthDictOrder

namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def Ins := InsWfm pairSalgebra uniDefList.defList
    def Inw := InwWfm pairSalgebra uniDefList.defList
    
    def InsV := Expr.Ins pairSalgebra
    def InwV := Expr.Inw pairSalgebra
    
    
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
    
    
    structure IsNatPairAAOfN (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = Pair.pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAAOfN p n
    def NatPairAA := { p // IsNatPairAA p }
    
    def insNatPairAA (isPnaa: IsNatPairAA p): Ins natPairAA p :=
      let np := isPnaa.unwrap
      
      let insD := insFree (insNatEncoding np.property.isNat) Nat.noConfusion
      let insPairAA := insPair insBound insBound
      
      np.property.eq ▸
        insWfmDef.toInsWfm (insUnDom insD insPairAA)
    
    def Inw.toIsNatPairAA (w: Inw natPairAA p): IsNatPairAA p :=
      let inwDef := inwWfm.toInwWfmDef w
      let n := (inwUnDomElim inwDef).unwrap
      
      let inwNatN: Inw nat n :=
        inwFreeElim n.property.inwDomain Nat.noConfusion
      
      let ⟨pairL, exR⟩ := inwPairElim.ex n.property.inwBody
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
      isLe: a.depth ≤ b.depth
    
    def IsNatLe: Pair → Prop
    | zero => False
    | pair a b => IsNatLe.Pair a b
    
    def nat501Neq500: 501 ≠ 500 := by simp
    def nat502Neq500: 502 ≠ 500 := by simp
    def nat502Neq501: 502 ≠ 501 := by simp
    def nat503Neq500: 503 ≠ 500 := by simp
    def nat504Neq500: 504 ≠ 500 := by simp
    
    def nat500NeqNat: 500 ≠ 0 := by simp
    def nat500NeqNatLe: 500 ≠ 2 := by simp
    def nat500NeqPairDictLt: 500 ≠ 9 := by simp
    def nat500NeqNatLeFn: 500 ≠ 10 := by simp
    def nat501NeqNatLeFn: 501 ≠ 10 := by simp
    def nat502NeqNatLeFn: 502 ≠ 10 := by simp
    def nat503NeqNatLeFn: 503 ≠ 10 := by simp
    def nat504NeqNatLeFn: 504 ≠ 10 := by simp
    def nat500NeqPairOfDepth: 500 ≠ 11 := by simp
    def nat501NeqPairOfDepth: 501 ≠ 11 := by simp
    def nat502NeqPairOfDepth: 502 ≠ 11 := by simp
    def nat503NeqPairOfDepth: 503 ≠ 11 := by simp
    
    
    def insNatLe.abEq (isNatLe: IsNatLe (pair a b)): Ins natLe (pair a b) :=
      let ⟨isNatA, isNatB, abLe⟩ := isNatLe
      
      if h: a = b then
        let isNatPairAA: IsNatPairAA (pair a b) :=
          ⟨a, {
            isNat := isNatA
            eq := h ▸ rfl
          }⟩
        
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
          
          let insNatLePred: Ins natLe (pair a bA) := abEq {
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
              abEq (pInnerEq ▸ inwDomain)
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
        insWfmDef.toInsWfm
          (insUnDom
            (insFree (insNatEncoding isEEV) nat500NeqNat)
            (insPair insZero insBound))
    
    def Inw.toIsExprEncoding.Var
      (w: Inw exprEncoding.var p)
    :
      IsExprEncoding.Var p
    :=
      let ⟨_pBound, ⟨inwNatPBound, inwPairP⟩⟩ :=
        inwUnDomElim (inwWfm.toInwWfmDef w)
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
      insWfmDef.toInsWfm
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
      (inwWfm.toInwWfmDef w).elim
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
      insWfmDef.toInsWfm
        (match isEEB with
        | Is7 eq => eq ▸ insUnL (insNatExpr _ _) _
        | Is8 eq => eq ▸ insUnR _ (insNatExpr _ _))
    
    def Inw.toIsExprEncoding.Quantifier
      (w: Inw exprEncoding.quantifier p)
    :
      IsExprEncoding.Quantifier p
    :=
      open IsExprEncoding.Quantifier in
      (inwWfm.toInwWfmDef w).elim
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
      insWfmDef.toInsWfm
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
          
          insFinUn inList (insWfmDef.toInsWfm
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
              (insPair (insNatEncoding isNat) (insExprEncoding isExpr))))
    
    def Inw.toIsExprEncoding
      (w: Inw exprEncoding p)
    :
      IsExprEncoding p
    :=
      open IsExprEncoding in
      inwFinUnElim (inwWfm.toInwWfmDef w)
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
            inwPairElim.ex (inwWfm.toInwWfmDef inwZero)
          
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
      insWfmDef.toInsWfm
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
        (inwWfm.toInwWfmDef w).elim
          (fun inwL => inwZeroElim.nope inwL)
          (fun inwR =>
            let ⟨l, r⟩ := inwPairElim inwR
            
            And.intro
              (Inw.toIsExprEncoding l)
              (Inw.toIsDefEncoding r))
    
    
    def IsPairDictLt: Pair → Prop
    | zero => False
    | pair a b => dictOrder.Lt a b
    
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
        insWfmDef.toInsWfm
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
          
          insWfmDef.toInsWfm
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
            (fun ab => dictOrder.Lt.antisymm ab ba)
            (fun ⟨eq, _⟩ => dictOrder.ltIrefl (eq ▸ ba))
        | IsEq eq =>
          let ipd: IsPairDictLt (pair aB bB) :=
            isPD.elim
              (fun ab => dictOrder.ltIrefl (eq ▸ ab))
              (fun ⟨_, lt⟩ => lt)
          let bInsAB := insPairDictLt ipd
          
          insWfmDef.toInsWfm
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
    
    def Inw.toIsPairDictLt.p p (inw: Inw pairDictLt p):
      IsPairDictLt p
    :=
      inwFinUnElim (inwWfm.toInwWfmDef inw)
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
              
              let eq: pair aA bA = pBound := inwBoundElim
                (inwZthFstElim inwZth inwFst nat502Neq500 rfl)
              
              let inwA: Inw pairDictLt (pair aA bA) :=
                eq ▸ inwFreeElim inwDomain nat500NeqPairDictLt
              
              have := depth.leZth aA aB bA bB
              Or.inl (toIsPairDictLt.p (pair aA bA) inwA))
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
              
              let eq := inwBoundElim
                (inwZthFstElim inwZth inwFst nat502Neq500 rfl)
              
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
                  (fun ⟨eq, _⟩ => eq ▸ (leSL.trans_lt (Pair.depthLtL _ _)))
                  (fun ⟨eq, _⟩ => eq ▸ (leSR.trans_lt (Pair.depthLtR _ _)))
              
              let r := toIsPairDictLt.p (pair aB bB) inwB
              
              Or.inr
                (And.intro
                  ((inwBoundElim inw501A).trans (inwBoundElim inw501B).symm)
                  r))
    termination_by Inw.toIsPairDictLt.p p inw => p.depth
    
    def Inw.toIsPairDictLt (inw: Inw pairDictLt p):
      IsPairDictLt p
    :=
      Inw.toIsPairDictLt.p p inw
    
    structure IsNatLeFn.Pair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: b.depth ≤ a.depth
    
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
    
    structure IsPairOfDepthAB (n p: Pair): Prop where
      isNat: IsNatEncoding n
      eqDepth: n.depth = p.depth
    
    def IsPairOfDepth: Pair → Prop
    | zero => False
    | pair n p => IsPairOfDepthAB n p
    
    def insPairOfDepth.p p (isPoD: IsPairOfDepth p):
      Ins pairOfDepth p
    :=
      match p with
      | zero => isPoD.elim
      | pair n p =>
        insWfmDef.toInsWfm
          (match n, p with
          | zero, zero =>
            let nEqZero := depth.eqZeroOfEqZero isPoD.eqDepth
            
            (insUnL (insPair (nEqZero ▸ insZero) insZero) _)
          | zero, pair _ _ => Nat.noConfusion isPoD.eqDepth
          | pair _ _, zero => Nat.noConfusion isPoD.eqDepth
          | pair nA nB, pair pA pB =>
            
            insUnR
              _
              ((depth.casesEq pA pB).elim
                (fun ⟨depthEq, depthLe⟩ =>
                  let isPoDA: IsPairOfDepth (pair nA pA) := {
                    isNat := isPoD.isNat.left
                    eqDepth :=
                      let depthEqN :=
                        depth.nat.eqSuccDepthPred isPoD.isNat
                      let succEq := depthEqN.symm.trans
                        (isPoD.eqDepth.trans depthEq)
                      
                      Nat.noConfusion succEq id
                  }
                  
                  let pBAndDepth := pair (fromNat pB.depth) pB
                  
                  let isPoDB: IsPairOfDepth pBAndDepth := {
                    isNat := fromNat.isNatEncoding _
                    eqDepth := fromNat.depthEq _
                  }
                  
                  have := depth.leZth nA nB pA pB
                  have:
                    pBAndDepth.depth
                      <
                    (pair (pair nA nB) (pair pA pB)).depth
                  :=
                    let eq: pBAndDepth.depth = Nat.succ pB.depth :=
                      (depth.casesEq (fromNat pB.depth) pB).elim
                        (fun ⟨eq, _⟩ =>
                          eq ▸ congr rfl (fromNat.depthEq pB.depth))
                        (fun ⟨eq, _⟩ => eq)
                    eq ▸ (Nat.succ_le_succ depthLe).trans_lt
                      ((Nat.succ_le_succ (depthLtL pA pB)).trans
                        (depthLtR (pair nA nB) (pair pA pB)))
                  
                  insUnDom
                    (insNatEncoding isPoD.isNat.left)
                    (insUnDom
                      (insCall
                        (insPairOfDepth.p _ isPoDA)
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500))
                      (insUnDom
                        (insCall
                          (insPairOfDepth.p _ isPoDB)
                          (insCall
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insNatLeFn {
                                      isNatA := isPoD.isNat.left
                                      isNatB := fromNat.isNatEncoding pB.depth
                                      isLe :=
                                        (fromNat.depthEq _) ▸
                                        isPoDA.eqDepth ▸ depthLe
                                    })
                                    nat501NeqNatLeFn)
                                  nat502NeqNatLeFn)
                                nat503NeqNatLeFn)
                              nat504NeqNatLeFn)
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    insBound
                                    nat501Neq500)
                                  nat502Neq500)
                                nat503Neq500)
                              nat504Neq500)))
                        (insUnL
                          (insPair
                            (insPair
                              (insFree
                                (insFree insBound nat501Neq500)
                                nat502Neq500)
                              (isPoD.isNat.right ▸ insZero))
                            (insPair
                              (insFree insBound nat502Neq501)
                              insBound))
                          _))))
                
                (fun ⟨depthEq, depthLt⟩ =>
                  let isPoDB: IsPairOfDepth (pair nA pB) := {
                    isNat := isPoD.isNat.left
                    eqDepth :=
                      let depthEqN :=
                        depth.nat.eqSuccDepthPred isPoD.isNat
                      let succEq := depthEqN.symm.trans
                        (isPoD.eqDepth.trans depthEq)
                      
                      Nat.noConfusion succEq id
                  }
                  
                  let pAAndDepth := pair (fromNat pA.depth) pA
                  
                  let isPoDA: IsPairOfDepth pAAndDepth := {
                    isNat := fromNat.isNatEncoding _
                    eqDepth := fromNat.depthEq _
                  }
                  
                  have := depth.leZthFst nA nB pA pB
                  have:
                    pAAndDepth.depth
                      <
                    (pair (pair nA nB) (pair pA pB)).depth
                  :=
                    let eq: pAAndDepth.depth = Nat.succ pA.depth :=
                      (depth.casesEq (fromNat pA.depth) pA).elim
                        (fun ⟨eq, _⟩ =>
                          eq ▸ congr rfl (fromNat.depthEq pA.depth))
                        (fun ⟨eq, _⟩ => eq)
                    let depthSuccLe := Nat.succ_le_of_lt depthLt
                    eq ▸ depthSuccLe.trans_lt
                      ((depthLtR pA pB).trans (depthLtR _ _))
                  
                  insUnDom
                    (insNatEncoding isPoD.isNat.left)
                    (insUnDom
                      (insCall
                        (insPairOfDepth.p _ isPoDB)
                        (insFree
                          (insFree insBound nat501Neq500)
                          nat502Neq500))
                      (insUnDom
                        (insCall
                          (insPairOfDepth.p _ isPoDA)
                          (insCall
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    (insNatLeFn {
                                      isNatA := isPoD.isNat.left
                                      isNatB := fromNat.isNatEncoding pA.depth
                                      isLe :=
                                        (fromNat.depthEq _) ▸
                                        isPoDB.eqDepth ▸
                                        Nat.le_of_lt depthLt
                                    })
                                    nat501NeqNatLeFn)
                                  nat502NeqNatLeFn)
                                nat503NeqNatLeFn)
                              nat504NeqNatLeFn)
                            (insFree
                              (insFree
                                (insFree
                                  (insFree
                                    insBound
                                    nat501Neq500)
                                  nat502Neq500)
                                nat503Neq500)
                              nat504Neq500)))
                        (insUnR
                          _
                          (insPair
                            (insPair
                              (insFree
                                (insFree insBound nat501Neq500)
                                nat502Neq500)
                              (isPoD.isNat.right ▸ insZero))
                            (insPair
                              insBound
                              (insFree insBound nat502Neq501)))))))))
    termination_by insPairOfDepth.p p isPoD => p.depth
    
    def insPairOfDepth (isPoD: IsPairOfDepth p):
      Ins pairOfDepth p
    :=
      insPairOfDepth.p p isPoD
    
    
    def Inw.toIsPairOfDepthAB n p (inw: Inw pairOfDepth (pair n p)):
      IsPairOfDepth (pair n p)
    :=
      (inwUnElim (inwWfm.toInwWfmDef inw)).elim
        (fun inw =>
          let ⟨l, r⟩ := inwPairElim inw
          let aEq := inwZeroElim l
          let bEq := inwZeroElim r
          
          let isZ: IsPairOfDepth (pair zero zero) := {
            isNat := trivial
            eqDepth := rfl
          }
          
          aEq ▸ bEq ▸ isZ)
        (fun inw =>
          let ⟨bound500, ___inwDomain, inwBody⟩ := inwUnDomElim inw
          let ⟨bound501, inwDomain501, inwBody⟩ := inwUnDomElim inwBody
          let ⟨bound502, inwDomain502, inwBody⟩ := inwUnDomElim inwBody
          
          let ⟨arg, ⟨inwFn, inwArg⟩⟩ := inwCallElim inwDomain501
          
          let argEq500 := inwBoundElim
            (inwFreeElim (inwFreeElim inwArg nat502Neq500) nat501Neq500)
          
          let inwPoD500501 := argEq500 ▸
            inwFreeElim
              (inwFreeElim
                (inwFreeElim inwFn nat502NeqPairOfDepth)
                nat501NeqPairOfDepth)
              nat500NeqPairOfDepth
          
          let ⟨argOuter, ⟨inwFnOuter, inwArgOuter⟩⟩ :=
            inwCallElim inwDomain502
          let ⟨argInner, ⟨inwFnInner, inwArgInner⟩⟩ :=
            inwCallElim inwArgOuter
          
          let argInnerIs500 :=
            inwBoundElim
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    (inwFreeElim inwArgInner nat504Neq500)
                  nat503Neq500)
                nat502Neq500)
              nat501Neq500)
          
          let ⟨isNat500, _isNatOuter, outerLe500⟩ :=
            argInnerIs500 ▸
            Inw.toIsNatLeFn
              (inwFreeElim
                (inwFreeElim
                  (inwFreeElim
                    (inwFreeElim
                      (inwFreeElim inwFnInner nat504NeqNatLeFn)
                    nat503NeqNatLeFn)
                  nat502NeqNatLeFn)
                nat501NeqNatLeFn)
              nat500NeqNatLeFn)
          
          (inwUnElim inwBody).elim
            (fun inw =>
              match h: n, p with
              | zero, _ => inwPairElim.nope (inwPairElim inw).inwL
              | _, zero => inwPairElim.nope (inwPairElim inw).inwR
              | pair nPred z, pair bA bB =>
                let ⟨inwSucc, inwPair⟩ := inwPairElim inw
                let ⟨inwPred, inwZ⟩ := inwPairElim inwSucc
                let ⟨inwA, inwB⟩ := inwPairElim inwPair
                
                let nPredEq500 :=
                  inwBoundElim
                    (inwFreeElim
                      (inwFreeElim inwPred nat502Neq500)
                      nat501Neq500)
                
                let aEq501 := inwBoundElim (inwFreeElim inwA nat502Neq501)
                let bEq502 := inwBoundElim inwB
                
                let zEq := inwZeroElim inwZ
                
                have: depth argOuter < depth n :=
                  h ▸
                  nPredEq500 ▸
                  outerLe500.trans_lt (depthLtL bound500 z)
                
                have: depth bound500 < depth n :=
                  h ▸ nPredEq500 ▸ (depthLtL nPred z)
                
                let isPodArgOuter502 := Inw.toIsPairOfDepthAB _ _
                  (inwFreeElim inwFnOuter nat503NeqPairOfDepth)
                
                let isPod500501 := Inw.toIsPairOfDepthAB _ _ inwPoD500501
                
                {
                  isNat :=
                    And.intro (nPredEq500 ▸ isNat500) zEq
                  eqDepth :=
                    let eqL: (pair nPred z).depth = Nat.succ nPred.depth :=
                      depth.eqL (zEq ▸ Nat.zero_le nPred.depth)
                    
                    let eqR: (pair bA bB).depth = Nat.succ bA.depth :=
                      depth.eqL
                        (aEq501 ▸
                        bEq502 ▸
                        isPod500501.eqDepth ▸
                        isPodArgOuter502.eqDepth ▸
                        outerLe500)
                    let eqMid: Nat.succ nPred.depth = Nat.succ bA.depth :=
                      aEq501 ▸
                      nPredEq500 ▸
                      congr rfl isPod500501.eqDepth
                    
                    (eqL.trans eqMid).trans eqR.symm
                })
            (fun inw =>
              match h: n, p with
              | zero, _ => inwPairElim.nope (inwPairElim inw).inwL
              | _, zero => inwPairElim.nope (inwPairElim inw).inwR
              | pair nPred z, pair bA bB =>
                let ⟨inwSucc, inwPair⟩ := inwPairElim inw
                let ⟨inwPred, inwZ⟩ := inwPairElim inwSucc
                let ⟨inwA, inwB⟩ := inwPairElim inwPair
                
                let nPredEq500 :=
                  inwBoundElim
                    (inwFreeElim
                      (inwFreeElim inwPred nat502Neq500)
                      nat501Neq500)
                
                let aEq502 := inwBoundElim inwA
                let bEq501 := inwBoundElim (inwFreeElim inwB nat502Neq501)
                
                let zEq := inwZeroElim inwZ
                
                have: depth argOuter < depth n :=
                  h ▸
                  nPredEq500 ▸
                  outerLe500.trans_lt (depthLtL bound500 z)
                
                have: depth bound500 < depth n :=
                  h ▸ nPredEq500 ▸ (depthLtL nPred z)
                
                let isPodArgOuter502 := Inw.toIsPairOfDepthAB _ _
                  (inwFreeElim inwFnOuter nat503NeqPairOfDepth)
                
                let isPod500501 := Inw.toIsPairOfDepthAB _ _ inwPoD500501
                
                {
                  isNat :=
                    And.intro (nPredEq500 ▸ isNat500) zEq
                  eqDepth :=
                    let eqL: (pair nPred z).depth = Nat.succ nPred.depth :=
                      depth.eqL (zEq ▸ Nat.zero_le nPred.depth)
                    
                    let eqR: (pair bA bB).depth = Nat.succ bB.depth :=
                      depth.eqR
                        (aEq502 ▸
                        bEq501 ▸
                        isPod500501.eqDepth ▸
                        isPodArgOuter502.eqDepth ▸
                        outerLe500)
                    let eqMid: Nat.succ nPred.depth = Nat.succ bB.depth :=
                      bEq501 ▸
                      nPredEq500 ▸
                      congr rfl isPod500501.eqDepth
                    
                    (eqL.trans eqMid).trans eqR.symm
                }))
    termination_by Inw.toIsPairOfDepthAB n p inw => n.depth
    
    def Inw.toIsPairOfDepth (inw: Inw pairOfDepth p):
      IsPairOfDepth p
    :=
      match p with
      | zero =>
          (inwUnElim (inwWfm.toInwWfmDef inw)).elim
            (fun l => inwPairElim.nope l)
            (fun r =>
              let ⟨_, ⟨_, inwBody⟩⟩ := inwUnDomElim r
              let ⟨_, ⟨_, inwBody⟩⟩ := inwUnDomElim inwBody
              let ⟨_, ⟨_, inwBody⟩⟩ := inwUnDomElim inwBody
              
              (inwUnElim inwBody).elim
                (fun l => inwPairElim.nope l)
                (fun r => inwPairElim.nope r))
      | pair a b => toIsPairOfDepthAB a b inw
    
  end uniSet3
end Pair
