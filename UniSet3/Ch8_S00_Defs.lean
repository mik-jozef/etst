/-
  # Chapter 8: The definitions of `theExternalDefList`
  
  This chapter describes most of the trisets defined by
  `theExternalDefList` of the previous chapter, along with some
  of their properties.
  
  Most of the trisets defined in `theExternalDefList` are classical.
  For every such triset `t`, we can define an `s: Set Pair` such
  that for all `p: Pair`,
  
      p ∈ t.defMem  ↔  p ∈ s  ↔  p ∈ t.posMem \,.              (0)
  
  Indeed, defining sets like this (usually using inductive
  propositions) is the main purpose of this section.
  
  ## Section 0: Definitions
  For almost every definition of `theExternalDefList`, we define
  a corresponding set `s`. For example, the definition
  `exprEncoding` is described by the indcutively defined set
  `IsExprEncoding: Pair → Prop`.
  
  Additionally, we prove some basic properties of these sets.
  For example, the lemma `IsExprEncoding.withIsBin` shows that
  if `pair n (pair a b)` is a pair encoding an expression, and
  `n` is a pair indicating a binary operation, then `a` and `b`
  are also pairs encoding expressions.
  
  ## Sections [1 to 12)
  These sections prove the equivalence (0) between the definitions
  of `theExternalDefList` and the sets defined in this section.
  Feel free to completely skip them, the statements are dull and
  the proofs are unreadable.
  
  ## Section 12
  The section defines the functions
  
      `Pair.exprToEncoding` \,,
      `Pair.encodingToExpr` \,, and
      `Pair.defListToEncoding` \,,
  
  which convert between expressions (with the signature for pairs)
  and their encodings.
  
  ## Section 13
  Finally, the last section defines the definition list represented
  by the definition `theDefList` of the previous chapter, called
  the internal definition list. It uses two notable functions of
  section 0:
  
      `IsTheDefListExprPair.getNthExpr` \,,
  
  which returns the `n`-th definition of the internal definition
  list, and
  
      `IsTheDefListExprPair.getIndexOf` \,,
  
  which for any finite prefix of any definition list, returns the
  index `i` where the prefix is contained in the internal definition
  list (in the sense that the `m`th definition of the prefix equals
  the `i + m`th definition of the internal definition list).
  
  Using the latter function, it is proven that the internal
  definition list defines all definable trisets of pairs.
  
  In subsequent chapters, we show that the well-founded model
  of the internal definition list is encoded by `uniSet3`, the
  triset defined by the definition `theSet` of the previous
  chapter.
-/

import UniSet3.Ch7_UniDefList
import Utils.PairDepthDictOrder


namespace Pair
  def boundVarsEncoding: List (ValVar Pair) → Pair
  | [] => Pair.zero
  | ⟨d, x⟩ :: rest =>
    Pair.pair (Pair.pair x d) (boundVarsEncoding rest)
  
  
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    /-
      `InsEdl x p` means that the definition `x` of the external
      definition list strongly contains the pair `p`.
      
      (Ie. let `m` be the well-founded model of the external
      definition list, then `p` is a definite member of `m x`.)
    -/
    def InsEdl := InsWfm pairSalgebra theExternalDefList.toDefList
    -- Weak containment is analogous to strong containment.
    def InwEdl := InwWfm pairSalgebra theExternalDefList.toDefList
    
    
    -- Helper proofs of that distinct variables are distinct.
    def nat501Neq500: 501 ≠ 500 := by decide
    def nat502Neq500: 502 ≠ 500 := by decide
    def nat502Neq501: 502 ≠ 501 := by decide
    def nat503Neq500: 503 ≠ 500 := by decide
    def nat503Neq501: 503 ≠ 501 := by decide
    def nat503Neq502: 503 ≠ 502 := by decide
    def nat504Neq500: 504 ≠ 500 := by decide
    def nat504Neq501: 504 ≠ 501 := by decide
    def nat504Neq502: 504 ≠ 502 := by decide
    def nat504Neq503: 504 ≠ 503 := by decide
    def nat505Neq500: 505 ≠ 500 := by decide
    def nat505Neq501: 505 ≠ 501 := by decide
    def nat505Neq502: 505 ≠ 502 := by decide
    def nat505Neq503: 505 ≠ 503 := by decide
    
    def nat500NeqNat: 500 ≠ 0 := by decide
    def nat500NeqNatLe: 500 ≠ 2 := by decide
    def nat500NeqExprEncoding: 500 ≠ 7 := by decide
    def nat500NeqDefEncoding: 500 ≠ 8 := by decide
    def nat501NeqDefEncoding: 501 ≠ 8 := by decide
    def nat500NeqPairDictLt: 500 ≠ 9 := by decide
    def nat500NeqNatLeFn: 500 ≠ 10 := by decide
    def nat501NeqNatLeFn: 501 ≠ 10 := by decide
    def nat502NeqNatLeFn: 502 ≠ 10 := by decide
    def nat503NeqNatLeFn: 503 ≠ 10 := by decide
    def nat504NeqNatLeFn: 504 ≠ 10 := by decide
    def nat500NeqPairOfDepth: 500 ≠ 11 := by decide
    def nat501NeqPairOfDepth: 501 ≠ 11 := by decide
    def nat502NeqPairOfDepth: 502 ≠ 11 := by decide
    def nat503NeqPairOfDepth: 503 ≠ 11 := by decide
    def nat500NeqNatLt: 500 ≠ 12 := by decide
    def nat500NeqIncrementExprs: 500 ≠ 21 := by decide
    def nat501NeqIncrementExprs: 501 ≠ 21 := by decide
    def nat502NeqIncrementExprs: 502 ≠ 21 := by decide
    def nat500NeqShiftDefEncoding: 500 ≠ 22 := by decide
    def nat501NeqShiftDefEncoding: 501 ≠ 22 := by decide
    def nat502NeqShiftDefEncoding: 502 ≠ 22 := by decide
    def nat503NeqShiftDefEncoding: 503 ≠ 22 := by decide
    def nat504NeqShiftDefEncoding: 504 ≠ 22 := by decide
    def nat500NeqTheDefList: 500 ≠ 32 := by decide
    def nat501NeqTheDefList: 501 ≠ 32 := by decide
    def nat502NeqTheDefList: 502 ≠ 32 := by decide
    def nat500NeqGetBounds: 500 ≠ 33 := by decide
    def nat501NeqGetBounds: 501 ≠ 33 := by decide
    def nat502NeqGetBounds: 502 ≠ 33 := by decide
    def nat503NeqGetBounds: 503 ≠ 33 := by decide
    def nat500NeqInterpretation: 500 ≠ 34 := by decide
    def nat501NeqInterpretation: 501 ≠ 34 := by decide
    def nat502NeqInterpretation: 502 ≠ 34 := by decide
    def nat503NeqInterpretation: 503 ≠ 34 := by decide
    def nat504NeqInterpretation: 504 ≠ 34 := by decide
    def nat505NeqInterpretation: 505 ≠ 34 := by decide
    
    
    structure IsNatPairAAPair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      eq: a = b
    
    -- `IsNatPairAA p` holds iff `p ∈ natPairAA`
    def IsNatPairAA: Pair → Prop
    | zero => False
    | pair a b => IsNatPairAAPair a b
    
    
    structure IsNatLePair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: a.depth ≤ b.depth
    
    -- `IsNatLe p` holds iff `p ∈ natLe`
    def IsNatLe: Pair → Prop
    | zero => False
    | pair a b => IsNatLePair a b
    
    def IsNatPairAA.toIsNatLe (isAA: IsNatPairAA p): IsNatLe p :=
      match p with
      | zero => isAA
      | pair _ _ =>
        isAA.eq ▸ {
          isNatA := isAA.isNatA,
          isNatB := isAA.eq ▸ isAA.isNatA
          isLe := Nat.le_refl _,
        }
    
    
    inductive IsExprEncoding.Bin (p: Pair): Prop :=
    | Is2 (eq: p = fromNat 2)
    | Is3 (eq: p = fromNat 3)
    | Is4 (eq: p = fromNat 4)
    | Is6 (eq: p = fromNat 6)
    
    inductive IsExprEncoding.Quantifier (p: Pair): Prop :=
    | Is7 (eq: p = fromNat 7)
    | Is8 (eq: p = fromNat 8)
    
    -- Defines the set of pairs that encode an expression.
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
    
    
    instance IsExprEncoding.decidableBin
      (n: Pair)
    :
      Decidable (Bin n)
    :=
      open Bin in
      if h2: n = fromNat 2 then
        isTrue (Is2 h2)
      else if h3: n = fromNat 3 then
        isTrue (Is3 h3)
      else if h4: n = fromNat 4 then
        isTrue (Is4 h4)
      else if h6: n = fromNat 6 then
        isTrue (Is6 h6)
      else
        isFalse (fun h =>
          match h with
          | Is2 is2 => h2 is2
          | Is3 is3 => h3 is3
          | Is4 is4 => h4 is4
          | Is6 is6 => h6 is6)
    
    def IsExprEncoding.decidableQuantifier
      (n: Pair)
    :
      Decidable (Quantifier n)
    :=
      open Quantifier in
      if h7: n = fromNat 7 then
        isTrue (Is7 h7)
      else if h8: n = fromNat 8 then
        isTrue (Is8 h8)
      else
        isFalse (fun h =>
          match h with
          | Is7 is7 => h7 is7
          | Is8 is8 => h8 is8)
    
    
    def IsExprEncoding.nopeZero
      (isExpr: IsExprEncoding zero)
    :
      P
    :=
      nomatch isExpr
    
    def IsExprEncoding.nopeBinQuant
      (isBin: IsExprEncoding.Bin p)
      (isQuant: IsExprEncoding.Quantifier p)
    :
      P
    :=
      False.elim (nomatch isBin, isQuant)
    
    def IsExprEncoding.Bin.nopeVar
      (isBin: IsExprEncoding.Bin zero)
    :
      P
    :=
      nomatch isBin
    
    def IsExprEncoding.Bin.nopeOpZero
      (isBin: IsExprEncoding.Bin (fromNat 1))
    :
      P
    :=
      nomatch isBin
    
    def IsExprEncoding.Bin.nopeCpl
      (isBin: IsExprEncoding.Bin (fromNat 5))
    :
      P
    :=
      nomatch isBin
    
    
    def IsExprEncoding.Quantifier.nopeVar
      (isQuant: IsExprEncoding.Quantifier zero)
    :
      P
    :=
      False.elim (nomatch isQuant)
    
    def IsExprEncoding.Quantifier.nopeOpZero
      (isQuant: IsExprEncoding.Quantifier (fromNat 1))
    :
      P
    :=
      False.elim (nomatch isQuant)
    
    def IsExprEncoding.Quantifier.nopeCpl
      (isQuant: IsExprEncoding.Quantifier (fromNat 5))
    :
      P
    :=
      False.elim (nomatch isQuant)
    
    
    def IsExprEncoding.withIsVar
      (isExpr: IsExprEncoding (pair (fromNat 0) x))
    :
      IsNatEncoding x
    :=
      match isExpr with
      | IsExprEncoding.IsVar isNat => isNat
    
    def IsExprEncoding.withIsZero
      (isExpr: IsExprEncoding (pair (fromNat 1) payload))
    :
      payload = zero
    :=
      match isExpr with
      | IsExprEncoding.IsZero => rfl
    
    structure IsExprEncoding.IsExprAB (a b: Pair): Prop where
      isExprA: IsExprEncoding a
      isExprB: IsExprEncoding b
    
    def IsExprEncoding.withIsBin
      (isExpr: IsExprEncoding (pair n (pair a b)))
      (isBin: IsExprEncoding.Bin n)
    :
      IsExprAB a b
    :=
      match isExpr with
      | IsExprEncoding.IsBin _ isExprA isExprB => {
        isExprA := isExprA
        isExprB := isExprB
      }
      | IsExprEncoding.IsQuantifier isQ _ _ =>
        nopeBinQuant isBin isQ
      | IsExprEncoding.IsVar _ => isBin.nopeVar
    
    def IsExprEncoding.withIsCpl
      (isExpr: IsExprEncoding (pair (fromNat 5) p))
    :
      IsExprEncoding p
    :=
      match isExpr with
      | IsExprEncoding.IsCpl isExpr => isExpr
    
    structure IsExprEncoding.IsQuantifierAB (x body: Pair): Prop where
      isNat: IsNatEncoding x
      isExpr: IsExprEncoding body
    
    def IsExprEncoding.withIsQuantifier
      (isExpr: IsExprEncoding (pair n (pair x body)))
      (isQuant: IsExprEncoding.Quantifier n)
    :
      IsQuantifierAB x body
    :=
      match isExpr with
      | IsExprEncoding.IsQuantifier _ isX isBody => {
        isNat := isX
        isExpr := isBody
      }
      | IsExprEncoding.IsVar _ => isQuant.nopeVar
    
    def IsExprEncoding.withIsQuantifierZero
      {P: Prop}
      (isExpr: IsExprEncoding (pair n zero))
      (isBin: IsExprEncoding.Quantifier n)
    :
      P
    :=
      nomatch isExpr, isBin
    
    def IsExprEncoding.Bin.nopeZeroPayload
      (isBin: IsExprEncoding.Bin n)
      (isExprZero: IsExprEncoding (pair n zero))
    :
      P
    :=
      False.elim
        (match isExprZero with
        | IsExprEncoding.IsZero => isBin.nopeOpZero)
    
    def IsExprEncoding.Quantifier.nopeZeroPayload
      (isQuant: IsExprEncoding.Quantifier n)
      (isExprZero: IsExprEncoding (pair n zero))
    :
      P
    :=
      False.elim
        (match isExprZero with
        | IsExprEncoding.IsVar _ => isQuant.nopeVar)
    
    def IsExprEncoding.nopeNumOutOfBounds
      (neq0: n ≠ (fromNat 0))
      (neq1: n ≠ (fromNat 1))
      (neq5: n ≠ (fromNat 5))
      (notBin: ¬ Bin n)
      (notQuant: ¬ Quantifier n)
      (isExpr: IsExprEncoding (pair n payload))
    :
      P
    :=
      False.elim
        (match isExpr with
        | IsExprEncoding.IsVar _ => neq0 rfl
        | IsExprEncoding.IsZero => neq1 rfl
        | IsExprEncoding.IsBin isBin _ _ => notBin isBin
        | IsExprEncoding.IsCpl _ => neq5 rfl
        | IsExprEncoding.IsQuantifier isQuant _ _ => notQuant isQuant)
    
    
    def IsDefEncoding: Pair → Prop
    | zero => True
    | pair a b => IsExprEncoding a ∧ IsDefEncoding b
    
    def IsDefEncoding.zero: IsDefEncoding zero :=
      trivial
    
    
    def IsPairDictLt: Pair → Prop
    | zero => False
    | pair a b => dictOrder.Lt a b
    
    
    structure IsNatLeFnPair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: b.depth ≤ a.depth
    
    def IsNatLeFn: Pair → Prop
    | zero => False
    | pair a b => IsNatLeFnPair a b
    
    
    structure IsPairOfDepthAB (n p: Pair): Prop where
      isNat: IsNatEncoding n
      eqDepth: n.depth = p.depth
    
    def IsPairOfDepth: Pair → Prop
    | zero => False
    | pair n p => IsPairOfDepthAB n p
    
    def IsPairOfDepth.ofDepth (p: Pair):
      IsPairOfDepth (pair (fromNat p.depth) p)
    := {
      isNat := fromNat.isNatEncoding _
      eqDepth := fromNat.depthEq _
    }
    
    
    structure IsNatLtPair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLt: a.depth < b.depth
    
    def IsNatLt: Pair → Prop
    | zero => False
    | pair a b => IsNatLtPair a b
    
    
    def IsSameDepth: Pair → Prop
    | zero => False
    | pair a b => a.depth = b.depth
    
    
    def IsPairLt: Pair → Prop
    | zero => False
    | pair a b => depthDictOrder.Lt a b
    
    
    structure IsDefEncodingLtPair (a b: Pair): Prop where
      isDefA: IsDefEncoding a
      isDefB: IsDefEncoding b
      isLt: depthDictOrder.Lt a b
    
    def IsDefEncodingLt: Pair → Prop
    | zero => False
    | pair a b => IsDefEncodingLtPair a b
    
    
    structure IsDefEncodingMinDist2ABC (a x b: Pair): Prop where
      ax: depthDictOrder.Lt a x
      xb: depthDictOrder.Lt x b
      isDefX: IsDefEncoding x
    
    structure IsDefEncodingMinDist2Pair (a b: Pair): Prop where
      isDefA: IsDefEncoding a
      isDefB: IsDefEncoding b
      minDist2: ∃ x, IsDefEncodingMinDist2ABC a x b
    
    def IsDefEncodingMinDist2: Pair → Prop
    | zero => False
    | pair a b => IsDefEncodingMinDist2Pair a b
    
    
    structure IsNextDefPair (a b: Pair): Prop where
      isDefA: IsDefEncoding a
      isLeast:
        iIsLeast
          depthDictOrder.le
          (fun p => IsDefEncoding p ∧ depthDictOrder.lt a p)
          b
    
    def IsNextDef: Pair → Prop
    | zero => False
    | pair a b => IsNextDefPair a b
    
    def IsNextDefPair.isDefB
      (isNext: IsNextDefPair a b)
    :
      IsDefEncoding b
    :=
      isNext.isLeast.isMember.left
    
    def IsNextDefPair.isUnique
      (isNextA: IsNextDefPair dl nextA)
      (isNextB: IsNextDefPair dl nextB)
    :
      nextA = nextB
    :=
      iIsLeast.isUnique
        depthDictOrder.toPartialOrder
        isNextA.isLeast
        isNextB.isLeast
    
    def IsNextDefPair.isLt
      (isNextDef: IsNextDefPair a b)
    :
      depthDictOrder.Lt a b
    :=
      isNextDef.isLeast.isMember.right
    
    def IsNextDefPair.nopeLtZero
      (isNextDef: IsNextDefPair dl zero)
    :
      P
    :=
      depthDictOrder.nopeLtZero _ isNextDef.isLt
    
    def IsNextDefPair.injEq
      (isNextA: IsNextDefPair defA next)
      (isNextB: IsNextDefPair defB next)
    :
      defA = defB
    :=
      (depthDictOrder.le_total defA defB).elim
        (fun ab =>
          ab.elim
            (fun lt =>
              let nextLeB :=
                isNextA.isLeast.isLeMember
                  (And.intro isNextB.isDefA lt)
              nextLeB.ltAntisymm isNextB.isLt)
            id)
        (fun ba =>
          ba.elim
            (fun lt =>
              let nextLeA :=
                isNextB.isLeast.isLeMember
                  (And.intro isNextA.isDefA lt)
              nextLeA.ltAntisymm isNextA.isLt)
            Eq.symm)
    
    structure IsNextDefPair.NextDefEncoding (dl: Pair) where
      next: Pair
      isNext: IsNextDefPair dl next
    
    noncomputable def IsNextDefPair.getNext
      (isDef: IsDefEncoding dl)
    :
      NextDefEncoding dl
    :=
      let greaterDefLists: Set Pair :=
        fun p => IsDefEncoding p ∧ depthDictOrder.Lt dl p
      
      let greaterDefList := pair (pair (fromNat 1) zero) dl
      let isDefList: IsDefEncoding greaterDefList :=
        And.intro IsExprEncoding.IsZero isDef
      
      let depthGt: dl.depth < greaterDefList.depth := depthLtR _ _
      
      let isIn: greaterDefList ∈ greaterDefLists :=
        And.intro isDefList (depthDictOrder.Lt.NeqDepth depthGt)
      
      let ⟨next, isLeast⟩ :=
        depthDictOrder.least greaterDefLists isIn
      
      {
        next := next,
        isNext := {
          isDefA := isDef,
          isLeast := isLeast
        }
      }
    
    structure IsNextDefPair.PrevDefEncoding (dl: Pair) where
      prev: Pair
      isPrev: IsNextDefPair prev dl
    
    noncomputable def IsNextDefPair.getPrev.helper
      (isDefDl: IsDefEncoding dl)
      (isDefLb: IsDefEncoding lb)
      (isLt: depthDictOrder.Lt lb dl)
    :
      PrevDefEncoding dl
    :=
      let IsMid mid :=
        IsDefEncoding mid ∧
        depthDictOrder.Lt lb mid ∧
        depthDictOrder.Lt mid dl
      
      if h: ∃ mid, IsMid mid then
        let ⟨mid, isDefMid, isGtLb, isLtDl⟩ := h.unwrap
        
        have :=
          Nat.sub_lt_sub_left
            (depthDictOrder.indexOf.isMono isLt)
            (depthDictOrder.indexOf.isMono isGtLb)
        
        getPrev.helper isDefDl isDefMid isLtDl
      else
        {
          prev := lb,
          isPrev := {
            isDefA := isDefLb,
            isLeast := {
              isMember := And.intro isDefDl isLt,
              isLeMember := fun m isMem =>
                let notLt :=
                  fun isLt => h ⟨m, isMem.left, isMem.right, isLt⟩
                
                @le_of_not_lt _ depthDictOrder _ _ notLt
            }
          }
        }
    termination_by
      depthDictOrder.indexOf dl - depthDictOrder.indexOf lb
    
    noncomputable def IsNextDefPair.getPrev
      (isDef: IsDefEncoding dl)
      (neqZero: dl ≠ zero)
    :
      PrevDefEncoding dl
    :=
      getPrev.helper
        isDef
        IsDefEncoding.zero
        (depthDictOrder.zeroLtOfNeq neqZero)
    
    
    inductive IsNthDefListPair: Pair → Pair → Prop where
    | Zero: IsNthDefListPair zero zero
    | Succ:
        IsNthDefListPair aPred bPred →
        IsNextDefPair bPred b →
        IsNthDefListPair (pair aPred zero) b
    
    def IsNthDefList: Pair → Prop
    | zero => False
    | pair a b => IsNthDefListPair a b
    
    def IsNthDefListPair.isNat
      (isNth: IsNthDefListPair n dl)
    :
      IsNatEncoding n
    :=
      match isNth with
      | Zero => trivial
      | Succ isNthPred _ => And.intro isNthPred.isNat rfl
    
    def IsNthDefListPair.isDefEncoding
      (isNth: IsNthDefListPair n dl)
    :
      IsDefEncoding dl
    :=
      match isNth with
      | Zero => trivial
      | Succ _isNthPred isNextDefPair =>
        isNextDefPair.isDefB
    
    def IsNthDefListPair.isUnique
      (isNthA: IsNthDefListPair n dlA)
      (isNthB: IsNthDefListPair n dlB)
    :
      dlA = dlB
    :=
      match isNthA, isNthB with
      | Zero, Zero => rfl
      | Succ isNthPredA isNextA, Succ isNthPredB isNextB =>
        let ih := isUnique isNthPredA isNthPredB
        
        isNextA.isUnique (ih ▸ isNextB)
      
    def IsNthDefListPair.ltIfLtNat
      (isNth: IsNthDefListPair n dlN)
      (isMth: IsNthDefListPair m dlM)
      (nm: n.depth < m.depth)
    :
      depthDictOrder.Lt dlN dlM
    :=
      match isMth with
      | Zero =>
        False.elim (Nat.not_lt_zero _ nm)
      | Succ isMthPred isNextDefPair =>
        let leMPred := Nat.le_of_lt_succ
          (depth.nat.eqSuccDepthPred
            ((Succ isMthPred isNextDefPair).isNat) ▸ nm)
        
        (Nat.eq_or_lt_of_le leMPred).elim
          (fun eqDepth =>
            let eqN := depth.nat.injEq
              isNth.isNat isMthPred.isNat eqDepth
            
            let eqDlN := isUnique isNth (eqN.symm ▸ isMthPred)
            
            eqDlN ▸ isNextDefPair.isLt)
          (fun lt =>
            let ih := ltIfLtNat isNth isMthPred lt
            
            ih.trans isNextDefPair.isLt)
    
    def IsNthDefListPair.injEq
      (isNthA: IsNthDefListPair nA dl)
      (isNthB: IsNthDefListPair nB dl)
    :
      nA = nB
    :=
      match isNthA, isNthB with
      | Zero, Zero => rfl
      | Succ isNthPredA isNextA, Succ isNthPredB isNextB =>
        let eqNext := isNextA.injEq isNextB
        let eqPred := injEq isNthPredA (eqNext ▸ isNthPredB)
        eqPred ▸ rfl
      
      | Zero, Succ _ isNext => isNext.nopeLtZero
      | Succ _ isNext, Zero => isNext.nopeLtZero
    
    def IsNthDefListPair.injNeq
      (isNthA: IsNthDefListPair nA dlA)
      (isNthB: IsNthDefListPair nB dlB)
      (neq: nA ≠ nB)
    :
      dlA ≠ dlB
    :=
      fun eq => neq (isNthA.injEq (eq.symm ▸ isNthB))
    
    def IsNthDefListPair.emptyIsZeroth:
      IsNthDefListPair zero zero
    :=
      Zero
    
    def IsNthDefListPair.posLengthIfIndexNotZero
      (isNth: IsNthDefListPair n dl)
      -- This variable is falsely marked as unused.
      -- It is used by the match expression to exclude
      -- the case where isNth is `IsNthDefListPair.Zero`.
      (_nNotZero: n ≠ 0)
    :
      0 < dl.arrayLength
    :=
      match isNth, h: dl with
      | Succ _ isNext, zero =>
        depthDictOrder.nopeLtZero _ (h ▸ isNext.isLt)
      | _, pair _ _ => Nat.zero_lt_succ _
    
    structure IsNthDefListPair.NthDlEncoding (n: Nat) where
      dlEncoding: Pair
      isNth: IsNthDefListPair (fromNat n) dlEncoding
    
    noncomputable def IsNthDefListPair.getNthDlEncoding
      (n: Nat)
    :
      IsNthDefListPair.NthDlEncoding n
    :=
      match n with
      | Nat.zero => {
        dlEncoding := zero
        isNth := Zero
      }
      | Nat.succ nPred =>
        let ⟨_nPredDl, isNthPred⟩ := getNthDlEncoding nPred
        let ⟨nPredNext, isNext⟩ :=
          IsNextDefPair.getNext isNthPred.isDefEncoding
        
        {
          dlEncoding := nPredNext
          isNth := Succ isNthPred isNext
        }
    
    def IsNthDefListPair.isSurjective
      (isDef: IsDefEncoding dl)
    :
      ∃ n, IsNthDefListPair n dl
    :=
      have := depthDictOrder.wfRel
      
      if h: dl = zero then
        ⟨0, h.symm ▸ Zero⟩
      else
        let ⟨prevDl, isNext⟩ := IsNextDefPair.getPrev isDef h
        
        have := depthDictOrder.indexOf.isMono isNext.isLt
        let ⟨nPred, isNthPred⟩ := isSurjective isNext.isDefA
        
        Exists.intro
          (pair nPred zero)
          (IsNthDefListPair.Succ isNthPred isNext)
    
    -- Cannot find a way to make Lean use `depthDictOrder.wfRel` :/
    termination_by depthDictOrder.indexOf dl
    
    
    inductive IsIncrVarsExprPair: Pair → Pair → Prop where
    | IsVar:
        IsNatEncoding x →
        IsIncrVarsExprPair (pair zero x) (pair zero (succ x))
    | IsZero:
        IsIncrVarsExprPair (pair (fromNat 1) zero) (pair (fromNat 1) zero)
    | IsBin:
        IsExprEncoding.Bin n →
        IsIncrVarsExprPair a as →
        IsIncrVarsExprPair b bs →
        IsIncrVarsExprPair (pair n (pair a b)) (pair n (pair as bs))
    | IsCpl:
        IsIncrVarsExprPair p ps →
        IsIncrVarsExprPair (pair (fromNat 5) p) (pair (fromNat 5) ps)
    | IsQuantifier:
        IsExprEncoding.Quantifier n →
        IsNatEncoding x →
        IsIncrVarsExprPair b bs →
        IsIncrVarsExprPair
          (pair n (pair x b))
          (pair n (pair (succ x) bs))
    
    def IsIncrVarsExpr: Pair → Prop
    | zero => False
    | pair a b => IsIncrVarsExprPair a b
    
    def IsIncrVarsExprPair.isExprA:
      IsIncrVarsExprPair a b → IsExprEncoding a
    
    | IsVar isNat => IsExprEncoding.IsVar isNat
    | IsZero => IsExprEncoding.IsZero
    | IsBin isBin isIncrA isIncrB =>
      IsExprEncoding.IsBin isBin isIncrA.isExprA isIncrB.isExprA
    
    | IsCpl isIncr => IsExprEncoding.IsCpl isIncr.isExprA
    | IsQuantifier isQuantifier isNat isIncr =>
      IsExprEncoding.IsQuantifier isQuantifier isNat isIncr.isExprA
    
    def IsIncrVarsExprPair.isExprB:
      IsIncrVarsExprPair a b → IsExprEncoding b
    
    | IsVar isNat => IsExprEncoding.IsVar (And.intro isNat rfl)
    | IsZero => IsExprEncoding.IsZero
    | IsBin isBin isIncrA isIncrB =>
      IsExprEncoding.IsBin isBin isIncrA.isExprB isIncrB.isExprB
    
    | IsCpl isIncr => IsExprEncoding.IsCpl isIncr.isExprB
      
    | IsQuantifier isQuantifier isNat isIncr =>
      IsExprEncoding.IsQuantifier
        isQuantifier (And.intro isNat rfl) isIncr.isExprB
    
    def IsIncrVarsExprPair.isUnique
      (isIncrA: IsIncrVarsExprPair expr a)
      (isIncrB: IsIncrVarsExprPair expr b)
    :
      a = b
    :=
      match isIncrA, isIncrB with
      | IsVar isNatA, IsVar isNatB => rfl
      
      | IsZero, IsZero => rfl
      
      | IsBin _sBinA isIncrLeftA isIncrRiteA,
        IsBin isBinB isIncrLeftB isIncrRiteB
      =>
        let eqLeft := isUnique isIncrLeftA isIncrLeftB
        let eqRite := isUnique isIncrRiteA isIncrRiteB
        eqRite ▸ eqLeft ▸ rfl
      
      | IsCpl isIncrA, IsCpl isIncrB =>
        let eqExpr := isUnique isIncrA isIncrB
        eqExpr ▸ rfl
      
      | IsQuantifier _sQuantifierA _sNatA isIncrA,
        IsQuantifier isQuantifierB isNatB isIncrB
      =>
        let eqIncremented := isUnique isIncrA isIncrB
        eqIncremented ▸ rfl
      
      | IsQuantifier isQuantifierA _ _,
        IsBin isBinB isIncrLeftB isIncrRiteB
      =>
        IsExprEncoding.nopeBinQuant isBinB isQuantifierA
      
      | IsQuantifier isQuantifierA _ _,
        IsCpl isIncrB
      =>
        isQuantifierA.nopeCpl
      
      | IsCpl _,
        IsQuantifier isQuantifierB _ _
      =>
        isQuantifierB.nopeCpl
      
      | IsBin isB _ _, IsQuantifier isQ _ _ => nomatch isB, isQ
      | IsQuantifier isQ _ _, IsVar _ => nomatch isQ
    
    
    -- why does this have to be noncomputable?
    -- Seems very much computable to me.
    -- I've proven decidability of the conditions, haven't I?
    noncomputable def IsIncrVarsExprPair.incrVars
      (exprEncoding: Pair)
    :
      Pair
    :=
      match exprEncoding with
      | zero => zero
      | pair n payload =>
        if n = fromNat 0 then
          pair (fromNat 0) (pair payload zero)
        else if n = fromNat 1 then
          pair (fromNat 1) payload
        else if IsExprEncoding.Bin n then
          match payload with
          | zero => zero
          | pair a b =>
            have: depth a < depth (pair n (pair a b)) :=
              (depthLtL a b).trans (depthLtR n (pair a b))
            
            have: depth b < depth (pair n (pair a b)) :=
              (depthLtR a b).trans (depthLtR n (pair a b))
            
            pair n (pair (incrVars a) (incrVars b))
        else if n = fromNat 5 then
          have := depthLtR n payload
          
          pair (fromNat 5) (incrVars payload)
        else if IsExprEncoding.Quantifier n then
          match payload with
          | zero => zero
          | pair x body =>
            have: depth body < depth (pair n (pair x body)) :=
              (depthLtR x body).trans (depthLtR n (pair x body))
            
            pair n (pair (pair x zero) (incrVars body))
        else
          zero
    
    def IsIncrVarsExprPair.incrVars.eq0
      (payload: Pair)
    :
      incrVars (pair (fromNat 0) payload)
        =
      pair (fromNat 0) (pair payload zero)
    :=
      by unfold incrVars; exact if_pos rfl
    
    def IsIncrVarsExprPair.incrVars.eq1
      (payload: Pair)
    :
      incrVars (pair (fromNat 1) payload)
        =
      pair (fromNat 1) payload
    :=
      let neqFN: fromNat 1 ≠ fromNat 0 := fromNat.injNeq (by decide)
      by
        unfold incrVars;
        exact (if_neg neqFN).trans (if_pos rfl)
    
    def IsIncrVarsExprPair.incrVars.eqBin
      (isBin: IsExprEncoding.Bin n)
      (a b: Pair)
    :
      incrVars (pair n (pair a b))
        =
      pair n (pair (incrVars a) (incrVars b))
    :=
      let neq0: n ≠ fromNat 0 :=
        fun eq =>
          let eq: n = zero := eq
          IsExprEncoding.Bin.nopeVar (eq.symm ▸ isBin)
      let neq1: n ≠ fromNat 1 :=
        fun eq =>
          IsExprEncoding.Bin.nopeOpZero (eq ▸ isBin)
      
      (if_neg neq0).trans ((if_neg neq1).trans (if_pos isBin))
    
    def IsIncrVarsExprPair.incrVars.eqCpl
      (payload: Pair)
    :
      incrVars (pair (fromNat 5) payload)
        =
      pair (fromNat 5) (incrVars payload)
    :=
      by
        conv => lhs; unfold incrVars;
        exact rfl
    
    def IsIncrVarsExprPair.incrVars.eqQuant
      (isQuant: IsExprEncoding.Quantifier n)
      (x body: Pair)
    :
      incrVars (pair n (pair x body))
        =
      pair n (pair (pair x zero) (incrVars body))
    :=
      let neq0: n ≠ fromNat 0 :=
        fun eq =>
          let eq: n = zero := eq
          IsExprEncoding.Quantifier.nopeVar (eq.symm ▸ isQuant)
      let neq1: n ≠ fromNat 1 :=
        fun eq =>
          IsExprEncoding.Quantifier.nopeOpZero (eq ▸ isQuant)
      let notBin: ¬ IsExprEncoding.Bin n :=
        fun isBin => IsExprEncoding.nopeBinQuant isBin isQuant
      let neq5: n ≠ fromNat 5 :=
        fun eq =>
          let eq: n = fromNat 5 := eq
          IsExprEncoding.Quantifier.nopeCpl (eq.symm ▸ isQuant)
      
      (if_neg neq0).trans
        ((if_neg neq1).trans
          ((if_neg notBin).trans
            ((if_neg neq5).trans
              (if_pos isQuant))))
    
    def IsIncrVarsExprPair.incrVars.eqQuantZero
      (isQuant: IsExprEncoding.Quantifier n)
    :
      incrVars (pair n zero) = zero
    :=
      let neq0: n ≠ fromNat 0 :=
        fun eq =>
          let eq: n = zero := eq
          IsExprEncoding.Quantifier.nopeVar (eq.symm ▸ isQuant)
      let neq1: n ≠ fromNat 1 :=
        fun eq =>
          IsExprEncoding.Quantifier.nopeOpZero (eq ▸ isQuant)
      let notBin: ¬ IsExprEncoding.Bin n :=
        fun isBin => IsExprEncoding.nopeBinQuant isBin isQuant
      let neq5: n ≠ fromNat 5 :=
        fun eq =>
          let eq: n = fromNat 5 := eq
          IsExprEncoding.Quantifier.nopeCpl (eq.symm ▸ isQuant)
      
      (if_neg neq0).trans
        ((if_neg neq1).trans
          ((if_neg notBin).trans
            ((if_neg neq5).trans
              (if_pos isQuant))))
    
    def IsIncrVarsExprPair.incrVars.eqZeroOutOfBounds
      (neq0: n ≠ fromNat 0)
      (neq1: n ≠ fromNat 1)
      (neq5: n ≠ fromNat 5)
      (notBin: ¬ IsExprEncoding.Bin n)
      (notQuant: ¬ IsExprEncoding.Quantifier n)
      (payload: Pair)
    :
      incrVars (pair n payload) = zero
    :=
      by
        unfold incrVars
        exact
          (if_neg neq0).trans
            ((if_neg neq1).trans
              ((if_neg notBin).trans
                ((if_neg neq5).trans
                  (if_neg notQuant))))
    
    def IsIncrVarsExprPair.fn
      (isExpr: IsExprEncoding expr)
    :
      IsIncrVarsExprPair expr (incrVars expr)
    :=
      match expr with
      | zero => isExpr.nopeZero
      | pair n payload =>
        if h0: n = fromNat 0 then
          h0 ▸
          incrVars.eq0 payload ▸
          IsVar (IsExprEncoding.withIsVar (h0 ▸ isExpr))
        else if h1: n = fromNat 1 then
          h1 ▸
          incrVars.eq1 payload ▸
          (h1 ▸ isExpr).withIsZero ▸
          IsZero
        else if hBin: IsExprEncoding.Bin n then
          match payload with
          | zero => hBin.nopeZeroPayload isExpr
          | pair a b =>
            let ⟨isExprA, isExprB⟩ := isExpr.withIsBin hBin
            
            incrVars.eqBin hBin a b ▸
            IsBin hBin (fn isExprA) (fn isExprB)
        else if h5: n = fromNat 5 then
          h5 ▸
          incrVars.eqCpl payload ▸
          IsCpl (fn (IsExprEncoding.withIsCpl (h5 ▸ isExpr)))
        else if hQuant: IsExprEncoding.Quantifier n then
          match payload with
          | zero => hQuant.nopeZeroPayload isExpr
          | pair x body =>
            let ⟨isNat, isBody⟩ := isExpr.withIsQuantifier hQuant
            
            incrVars.eqQuant hQuant x body ▸
            IsQuantifier hQuant isNat (fn isBody)
        else
          IsExprEncoding.nopeNumOutOfBounds h0 h1 h5 hBin hQuant isExpr
    
    def IsIncrVarsExprPair.incrVars.isExprArg
      (isExpr: IsExprEncoding (incrVars expr))
    :
      IsExprEncoding expr
    :=
      match expr with
      | zero => isExpr.nopeZero
      | pair n payload =>
        if h0: n = fromNat 0 then
          let isExpr := incrVars.eq0 payload ▸ h0 ▸ isExpr
          
          h0 ▸
          IsExprEncoding.IsVar (isExpr.withIsVar).left
        else if h1: n = fromNat 1 then
          let eq: payload = zero :=
            (incrVars.eq1 payload ▸ h1 ▸ isExpr).withIsZero
          
          h1 ▸ eq ▸ IsExprEncoding.IsZero
        else if hBin: IsExprEncoding.Bin n then
          match payload, hBin with
          | pair a b, hBin =>
            let isExpr := (incrVars.eqBin hBin a b) ▸ isExpr
            let ⟨l, r⟩ := isExpr.withIsBin hBin
            
            IsExprEncoding.IsBin hBin (isExprArg l) (isExprArg r)
        else if h5: n = fromNat 5 then
          let isExpr := incrVars.eqCpl payload ▸ h5 ▸ isExpr
          
          h5 ▸
          IsExprEncoding.IsCpl (isExprArg isExpr.withIsCpl)
        else if hQuant: IsExprEncoding.Quantifier n then
          match payload, hQuant with
          | zero, hQuant =>
            let isExpr := incrVars.eqQuantZero hQuant ▸ isExpr
            
            nomatch isExpr
          | pair x body, hQuant =>
            let isExpr := (incrVars.eqQuant hQuant x body) ▸ isExpr
            let ⟨isNat, isBody⟩ := isExpr.withIsQuantifier hQuant
            
            IsExprEncoding.IsQuantifier
              hQuant isNat.left (isExprArg isBody)
        else
          let eq := eqZeroOutOfBounds h0 h1 h5 hBin hQuant payload
          nomatch eq ▸ isExpr
    
    noncomputable def IsIncrVarsExprPair.shiftVars
      (n: Nat)
      (expr: Pair)
    :
      Pair
    :=
      match n with
      | Nat.zero => expr
      | Nat.succ nPred => incrVars (shiftVars nPred expr)
    
    
    inductive IsIncrVarsDefEncodingPair: Pair → Pair → Prop where
    | EmptyDefList: IsIncrVarsDefEncodingPair zero zero
    | NonemptyDefList:
      IsIncrVarsExprPair exprA exprB →
      IsIncrVarsDefEncodingPair defListA defListB →
      IsIncrVarsDefEncodingPair (pair exprA defListA) (pair exprB defListB)
    
    def IsIncrVarsDefEncoding: Pair → Prop
    | zero => False
    | pair a b => IsIncrVarsDefEncodingPair a b
    
    def IsIncrVarsDefEncodingPair.isDefA
      (isInc: IsIncrVarsDefEncodingPair a b)
    :
      IsDefEncoding a
    :=
      match isInc with
      | EmptyDefList => trivial
      | NonemptyDefList isIncr isInc =>
        And.intro isIncr.isExprA isInc.isDefA
    
    def IsIncrVarsDefEncodingPair.isDefB
      (isInc: IsIncrVarsDefEncodingPair a b)
    :
      IsDefEncoding b
    :=
      match isInc with
      | EmptyDefList => trivial
      | NonemptyDefList isIncr isInc =>
        And.intro isIncr.isExprB isInc.isDefB
    
    def IsIncrVarsDefEncodingPair.pairZeroNope
      (isInc: IsIncrVarsDefEncodingPair (pair a b) zero)
    :
      P
    :=
      nomatch isInc
    
    def IsIncrVarsDefEncodingPair.zeroPairNope
      (isInc: IsIncrVarsDefEncodingPair zero (pair a b))
    :
      P
    :=
      nomatch isInc
    
    def IsIncrVarsDefEncodingPair.lengthEq
      (isInc: IsIncrVarsDefEncodingPair a b)
    :
      a.arrayLength = b.arrayLength
    :=
      match isInc with
      | EmptyDefList => rfl
      | NonemptyDefList _isIncr isIncPrev =>
        Pair.arrayLength.eqOfEqTail (lengthEq isIncPrev) _ _
    
    def IsIncrVarsDefEncodingPair.isUnique
      (isIncA: IsIncrVarsDefEncodingPair dl dlIncA)
      (isIncB: IsIncrVarsDefEncodingPair dl dlIncB)
    :
      dlIncA = dlIncB
    :=
      match isIncA, isIncB with
      | EmptyDefList, EmptyDefList => rfl
      | NonemptyDefList isIncrA isIncA,
        NonemptyDefList isIncrB isIncB
      =>
        let eqIncremented := isIncrA.isUnique isIncrB
        let eqPrev := isUnique isIncA isIncB
        
        eqPrev ▸ eqIncremented ▸ rfl
    
    noncomputable def IsIncrVarsDefEncodingPair.incrVars
      (dl: Pair)
    :
      Pair
    :=
      match dl with
      | zero => zero
      | pair head tail =>
        pair
          (IsIncrVarsExprPair.incrVars head)
          (incrVars tail)
    
    def IsIncrVarsDefEncodingPair.incrVars.lengthEq
      (dl: Pair)
    :
      dl.arrayLength = (incrVars dl).arrayLength
    :=
      match dl with
      | zero => rfl
      | pair head tail =>
        let ih := lengthEq tail
        arrayLength.eqOfEqTail ih head tail
    
    def IsIncrVarsDefEncodingPair.fn
      (isDef: IsDefEncoding dl)
    :
      IsIncrVarsDefEncodingPair dl (incrVars dl)
    :=
      match dl with
      | zero => EmptyDefList
      | pair _expr _defList =>
        NonemptyDefList
          (IsIncrVarsExprPair.fn isDef.left)
          (fn isDef.right)
    
    def IsIncrVarsDefEncodingPair.incrVars.isDef
      (isDef: IsDefEncoding dl)
    :
      IsDefEncoding (incrVars dl)
    :=
      (fn isDef).isDefB
    
    def IsIncrVarsDefEncodingPair.incrVars.isDefArg
      (isDef: IsDefEncoding (incrVars dl))
    :
      IsDefEncoding dl
    :=
      match dl with
      | zero => isDef
      | pair _ _ =>
        And.intro
          (IsIncrVarsExprPair.incrVars.isExprArg isDef.left)
          (isDefArg isDef.right)
    
    def IsIncrVarsDefEncodingPair.incrVars.incrAt
      {dl: Pair}
      (eqAt: dl.arrayAt i = some expr)
    :
      (incrVars dl).arrayAt i
        =
      some (IsIncrVarsExprPair.incrVars expr)
    :=
      match i, dl with
      | Nat.zero, pair _ _ =>
        Option.noConfusion eqAt id ▸ rfl
      | Nat.succ _, pair _ tail => @incrAt _ _ tail eqAt
    
    
    inductive IsShiftDefEncodingABC: (a b c: Pair) → Prop
    | ZeroShift:
      IsDefEncoding b →
      IsShiftDefEncodingABC zero b b
    | SuccShift:
      IsShiftDefEncodingABC a b c →
      IsIncrVarsDefEncodingPair c cIncr →
      IsShiftDefEncodingABC (pair a zero) b cIncr
    
    def IsShiftDefEncoding: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair a (pair b c) => IsShiftDefEncodingABC a b c
    
    def IsShiftDefEncodingABC.isNatA
      (isShiftDef: IsShiftDefEncodingABC a b c)
    :
      IsNatEncoding a
    :=
      match isShiftDef with
      | ZeroShift _ => trivial
      | SuccShift isShiftPrev _ =>
        And.intro isShiftPrev.isNatA rfl
    
    def IsShiftDefEncodingABC.isDefB
      (isShiftDef: IsShiftDefEncodingABC a b c)
    :
      IsDefEncoding b
    :=
      match isShiftDef with
      | ZeroShift isDef => isDef
      | SuccShift isShiftPrev _ => isShiftPrev.isDefB
    
    def IsShiftDefEncodingABC.isDefC
      (isShiftDef: IsShiftDefEncodingABC a b c)
    :
      IsDefEncoding c
    :=
      match isShiftDef with
      | ZeroShift isDef => isDef
      | SuccShift _ isInc => isInc.isDefB
    
    def IsShiftDefEncodingABC.lengthEq
      (isShiftDef: IsShiftDefEncodingABC n dlIn dlOut)
    :
      dlIn.arrayLength = dlOut.arrayLength
    :=
      match isShiftDef with
      | ZeroShift isDef => rfl
      | SuccShift isShiftPrev isInc =>
        isShiftPrev.lengthEq.trans isInc.lengthEq
    
    def IsShiftDefEncodingABC.isUnique
      (isShiftDefA: IsShiftDefEncodingABC n dlIn dlOutA)
      (isShiftDefB: IsShiftDefEncodingABC n dlIn dlOutB)
    :
      dlOutA = dlOutB
    :=
      match isShiftDefA, isShiftDefB with
      | ZeroShift _, ZeroShift _ => rfl
      | SuccShift isShiftPrevA isIncA,
        SuccShift isShiftPrevB isIncB
      =>
        let eqPrev := isUnique isShiftPrevA isShiftPrevB
        isIncA.isUnique (eqPrev ▸ isIncB)
    
    noncomputable def IsShiftDefEncodingABC.shiftVars
      (n dl: Pair)
    :
      Pair
    :=
      match n with
      | zero => dl
      | pair nPred _ =>
        IsIncrVarsDefEncodingPair.incrVars (shiftVars nPred dl)
    
    def IsShiftDefEncodingABC.shiftVars.isDef
      (n: Pair)
      (isDef: IsDefEncoding dl)
    :
      IsDefEncoding (shiftVars n dl)
    :=
      match n with
      | zero => isDef
      | pair nPred _ =>
        IsIncrVarsDefEncodingPair.incrVars.isDef
          (shiftVars.isDef nPred isDef)
    
    noncomputable def IsShiftDefEncodingABC.shiftVars.lengthEq
      (n dl: Pair)
    :
      dl.arrayLength = (shiftVars n dl).arrayLength
    :=
      match n with
      | zero => rfl
      | pair nPred _ =>
        lengthEq nPred dl ▸
        IsIncrVarsDefEncodingPair.incrVars.lengthEq _ ▸
        rfl
    
    def IsShiftDefEncodingABC.shiftVars.isDefArg
      (n: Pair)
      (isDef: IsDefEncoding (shiftVars n dl))
    :
      IsDefEncoding dl
    :=
      match n with
      | zero => isDef
      | pair nPred _ =>
          (shiftVars.isDefArg
            nPred
            (IsIncrVarsDefEncodingPair.incrVars.isDefArg isDef))
    
    def IsShiftDefEncodingABC.shiftVars.eqExprShift
      (n: Nat)
      (eqAt: dl.arrayAt i = some expr)
    :
      (shiftVars (fromNat n) dl).arrayAt i
        =
      some (IsIncrVarsExprPair.shiftVars n expr)
    :=
      match n with
      | Nat.zero => eqAt
      | Nat.succ nPred =>
        let ih := eqExprShift nPred eqAt
        
        IsIncrVarsDefEncodingPair.incrVars.incrAt ih
    
    def IsShiftDefEncodingABC.fn
      (isNat: IsNatEncoding n)
      (isDef: IsDefEncoding dl)
    :
      IsShiftDefEncodingABC n dl (shiftVars n dl)
    :=
      match n with
      | zero => ZeroShift isDef
      | pair nPred _ =>
        isNat.right ▸
        SuccShift
          (fn isNat.left isDef)
          (IsIncrVarsDefEncodingPair.fn
            (shiftVars.isDef nPred isDef))
    
    
    structure IsLastExprBasePair (a b: Pair): Prop where
      eq: a = b
      isExprA: IsExprEncoding a
    
    def IsLastExprBasePair.isExprB
      (isB: IsLastExprBasePair a b)
    :
      IsExprEncoding b
    :=
      isB.eq ▸ isB.isExprA
    
    def IsLastExprBase: Pair → Prop
    | zero => False
    | pair zero _ => False
    | pair (pair _ (pair _ _)) _ => False
    | pair (pair a zero) b => IsLastExprBasePair a b
    
    
    inductive IsLastExprPair: Pair → Pair → Prop where
    | LengthOne: IsExprEncoding a → IsLastExprPair (pair a zero) a
    | LengthMore:
      IsExprEncoding a →
      IsDefEncoding b →
      IsLastExprPair b c →
      IsLastExprPair (pair a b) c
    
    def IsLastExpr: Pair → Prop
    | zero => False
    | pair a b => IsLastExprPair a b
    
    def IsLastExprPair.nopeZeroDef
      (isL: IsLastExprPair zero b)
    :
      P
    :=
      nomatch isL
    
    def IsLastExprBase.toIsLastExpr
      (isBase: IsLastExprBase p)
    :
      IsLastExpr p
    :=
      match p with
      | zero => isBase
      | pair zero _ => isBase.elim
      | pair (pair _ (pair _ _)) _ => isBase.elim
      | pair (pair _ zero) _ =>
        isBase.eq ▸ IsLastExprPair.LengthOne isBase.isExprA
    
    def IsLastExprPair.isDefA
      (isL: IsLastExprPair a b)
    :
      IsDefEncoding a
    :=
      match isL with
      | LengthOne isExprB => And.intro isExprB trivial
      | LengthMore isExprHead isDefTail isLast =>
        And.intro isExprHead isDefTail
    
    def IsLastExprPair.isExprB
      (isL: IsLastExprPair a b)
    :
      IsExprEncoding b
    :=
      match isL with
      | LengthOne isExprB => isExprB
      | LengthMore _ _ isLast => isLast.isExprB
    
    def IsLastExprPair.isUnique
      (isLastA: IsLastExprPair dl lastA)
      (isLastB: IsLastExprPair dl lastB)
    :
      lastA = lastB
    :=
      match isLastA, isLastB with
      | LengthOne _, LengthOne _ =>
        rfl
      | LengthMore _ _ isLastA,
        LengthMore _ _ isLastB
      =>
        isLastA.isUnique isLastB
    
    def IsLastExprPair.fn
      (isDef: IsDefEncoding (pair expr dlTail))
    :
      IsLastExprPair (pair expr dlTail) (expr.arrayLast dlTail)
    :=
      match dlTail with
      | zero => LengthOne isDef.left
      | pair _ _ =>
        LengthMore isDef.left isDef.right (fn isDef.right)
    
    
    inductive IsUpToLastPair: Pair → Pair → Prop where
    | LengthOne: IsExprEncoding a → IsUpToLastPair (pair a zero) zero
    | LengthMore:
      IsExprEncoding head →
      IsUpToLastPair tail init →
      IsUpToLastPair (pair head tail) (pair head init)
    
    def IsUpToLast: Pair → Prop
    | zero => False
    | pair a b => IsUpToLastPair a b
    
    def IsUpToLastPair.isDefA
      (isUTL: IsUpToLastPair a b)
    :
      IsDefEncoding a
    :=
      match isUTL with
      | LengthOne isExpr => And.intro isExpr trivial
      | LengthMore isExprHead isUTLTail =>
        And.intro isExprHead (isDefA isUTLTail)
    
    def IsUpToLastPair.isDefB
      (isUTL: IsUpToLastPair a b)
    :
      IsDefEncoding b
    :=
      match isUTL with
      | LengthOne _ => trivial
      | LengthMore isExpr isUTLTail =>
        And.intro isExpr (isDefB isUTLTail)
    
    def IsUpToLastPair.arrayLengthLt
      (isUTL: IsUpToLastPair a b)
    :
      b.arrayLength < a.arrayLength
    :=
      isUTL.rec
        (fun _ => arrayLength.ltTail _ _)
        (fun _ _ isLtTail => arrayLength.ltOfLtTail isLtTail _ _)
    
    def IsUpToLastPair.lengthEq
      (isUpToLast: IsUpToLastPair dlA dlB)
    :
      dlA.arrayLength = Nat.succ dlB.arrayLength
    :=
      match isUpToLast with
      | LengthOne isExpr => rfl
      | @LengthMore head tail upToLast _isExpr isUpToLastPrev =>
        let ih := isUpToLastPrev.lengthEq
        
        (arrayLength.eqSuccTail head tail) ▸
        (arrayLength.eqSuccTail head upToLast) ▸
        congr rfl ih
    
    def IsUpToLastPair.isUnique
      (isUpToLastA: IsUpToLastPair dl dlUpToLastA)
      (isUpToLastB: IsUpToLastPair dl dlUpToLastB)
    :
      dlUpToLastA = dlUpToLastB
    :=
      match isUpToLastA, isUpToLastB with
      | LengthOne _, LengthOne isExprB =>
        rfl
      | LengthMore _ isUpToLastTailA,
        LengthMore _ isUpToLastTailB
      =>
        let eqTail := isUpToLastTailA.isUnique isUpToLastTailB
        
        eqTail ▸ rfl
    
    def IsUpToLastPair.fn
      (isDef: IsDefEncoding (pair expr dlTail))
    :
      IsUpToLastPair (pair expr dlTail) (expr.arrayUpToLast dlTail)
    :=
      match dlTail with
      | zero => LengthOne isDef.left
      | pair _ _ =>
        LengthMore isDef.left (fn isDef.right)
    
    def IsUpToLastPair.preservesElements
      (isUpToLast: IsUpToLastPair dl dlUtl)
      (isAt: dlUtl.arrayAt i = some expr)
    :
      dl.arrayAt i = some expr
    :=
      match isUpToLast, i with
      | LengthOne _, _ => Option.noConfusion isAt
      | LengthMore _ _, Nat.zero =>
        isAt
      | LengthMore _ isUpToLastPrev, Nat.succ _ =>
        -- This variable cannot be inlined. How come, Lean?
        let ih := preservesElements isUpToLastPrev isAt
        ih
    
    
    inductive IsArrayAppendABC: Pair → Pair → Pair → Prop
    | Base: IsDefEncoding dl → IsArrayAppendABC zero dl dl
    | Step:
      IsUpToLastPair dlA dlAUpToLast →
      IsLastExprPair dlA dlALast →
      IsArrayAppendABC dlAUpToLast (pair dlALast dlB) dlRes →
      IsArrayAppendABC dlA dlB dlRes
    
    def IsArrayAppend: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair a (pair b c) => IsArrayAppendABC a b c
    
    def IsArrayAppendABC.isDefA
      (isAppend: IsArrayAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlA
    :=
      match isAppend with
      | Base _ => trivial
      | Step isUpToLast _ _ => isUpToLast.isDefA
    
    def IsArrayAppendABC.isDefB
      (isAppend: IsArrayAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlB
    :=
      -- Lean, get better at automatic termination-showing, pls.
      -- match isAppend with
      -- | Base isDef => isDef
      -- | Step _ _ isAppendPrev => isAppendPrev.isDefB.right
      isAppend.rec id (fun _ _ _ ih => ih.right)
    
    def IsArrayAppendABC.isDefRes
      (isAppend: IsArrayAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlRes
    :=
      isAppend.rec id (fun _ _ _ ih => ih)
    
    structure IsArrayAppendABC.AppendResult
      (a b: Pair)
    where
      dl: Pair
      isAppend: IsArrayAppendABC a b dl
    
    noncomputable def IsArrayAppendABC.append
      (isDefA: IsDefEncoding a)
      (isDefB: IsDefEncoding b)
    :
      AppendResult a b
    :=
      match a with
      | zero => {
        dl := b
        isAppend := IsArrayAppendABC.Base isDefB
      }
      | pair aHead aTail =>
        let isUpToLast := IsUpToLastPair.fn isDefA
        let isLast := IsLastExprPair.fn isDefA
        
        have := arrayUpToLast.lengthLt aHead aTail
        
        let ⟨dl, isAppend⟩ :=
          append
            isUpToLast.isDefB
            (show
              IsDefEncoding (pair (aHead.arrayLast aTail) b)
            from
              And.intro isLast.isExprB isDefB)
        
        {
          dl := dl
          isAppend :=
            IsArrayAppendABC.Step isUpToLast isLast isAppend
        }
    termination_by a.arrayLength
    
    def IsArrayAppendABC.lengthEq
      (isAppend: IsArrayAppendABC a b c)
    :
      a.arrayLength + b.arrayLength = c.arrayLength
    :=
      isAppend.rec
        (fun _isDef => Nat.zero_add _)
        (fun isUtl _ _ ih =>
          isUtl.lengthEq ▸
          (Nat.succ_add_eq_add_succ _ _) ▸
          ih)
    
    def IsArrayAppendABC.isUnique
      (isAppendA: IsArrayAppendABC dl0 dl1 dlA)
      (isAppendB: IsArrayAppendABC dl0 dl1 dlB)
    :
      dlA = dlB
    :=
      match isAppendA, isAppendB with
      | Base _isDefA, Base _isDefB => rfl
      | Step isUpToLastA isLastA isAppendPrevA,
        Step isUpToLastB isLastB isAppendPrevB
      =>
        let eqUpToLast := isUpToLastA.isUnique isUpToLastB
        let eqLast := isLastA.isUnique isLastB
        
        have := isUpToLastA.arrayLengthLt
        
        isAppendPrevA.isUnique
          (eqUpToLast ▸ eqLast ▸ isAppendPrevB)
    termination_by dl0.arrayLength
    
    def IsArrayAppendABC.preservesFinal
      (isAppend: IsArrayAppendABC a b c)
      (isAt: b.arrayAt i = some expr)
    :
      c.arrayAt (a.arrayLength + i) = some expr
    :=
      match isAppend with
      | Base _ => Nat.zero_add _ ▸ isAt
      | @Step _ aUtl aL _ _
          isUpToLast _ isAppendPrev
      =>
        let isAtNew: (pair aL b).arrayAt (i.succ) = some expr := isAt
        
        have := isUpToLast.arrayLengthLt
        
        isUpToLast.lengthEq ▸
        (Nat.succ_add_eq_add_succ _ _) ▸
        preservesFinal isAppendPrev isAtNew
    termination_by a.arrayLength
    
    def IsArrayAppendABC.preservesInitial
      (isAppend: IsArrayAppendABC a b c)
      (isAt: a.arrayAt i = some expr)
    :
      c.arrayAt i = some expr
    :=
      match isAppend with
      | Base isDefB => Option.noConfusion isAt
      | @Step _ aUtl aL _ _
          isUpToLast isLast isAppendPrev
      =>
        match a, h: aUtl.arrayAt i with
        | pair aHead aTail, none =>
          let aUtlEq: aUtl = arrayUpToLast aHead aTail :=
            isUpToLast.isUnique (IsUpToLastPair.fn isUpToLast.isDefA)
          
          let lengthEq :=
            arrayUpToLast.lengthEqOfNone isAt (aUtlEq ▸ h)
          
          let arrayLastEq := arrayLast.eqOfEqAt isAt lengthEq
          let isLastEqArrayLast: aL = arrayLast aHead aTail :=
            isLast.isUnique (IsLastExprPair.fn isLast.isDefA)
          let isLastEq := isLastEqArrayLast.trans arrayLastEq
          
          let isAtNew: (pair aL b).arrayAt 0 = some expr :=
            isLastEq ▸ rfl
          
          let iEq: i = aUtl.arrayLength :=
            Nat.succ_injective
              (isUpToLast.lengthEq ▸ lengthEq.symm)
          
          iEq ▸
          preservesFinal isAppendPrev isAtNew
        
        | a, some exprU =>
          have := isUpToLast.arrayLengthLt
          
          isAt.symm.trans (isUpToLast.preservesElements h) ▸
          isAppendPrev.preservesInitial h
    termination_by a.arrayLength
    
    
    inductive IsArrayLengthPair: Pair → Pair → Prop
    | Zero: IsArrayLengthPair zero zero
    | Succ:
      IsArrayLengthPair dl dlLength →
      (expr: Pair) →
      IsArrayLengthPair (pair expr dl) (pair dlLength zero)
    
    def IsArrayLength: Pair → Prop
    | zero => False
    | pair a b => IsArrayLengthPair a b
    
    def IsArrayLength.lengthIslength
      (arr: Pair)
    :
      IsArrayLengthPair arr (fromNat arr.arrayLength)
    :=
      match arr with
      | zero => IsArrayLengthPair.Zero
      | pair head tail =>
        IsArrayLengthPair.Succ (lengthIslength tail) head
    
    def IsArrayLength.lengthEqFromNat
      (isArrLength: IsArrayLengthPair arr n)
    :
      n = fromNat arr.arrayLength
    :=
      match isArrLength with
      | IsArrayLengthPair.Zero => rfl
      | IsArrayLengthPair.Succ eqTail _head =>
        let ih := lengthEqFromNat eqTail
        arrayLength.eqSuccTail _ _ ▸
        fromNat.fromSuccEq _ ▸
        ih ▸ rfl
    
    
    def IsAppendABC (a b c: Pair): Prop :=
      IsArrayAppendABC
        a
        (IsShiftDefEncodingABC.shiftVars (fromNat a.arrayLength) b)
        c
    
    def IsAppend: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair a (pair b c) => IsAppendABC a b c
    
    def IsAppendABC.isDefA
      (isAppend: IsAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlA
    :=
      IsArrayAppendABC.isDefA isAppend
    
    def IsAppendABC.isDefB
      (isAppend: IsAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlB
    :=
      IsShiftDefEncodingABC.shiftVars.isDefArg
        _ (IsArrayAppendABC.isDefB isAppend)
    
    def IsAppendABC.isDefRes
      (isAppend: IsAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlRes
    :=
      IsArrayAppendABC.isDefRes isAppend
    
    structure IsAppendABC.AppendResult
      (a b: Pair)
    where
      dl: Pair
      isAppend: IsAppendABC a b dl
    
    noncomputable def IsAppendABC.append
      (isDefA: IsDefEncoding a)
      (isDefB: IsDefEncoding b)
    :
      AppendResult a b
    :=
      let isDefBShifted :=
        IsShiftDefEncodingABC.shiftVars.isDef _ isDefB
      
      let ⟨dl, isAppend⟩ :=
        IsArrayAppendABC.append isDefA isDefBShifted
      
      { dl, isAppend }
    
    def IsAppendABC.lengthEq
      (isAppend: IsAppendABC a b c)
    :
      a.arrayLength + b.arrayLength = c.arrayLength
    :=
      IsShiftDefEncodingABC.shiftVars.lengthEq _ b ▸
      IsArrayAppendABC.lengthEq isAppend
    
    def IsAppendABC.isUnique
      (isAppendA: IsAppendABC dl0 dl1 dlA)
      (isAppendB: IsAppendABC dl0 dl1 dlB)
    :
      dlA = dlB
    :=
      IsArrayAppendABC.isUnique isAppendA isAppendB
    
    def IsAppendABC.preservesInitial
      (isAppend: IsAppendABC a b c)
      (isAt: a.arrayAt i = some expr)
    :
      c.arrayAt i = some expr
    :=
      IsArrayAppendABC.preservesInitial isAppend isAt
    
    def IsAppendABC.shiftsFinal
      (isAppend: IsAppendABC a b c)
      (isAt: b.arrayAt i = some expr)
    :
      c.arrayAt (a.arrayLength + i)
        =
      some (IsIncrVarsExprPair.shiftVars a.arrayLength expr)
    :=
      let eqAtShifted :=
        IsShiftDefEncodingABC.shiftVars.eqExprShift
          a.arrayLength
          isAt
      
      IsArrayAppendABC.preservesFinal isAppend eqAtShifted
    
    def IsAppendABC.fromArrayAppend
      (isArrayAppend: IsArrayAppendABC a bShifted c)
      (isShift: IsShiftDefEncodingABC n b bShifted)
      (isLength: IsArrayLengthPair a n)
    :
      IsAppendABC a b c
    :=
      let eq:
        bShifted = IsShiftDefEncodingABC.shiftVars (fromNat a.arrayLength) b
      :=
        IsShiftDefEncodingABC.isUnique
          isShift
          (IsArrayLength.lengthEqFromNat isLength ▸
          IsShiftDefEncodingABC.fn isShift.isNatA isShift.isDefB)
      
      by unfold IsAppendABC; exact eq ▸ isArrayAppend
    
    
    inductive IsEnumUpToPair: Pair → Pair → Prop
    | Base: IsEnumUpToPair zero zero
    | Step:
      IsEnumUpToPair n dlSoFar →
      IsNthDefListPair n dlNth →
      IsAppendABC dlSoFar dlNth dlAppended →
      IsEnumUpToPair (pair n zero) dlAppended
    
    def IsEnumUpTo: Pair → Prop
    | zero => False
    | pair a b => IsEnumUpToPair a b
    
    def IsEnumUpToPair.isNatA
      (isEnumUpTo: IsEnumUpToPair a b)
    :
      IsNatEncoding a
    :=
      isEnumUpTo.rec
        trivial
        (fun _ _ _ isNatN => And.intro isNatN rfl)
    
    def IsEnumUpToPair.isDefB
      (isEnumUpTo: IsEnumUpToPair a b)
    :
      IsDefEncoding b
    :=
      isEnumUpTo.rec
        trivial
        (fun _ _ isAppend _ => isAppend.isDefRes)
    
    def IsEnumUpToPair.isUnique
      (isEnumUpToA: IsEnumUpToPair n a)
      (isEnumUpToB: IsEnumUpToPair n b)
    :
      a = b
    :=
      match isEnumUpToA, isEnumUpToB with
      | Base, Base => rfl
      | Step isEnumUpToPrevA isNthA isAppendA,
        Step isEnumUpToPrevB isNthB isAppendB
      =>
        let eqPrev := isUnique isEnumUpToPrevA isEnumUpToPrevB
        let eqNth := isNthA.isUnique isNthB
        
        IsAppendABC.isUnique
          isAppendA
          (eqPrev.symm ▸ eqNth.symm ▸ isAppendB)
    
    structure IsEnumUpToPair.NthIteration (n: Nat) where
      dlEncoding: Pair
      isEnumUpTo: IsEnumUpToPair (fromNat n) dlEncoding
    
    noncomputable def IsEnumUpToPair.nthIteration
      (n: Nat)
    :
      NthIteration n
    :=
      match n with
      | Nat.zero => {
        dlEncoding := zero
        isEnumUpTo := IsEnumUpToPair.Base
      }
      | Nat.succ nPred =>
        let previousIteration := nthIteration nPred
        let dlToAppend := IsNthDefListPair.getNthDlEncoding nPred
        
        let ⟨dlEncoding, isAppend⟩ :=
          IsAppendABC.append
            previousIteration.isEnumUpTo.isDefB
            dlToAppend.isNth.isDefEncoding
        
        {
          dlEncoding,
          isEnumUpTo :=
            Step
              previousIteration.isEnumUpTo
              dlToAppend.isNth
              isAppend
        }
    
    def IsEnumUpToPair.lengthGrows
      (_nNotZero: n ≠ 0)
      (isNth: IsEnumUpToPair (fromNat n) dlN)
      (isSuccNth: IsEnumUpToPair (fromNat n.succ) dlSuccN)
    :
      dlN.arrayLength < dlSuccN.arrayLength
    :=
      match n, isSuccNth with
      | Nat.succ _nPred,
        Step isEnumUpToN isNthDefN isAppend
      =>
        let dlNEq := isEnumUpToN.isUnique isNth
        
        let nthDlPosLength :=
          isNthDefN.posLengthIfIndexNotZero Pair.noConfusion
        
        dlNEq ▸ Nat.lt_left_of_add
          isAppend.lengthEq nthDlPosLength
    
    def IsEnumUpToPair.nthIteration.lengthGrows
      {n: Nat}
      (nNotZero: n ≠ 0)
    :
      (nthIteration n).dlEncoding.arrayLength
        <
      (nthIteration n.succ).dlEncoding.arrayLength
    :=
      IsEnumUpToPair.lengthGrows
        nNotZero
        (nthIteration n).isEnumUpTo
        (nthIteration n.succ).isEnumUpTo
    
    structure IsEnumUpToPair.DlWithNthDef (n: Nat) where
      dlEncoding: Pair
      i: Nat
      isEnumUpTo: IsEnumUpToPair (fromNat i) dlEncoding
      hasNthDef: n < dlEncoding.arrayLength
    
    noncomputable def IsEnumUpToPair.nthDef.loop
      (n: Nat)
      (i: Nat) -- The loop index.
      (iNotZero: i ≠ 0)
    :
      DlWithNthDef n
    :=
      let ith := nthIteration i
      
      if h: n < ith.dlEncoding.arrayLength then
        {
          dlEncoding := ith.dlEncoding
          i,
          isEnumUpTo := ith.isEnumUpTo
          hasNthDef := h
        }
      else
        have:
          n.succ - (nthIteration i.succ).dlEncoding.arrayLength
            <
          n.succ - (nthIteration i).dlEncoding.arrayLength
        :=
          Nat.sub_lt_sub_left
            (Nat.lt_of_not_ge h)
            (nthIteration.lengthGrows iNotZero)
        
        nthDef.loop n i.succ Nat.noConfusion
    
    termination_by
      n.succ - (nthIteration i).dlEncoding.arrayLength
    
    noncomputable def IsEnumUpToPair.nthDef
      (n: Nat)
    :
      DlWithNthDef n
    :=
      nthDef.loop n 1 Nat.one_ne_zero
    
    def IsEnumUpToPair.preservesPrevious.succ
      (isEnumUpTo: IsEnumUpToPair (fromNat n) dl)
      (isSuccEnumUpTo: IsEnumUpToPair (fromNat n.succ) dlSucc)
      (isAt: dl.arrayAt i = some expr)
    :
      dlSucc.arrayAt i = some expr
    :=
      match isSuccEnumUpTo with
      | Step isEnumUpToPrev _ isAppend =>
        let eqPrev := isEnumUpToPrev.isUnique isEnumUpTo
        
        isAppend.preservesInitial (eqPrev ▸ isAt)
    
    def IsEnumUpToPair.preservesPrevious.directed
      (isEnumUpToA: IsEnumUpToPair (fromNat nA) dlA)
      (isEnumUpToB: IsEnumUpToPair (fromNat nB) dlB)
      (isAt: dlA.arrayAt i = some expr)
      (ab: nA < nB)
    :
      dlB.arrayAt i = some expr
    :=
      match nB with
      | Nat.zero => False.elim (Nat.not_lt_zero _ ab)
      | Nat.succ nBPred =>
        if h: nA = nBPred then
          succ isEnumUpToA (h ▸ isEnumUpToB) isAt
        else
          let ltNBPred: nA < nBPred :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ab) h
          
          let ⟨_, isUpToPred⟩ := IsEnumUpToPair.nthIteration nBPred
          let ih := directed isEnumUpToA isUpToPred isAt ltNBPred
          
          succ isUpToPred isEnumUpToB ih
    
    inductive IsEnumUpToPair.PreservesPrevious
      (dl: Pair)
      (i: Nat)
      (expr: Pair)
    :
      Prop where
    | CaseNone (isNone: dl.arrayAt i = none)
    | CaseSome (isSome: dl.arrayAt i = some expr)
    
    def IsEnumUpToPair.preservesPrevious
      (isEnumUpToA: IsEnumUpToPair (fromNat nA) dlA)
      (isEnumUpToB: IsEnumUpToPair (fromNat nB) dlB)
      (isAt: dlA.arrayAt i = some expr)
    :
      IsEnumUpToPair.PreservesPrevious dlB i expr
    :=
      open PreservesPrevious in
      (Nat.ltTotal nA nB).rec
        (fun ab =>
          CaseSome
            (preservesPrevious.directed
              isEnumUpToA isEnumUpToB isAt ab))
        (fun ba =>
          match h: dlB.arrayAt i with
          | none => CaseNone h
          | some exprB =>
            let isAtB :=
              (preservesPrevious.directed
                isEnumUpToB isEnumUpToA h ba)
            let exprEq: expr = exprB :=
              Option.some.inj (isAt.symm.trans isAtB)
            exprEq ▸ CaseSome h)
        (fun eqN =>
          let eqDl: dlA = dlB :=
            isEnumUpToA.isUnique (eqN ▸ isEnumUpToB)
          
          CaseSome (eqDl ▸ isAt))
    
    def IsEnumUpToPair.isUniqueNthDef
      (n: Nat)
      (dlA: DlWithNthDef n)
      (dlB: DlWithNthDef n)
    :
      dlA.dlEncoding.arrayAt n = dlB.dlEncoding.arrayAt n
    :=
      let notNoneA: dlA.dlEncoding.arrayAt n ≠ none :=
        fun eq => arrayAt.nopeNoneOfWithinBounds dlA.hasNthDef eq
      let notNoneB: dlB.dlEncoding.arrayAt n ≠ none :=
        fun eq => arrayAt.nopeNoneOfWithinBounds dlB.hasNthDef eq
      
      match
        hA: dlA.dlEncoding.arrayAt n,
        hB: dlB.dlEncoding.arrayAt n
      with
        | none, none => rfl
        | none, some _ => False.elim (notNoneA (hA ▸ rfl))
        | some _, none => False.elim (notNoneB (hB ▸ rfl))
        | some _, some _ =>
        (dlA.isEnumUpTo.preservesPrevious dlB.isEnumUpTo hA).rec
          (fun eq => False.elim (notNoneB eq))
          (fun eq => eq.symm.trans hB)
    
    
    structure IsDefListToSetABC (a b c: Pair): Prop where
      isDef: IsDefEncoding a
      isNat: IsNatEncoding b
      eq: a.arrayAt b.depth = c
    
    def IsDefListToSet: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair a (pair b c) => IsDefListToSetABC a b c
    
    def IsDefListToSetABC.isExpr
      (is: IsDefListToSetABC a b c)
    :
      IsExprEncoding c
    :=
      match a, b with
      | pair _head _tail, zero =>
        let eq := Option.noConfusion is.eq id
        eq ▸ is.isDef.left
      | pair _head _tail, pair _bPred zero =>
        isExpr {
          isDef := is.isDef.right
          isNat := is.isNat.left
          eq :=
            arrayAt.tailEq
              (depth.nat.eqSuccDepthPred is.isNat ▸ is.eq)
        }
    
    def IsDefListToSetABC.defNonempty
      (is: IsDefListToSetABC zero b c)
    :
      P
    :=
      let eqNone: none = zero.arrayAt b.depth := rfl
      
      Option.noConfusion (eqNone.trans is.eq)
    
    def IsDefListToSetABC.isUnique
      (isA: IsDefListToSetABC dl n a)
      (isB: IsDefListToSetABC dl n b)
    :
      a = b
    :=
      Option.some.inj (isA.eq.symm.trans isB.eq)
    
    inductive IsTheDefListExprPair
      (exprIndex expr: Pair)
    :
      Prop where
    | intro
      (i: Nat)
      (dl: Pair)
      (isEnumUpTo: IsEnumUpToPair (fromNat i) dl)
      (isAt: IsDefListToSetABC dl exprIndex expr)
    
    def IsTheDefListExpr: Pair → Prop
    | zero => False
    | pair exprIndex expr => IsTheDefListExprPair exprIndex expr
    
    def IsTheDefListExprPair.isExpr
      (is: IsTheDefListExprPair i exprEnc)
    :
      IsExprEncoding exprEnc
    :=
      match is with
      | intro _ _ _ isDefListToSet => isDefListToSet.isExpr
    
    def IsTheDefListExprPair.isUnique
      (isB: IsTheDefListExprPair exprIndex exprA)
      (isA: IsTheDefListExprPair exprIndex exprB)
    :
      exprA = exprB
    :=
      match isA, isB with
      | intro _ _ isUpToA isAtA,
        intro _ _ isUpToB isAtB
      =>
        open IsEnumUpToPair.PreservesPrevious in
        match isUpToA.preservesPrevious isUpToB isAtA.eq with
        | CaseNone isNone =>
          Option.noConfusion (isNone.symm.trans isAtB.eq)
        | CaseSome isSome =>
          Option.some.inj (isAtB.eq.symm.trans isSome)
    
    structure IsTheDefListExprPair.NthExpr (n: Nat) where
      expr: Pair
      isNth: IsTheDefListExprPair (fromNat n) expr
    
    /-
      Returns the nth expression of the internal defintion list.
      See `theExternalDefList` of chapter 7.
    -/
    noncomputable def IsTheDefListExprPair.getNthExpr
      (n: Nat)
    :
      NthExpr n
    :=
      let {
        dlEncoding, i, isEnumUpTo, hasNthDef
      } :=
        IsEnumUpToPair.nthDef n
      
      match h: dlEncoding.arrayAt n with
      | none =>
        False.elim (arrayAt.nopeNoneOfWithinBounds hasNthDef h)
      
      | some expr =>
        let isNth :=
          intro
            i
            dlEncoding
            isEnumUpTo
            {
              isDef := isEnumUpTo.isDefB
              isNat := fromNat.isNatEncoding n
              eq := fromNat.depthEq _ ▸ h
            }
        
        { expr, isNth }
    
    def IsTheDefListExprPair.getNthExpr.eq
      (is: IsTheDefListExpr (pair xEnc exprEnc))
      (eq: xEnc = fromNat x)
    :
      exprEnc = (IsTheDefListExprPair.getNthExpr x).expr
    :=
      let isX := (IsTheDefListExprPair.getNthExpr x).isNth
      
      IsTheDefListExprPair.isUnique (eq ▸ is) isX
    
    structure IsTheDefListExprPair.IndexOfDefList (dl: Pair) where
      i: Nat
      eqAt:
        ∀ (_isSome: dl.arrayAt n = some expr)
        ,
          IsTheDefListExprPair
            (fromNat (i + n))
            (IsIncrVarsExprPair.shiftVars i expr)
    
    /-
      Let `dl` be (an encoding of) a prefix of a definition list
      of length `n`.
      
      This function returns an index `i` such that for every
      `m < n`, `dl.arrayAt m` equals (the encoding of) the `i + m`-th
      expression of the internal definition list (see
      `theExternalDefList` of chapter 7).
    -/
    noncomputable def IsTheDefListExprPair.getIndexOf
      (isDef: IsDefEncoding dl)
    :
      IndexOfDefList dl
    :=
      let ⟨nPair, isNth⟩ :=
        (IsNthDefListPair.isSurjective isDef).unwrap
      
      let nNat := isNth.isNat.toNat
      let nEq: fromNat nNat = nPair := isNth.isNat.toNatFromNatEq
      
      let ⟨dlSoFar, isEnumUpTo⟩ :=
        IsEnumUpToPair.nthIteration nNat
      
      let ⟨dlRes, isAppend⟩ :=
        IsAppendABC.append isEnumUpTo.isDefB isDef
      
      let isEnumUpToNext :=
        IsEnumUpToPair.Step
          (nEq ▸ isEnumUpTo)
          isNth
          isAppend
      
      {
        i := dlSoFar.arrayLength
        eqAt :=
          fun eqSome =>
            let isDlToSet := {
              isDef := isAppend.isDefRes
              isNat := fromNat.isNatEncoding _
              eq :=
                fromNat.depthEq _ ▸
                IsAppendABC.shiftsFinal isAppend eqSome
            }
            
            IsTheDefListExprPair.intro
              nNat.succ
              dlRes
              (fromNat.fromSuccEq _ ▸ nEq ▸ isEnumUpToNext)
              isDlToSet
      }
    
    
    -- IsGetBound boundVarsEncoding xEnc boundValue
    inductive IsGetBound: Pair → Pair → Pair → Prop where
    | InHead
      (isNat: IsNatEncoding hA)
      (hB tail: Pair):
        IsGetBound (pair (pair hA hB) tail) hA hB
    | InTail
      (isGetTail: IsGetBound tail xEnc p)
      (hB: Pair)
      (neq: hA ≠ xEnc):
        IsGetBound (pair (pair hA hB) tail) xEnc p
    
    def IsGetBound.toIsNat
      (isGet: IsGetBound boundVars xEnc p)
    :
      IsNatEncoding xEnc
    :=
      match isGet with
      | InHead isNat _ _ => isNat
      | InTail isGetTail _ _ => toIsNat isGetTail
    
    def IsGetBound.isUnique
      (isGetA: IsGetBound boundVars xEnc a)
      (isGetB: IsGetBound boundVars xEnc b)
    :
      a = b
    :=
      match isGetA, isGetB with
      | InHead _ _ _,
        InHead _ _ _
      =>
        rfl
      | InTail isGetTailA _ _,
        InTail isGetTailB _ _
      =>
        isGetTailA.isUnique isGetTailB
    
    -- Recursing on IsGetBound with `boundVarsEncoding` directly
    -- causes the match expression to error (even when unfolded
    -- once). Seems like a bug to me, but I've already submitted
    -- one issue today, plus a few others some time ago that are
    -- still open, and I'm getting a bit anxious about bothering
    -- them too much lol.
    def IsGetBound.inBoundVarsHelper
      (eq: boundVarsEnc = boundVarsEncoding boundVars)
      (isGet: IsGetBound boundVarsEnc (fromNat x) d)
    :
      ⟨d, x⟩ ∈ boundVars
    :=
      match boundVars, isGet with
      |
        _ :: _, InHead _ _ _ =>
          let eq := Pair.noConfusion eq (Function.const _)
          let ⟨eqXEnc, eqD⟩ := Pair.noConfusion eq And.intro
          (fromNat.injEq eqXEnc) ▸ eqD ▸ List.Mem.head _
      |
        _ :: _, InTail isGetTail _ _ =>
        let ⟨_, eqTail⟩ := Pair.noConfusion eq And.intro
        List.Mem.tail _ (inBoundVarsHelper eqTail isGetTail)
    
    def IsGetBound.inBoundVars
      (isGet:
        IsGetBound (boundVarsEncoding boundVars) (fromNat x) d)
    :
      ⟨d, x⟩ ∈ boundVars
    :=
      inBoundVarsHelper rfl isGet
    
  end uniSet3
end Pair
