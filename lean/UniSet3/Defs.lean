/-
  This file defines descriptions of the sets
  defined by the definition list in `UniDefList`.
-/

import UniDefList
import Wfm
import PairDictOrderInstance
import PairDepthDictOrder
import UniSet3.DefListToEncoding


namespace Pair
  namespace uniSet3
    open Expr
    open PairExpr
    open uniDefList
    
    
    def Ins := InsWfm pairSalgebra uniDefList.defList
    def Inw := InwWfm pairSalgebra uniDefList.defList
    
    
    def nat501Neq500: 501 ≠ 500 := by decide
    def nat502Neq500: 502 ≠ 500 := by decide
    def nat502Neq501: 502 ≠ 501 := by decide
    def nat503Neq500: 503 ≠ 500 := by decide
    def nat503Neq501: 503 ≠ 501 := by decide
    def nat503Neq502: 503 ≠ 502 := by decide
    def nat504Neq500: 504 ≠ 500 := by decide
    def nat504Neq501: 504 ≠ 501 := by decide
    def nat505Neq500: 505 ≠ 500 := by decide
    
    def nat500NeqNat: 500 ≠ 0 := by decide
    def nat500NeqNatLe: 500 ≠ 2 := by decide
    def nat500NeqExprEncoding: 500 ≠ 7 := by decide
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
    
    
    structure IsNatPairAAPair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      eq: a = b
    
    def IsNatPairAA: Pair → Prop
    | zero => False
    | pair a b => IsNatPairAAPair a b
    
    
    structure IsNatLePair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: a.depth ≤ b.depth
    
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
      match isExpr with.
    
    def IsExprEncoding.nopeBinQuant
      (isBin: IsExprEncoding.Bin p)
      (isQuant: IsExprEncoding.Quantifier p)
    :
      P
    :=
      False.elim (match isBin, isQuant with.)
    
    def IsExprEncoding.Bin.nopeVar
      (isBin: IsExprEncoding.Bin zero)
    :
      P
    :=
      match isBin with.
    
    def IsExprEncoding.Bin.nopeOpZero
      (isBin: IsExprEncoding.Bin (fromNat 1))
    :
      P
    :=
      match isBin with.
    
    def IsExprEncoding.Bin.nopeCpl
      (isBin: IsExprEncoding.Bin (fromNat 5))
    :
      P
    :=
      match isBin with.
    
    
    def IsExprEncoding.Quantifier.nopeVar
      (isQuant: IsExprEncoding.Quantifier zero)
    :
      P
    :=
      False.elim (match isQuant with.)
    
    def IsExprEncoding.Quantifier.nopeOpZero
      (isQuant: IsExprEncoding.Quantifier (fromNat 1))
    :
      P
    :=
      False.elim (match isQuant with.)
    
    def IsExprEncoding.Quantifier.nopeCpl
      (isQuant: IsExprEncoding.Quantifier (fromNat 5))
    :
      P
    :=
      False.elim (match isQuant with.)
    
    
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
        | IsExprEncoding.IsVar _ => (neq0 rfl).elim
        | IsExprEncoding.IsZero => (neq1 rfl).elim
        | IsExprEncoding.IsBin isBin _ _ => notBin isBin
        | IsExprEncoding.IsCpl _ => (neq5 rfl).elim
        | IsExprEncoding.IsQuantifier isQuant _ _ => notQuant isQuant)
    
    
    def IsDefEncoding: Pair → Prop
    | zero => True
    | pair a b => IsExprEncoding a ∧ IsDefEncoding b
    
    
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
          depthDictOrder.toPartialOrder
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
      iIsLeast.isUnique isNextA.isLeast isNextB.isLeast
    
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
      sorry
    
    structure IsNextDefPair.NextDefEncoding (dl: Pair) where
      next: Pair
      isNext: IsNextDefPair dl next
    
    def IsNextDefPair.getNext
      (isDef: IsDefEncoding dl)
    :
      NextDefEncoding dl
    :=
      sorry
    
    
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
    
    def IsNthDefListPair.getNthDlEncoding
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
    
    
    inductive IsShiftExprPair: Pair → Pair → Prop where
    | IsVar:
        IsNatEncoding x →
        IsShiftExprPair (pair zero x) (pair zero (succ x))
    | IsZero:
        IsShiftExprPair (pair (fromNat 1) zero) (pair (fromNat 1) zero)
    | IsBin:
        IsExprEncoding.Bin n →
        IsShiftExprPair a as →
        IsShiftExprPair b bs →
        IsShiftExprPair (pair n (pair a b)) (pair n (pair as bs))
    | IsCpl:
        IsShiftExprPair p ps →
        IsShiftExprPair (pair (fromNat 5) p) (pair (fromNat 5) ps)
    | IsQuantifier:
        IsExprEncoding.Quantifier n →
        IsNatEncoding x →
        IsShiftExprPair b bs →
        IsShiftExprPair
          (pair n (pair x b))
          (pair n (pair (succ x) bs))
    
    def IsShiftExprEncoding: Pair → Prop
    | zero => False
    | pair a b => IsShiftExprPair a b
    
    def IsShiftExprPair.isExprA:
      IsShiftExprPair a b → IsExprEncoding a
    
    | IsVar isNat => IsExprEncoding.IsVar isNat
    | IsZero => IsExprEncoding.IsZero
    | IsBin isBin isShiftA isShiftB =>
      IsExprEncoding.IsBin isBin isShiftA.isExprA isShiftB.isExprA
    
    | IsCpl isShift => IsExprEncoding.IsCpl isShift.isExprA
    | IsQuantifier isQuantifier isNat isShift =>
      IsExprEncoding.IsQuantifier isQuantifier isNat isShift.isExprA
    
    def IsShiftExprPair.isExprB:
      IsShiftExprPair a b → IsExprEncoding b
    
    | IsVar isNat => IsExprEncoding.IsVar (And.intro isNat rfl)
    | IsZero => IsExprEncoding.IsZero
    | IsBin isBin isShiftA isShiftB =>
      IsExprEncoding.IsBin isBin isShiftA.isExprB isShiftB.isExprB
    
    | IsCpl isShift => IsExprEncoding.IsCpl isShift.isExprB
      
    | IsQuantifier isQuantifier isNat isShift =>
      IsExprEncoding.IsQuantifier
        isQuantifier (And.intro isNat rfl) isShift.isExprB
    
    def IsShiftExprPair.isUnique
      (isShiftA: IsShiftExprPair expr shiftedA)
      (isShiftB: IsShiftExprPair expr shiftedB)
    :
      shiftedA = shiftedB
    :=
      match isShiftA, isShiftB with
      | IsVar isNatA, IsVar isNatB => rfl
      
      | IsZero, IsZero => rfl
      
      | IsBin _sBinA isShiftLeftA isShiftRiteA,
        IsBin isBinB isShiftLeftB isShiftRiteB
      =>
        let eqLeft := isUnique isShiftLeftA isShiftLeftB
        let eqRite := isUnique isShiftRiteA isShiftRiteB
        eqRite ▸ eqLeft ▸ rfl
      
      | IsCpl isShiftA, IsCpl isShiftB =>
        let eqExpr := isUnique isShiftA isShiftB
        eqExpr ▸ rfl
      
      | IsQuantifier _sQuantifierA _sNatA isShiftA,
        IsQuantifier isQuantifierB isNatB isShiftB
      =>
        let eqShift := isUnique isShiftA isShiftB
        eqShift ▸ rfl
      
      | IsQuantifier isQuantifierA _ _,
        IsBin isBinB isShiftLeftB isShiftRiteB
      =>
        IsExprEncoding.nopeBinQuant isBinB isQuantifierA
      
      | IsQuantifier isQuantifierA _ _,
        IsCpl isShiftB
      =>
        isQuantifierA.nopeCpl
      
      | IsBin isBinA _ _,
        IsQuantifier isQuantifierB isNatB isShiftB
      =>
        IsExprEncoding.nopeBinQuant isBinA isQuantifierB
      
      | IsBin isBinA _ _,
        IsCpl isShiftB
      =>
        isBinA.nopeCpl
    
    -- why does this have to be noncomputable?
    -- Seems very much computable to me.
    -- I've proven decidability of the conditions, haven't I?
    noncomputable def IsShiftExprPair.shiftExpr
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
          pair (fromNat 1) zero
        else if IsExprEncoding.Bin n then
          match payload with
          | zero => zero
          | pair a b =>
            have: depth a < depth (pair n (pair a b)) :=
              (depthLtL a b).trans (depthLtR n (pair a b))
            
            have: depth b < depth (pair n (pair a b)) :=
              (depthLtR a b).trans (depthLtR n (pair a b))
            
            pair n (pair (shiftExpr a) (shiftExpr b))
        else if n = fromNat 5 then
          have := depthLtR n payload
          
          pair (fromNat 5) (shiftExpr payload)
        else if IsExprEncoding.Quantifier n then
          match payload with
          | zero => zero
          | pair x body =>
            have: depth body < depth (pair n (pair x body)) :=
              (depthLtR x body).trans (depthLtR n (pair x body))
            
            pair n (pair (pair x zero) (shiftExpr body))
        else
          zero
    
    def IsShiftExprPair.shiftExpr.eq0
      (payload: Pair)
    :
      shiftExpr (pair (fromNat 0) payload)
        =
      pair (fromNat 0) (pair payload zero)
    :=
      by unfold shiftExpr; exact if_pos rfl
    
    def IsShiftExprPair.shiftExpr.eq1
      (payload: Pair)
    :
      shiftExpr (pair (fromNat 1) payload)
        =
      pair (fromNat 1) zero
    :=
      let neqFN: fromNat 1 ≠ fromNat 0 := fromNat.injNeq (by decide)
      by
        unfold shiftExpr;
        exact (if_neg neqFN).trans (if_pos rfl)
    
    def IsShiftExprPair.shiftExpr.eqBin
      (isBin: IsExprEncoding.Bin n)
      (a b: Pair)
    :
      shiftExpr (pair n (pair a b))
        =
      pair n (pair (shiftExpr a) (shiftExpr b))
    :=
      let neq0: n ≠ fromNat 0 :=
        fun eq =>
          let eq: n = zero := eq
          IsExprEncoding.Bin.nopeVar (eq.symm ▸ isBin)
      let neq1: n ≠ fromNat 1 :=
        fun eq =>
          IsExprEncoding.Bin.nopeOpZero (eq ▸ isBin)
      
      (if_neg neq0).trans ((if_neg neq1).trans (if_pos isBin))
    
    def IsShiftExprPair.shiftExpr.eqCpl
      (payload: Pair)
    :
      shiftExpr (pair (fromNat 5) payload)
        =
      pair (fromNat 5) (shiftExpr payload)
    :=
      -- What arcane magic is this?
      by conv => lhs; unfold shiftExpr;
    
    def IsShiftExprPair.shiftExpr.eqQuant
      (isQuant: IsExprEncoding.Quantifier n)
      (x body: Pair)
    :
      shiftExpr (pair n (pair x body))
        =
      pair n (pair (pair x zero) (shiftExpr body))
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
    
    
    def IsShiftExprPair.fn
      (isExpr: IsExprEncoding expr)
    :
      IsShiftExprPair expr (shiftExpr expr)
    :=
      match expr with
      | zero => isExpr.nopeZero
      | pair n payload =>
        if h0: n = fromNat 0 then
          h0 ▸
          shiftExpr.eq0 payload ▸
          IsVar (IsExprEncoding.withIsVar (h0 ▸ isExpr))
        else if h1: n = fromNat 1 then
          h1 ▸
          shiftExpr.eq1 payload ▸
          IsExprEncoding.withIsZero (h1 ▸ isExpr) ▸
          IsZero
        else if hBin: IsExprEncoding.Bin n then
          match payload with
          | zero => hBin.nopeZeroPayload isExpr
          | pair a b =>
            let ⟨isExprA, isExprB⟩ := isExpr.withIsBin hBin
            
            shiftExpr.eqBin hBin a b ▸
            IsBin hBin (fn isExprA) (fn isExprB)
        else if h5: n = fromNat 5 then
          h5 ▸
          shiftExpr.eqCpl payload ▸
          IsCpl (fn (IsExprEncoding.withIsCpl (h5 ▸ isExpr)))
        else if hQuant: IsExprEncoding.Quantifier n then
          match payload with
          | zero => hQuant.nopeZeroPayload isExpr
          | pair x body =>
            let ⟨isNat, isBody⟩ := isExpr.withIsQuantifier hQuant
            
            shiftExpr.eqQuant hQuant x body ▸
            IsQuantifier hQuant isNat (fn isBody)
        else
          IsExprEncoding.nopeNumOutOfBounds h0 h1 h5 hBin hQuant isExpr
    
    
    inductive IsIncrementExprsPair: Pair → Pair → Prop where
    | EmptyDefList: IsIncrementExprsPair zero zero
    | NonemptyDefList:
      IsShiftExprPair exprA exprB →
      IsIncrementExprsPair defListA defListB →
      IsIncrementExprsPair (pair exprA defListA) (pair exprB defListB)
    
    def IsIncrementExprs: Pair → Prop
    | zero => False
    | pair a b => IsIncrementExprsPair a b
    
    def IsIncrementExprsPair.isDefA
      (isInc: IsIncrementExprsPair a b)
    :
      IsDefEncoding a
    :=
      match isInc with
      | EmptyDefList => trivial
      | NonemptyDefList isShift isInc =>
        And.intro isShift.isExprA isInc.isDefA
    
    def IsIncrementExprsPair.isDefB
      (isInc: IsIncrementExprsPair a b)
    :
      IsDefEncoding b
    :=
      match isInc with
      | EmptyDefList => trivial
      | NonemptyDefList isShift isInc =>
        And.intro isShift.isExprB isInc.isDefB
    
    def IsIncrementExprsPair.pairZeroNope
      (isInc: IsIncrementExprsPair (pair a b) zero)
    :
      P
    :=
      match isInc with.
    
    def IsIncrementExprsPair.zeroPairNope
      (isInc: IsIncrementExprsPair zero (pair a b))
    :
      P
    :=
      match isInc with.
    
    def IsIncrementExprsPair.lengthEq
      (isInc: IsIncrementExprsPair a b)
    :
      a.arrayLength = b.arrayLength
    :=
      match isInc with
      | EmptyDefList => rfl
      | NonemptyDefList _isShift isIncPrev =>
        Pair.arrayLength.eqOfEqTail (lengthEq isIncPrev) _ _
    
    def IsIncrementExprsPair.isUnique
      (isIncA: IsIncrementExprsPair dl dlIncA)
      (isIncB: IsIncrementExprsPair dl dlIncB)
    :
      dlIncA = dlIncB
    :=
      match isIncA, isIncB with
      | EmptyDefList, EmptyDefList => rfl
      | NonemptyDefList isShiftA isIncA,
        NonemptyDefList isShiftB isIncB
      =>
        let eqShift := isShiftA.isUnique isShiftB
        let eqPrev := isUnique isIncA isIncB
        
        eqPrev ▸ eqShift ▸ rfl
    
    noncomputable def IsIncrementExprsPair.shiftExprs
      (isDef: IsDefEncoding dl)
    :
      Pair
    :=
      match dl with
      | zero => zero
      | pair a _ =>
        pair
          (IsShiftExprPair.shiftExpr a)
          (shiftExprs isDef.right)
    
    def IsIncrementExprsPair.fn
      (isDef: IsDefEncoding dl)
    :
      IsIncrementExprsPair dl (shiftExprs isDef)
    :=
      match dl with
      | zero => EmptyDefList
      | pair _expr _defList =>
        NonemptyDefList
          (IsShiftExprPair.fn isDef.left)
          (fn isDef.right)
    
    def IsIncrementExprsPair.shiftedIsDef
      (isDef: IsDefEncoding dl)
    :
      IsDefEncoding (shiftExprs isDef)
    :=
      (fn isDef).isDefB
    
    
    /-
      ```
        shift(a: Expr, b: DefList)
          = c
          = pair cA cB
          = pair a (incrementExprs b)
          = [ a, ...(incrementExprs b) ]
      ```
    -/
    structure IsShiftDefPair (a b cHead cTail: Pair): Prop where
      isExprA: IsExprEncoding a
      isDefB: IsDefEncoding b
      eqA: a = cHead
      isIncrementedB: IsIncrementExprsPair b cTail
    
    def IsShiftDefEncoding: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair _ (pair _ zero) => False
    | pair a (pair b (pair cA cB)) => IsShiftDefPair a b cA cB
    
    def IsShiftDefPair.isDefC
      (isShiftDef: IsShiftDefPair a b cHead cTail)
    :
      IsDefEncoding (pair cHead cTail)
    :=
      And.intro
        (isShiftDef.eqA ▸ isShiftDef.isExprA)
        isShiftDef.isIncrementedB.isDefB
    
    def IsShiftDefPair.lengthEqTail
      (isShiftDefPair: IsShiftDefPair expr dl _expr dlShifted)
    :
      dl.arrayLength = dlShifted.arrayLength
    :=
      isShiftDefPair.isIncrementedB.lengthEq
    
    def IsShiftDefPair.lengthEqWhole
      (isShiftDefPair: IsShiftDefPair expr dl _expr dlShifted)
    :
      dl.arrayLength.succ = (pair expr dlShifted).arrayLength
    :=
      (arrayLength.eqSuccTail expr dl).symm.trans
        (arrayLength.eqOfEqTail (lengthEqTail isShiftDefPair) _ _)
    
    def IsShiftDefPair.isUniqueHead
      (isShiftDefA: IsShiftDefPair a b cHeadA cTailA)
      (isShiftDefB: IsShiftDefPair a b cHeadB cTailB)
    :
      cHeadA = cHeadB
    :=
      isShiftDefA.eqA.symm.trans isShiftDefB.eqA
    
    def IsShiftDefPair.isUniqueTail
      (isShiftDefA: IsShiftDefPair a b cHeadA cTailA)
      (isShiftDefB: IsShiftDefPair a b cHeadB cTailB)
    :
      cTailA = cTailB
    :=
      isShiftDefA.isIncrementedB.isUnique isShiftDefB.isIncrementedB
    
    def IsShiftDefPair.fn
      (isExpr: IsExprEncoding expr)
      (isDef: IsDefEncoding dl)
    :
      IsShiftDefPair expr dl expr
        (IsIncrementExprsPair.shiftExprs isDef)
    :=
      {
        isExprA := isExpr
        isDefB := isDef
        eqA := rfl
        isIncrementedB := IsIncrementExprsPair.fn isDef
      }
    
    
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
      match isL with.
    
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
    
    
    inductive IsAppendABC: Pair → Pair → Pair → Prop
    | Base: IsDefEncoding dl → IsAppendABC zero dl dl
    | Step:
      IsUpToLastPair dlA dlAUpToLast →
      IsLastExprPair dlA dlALast →
      IsShiftDefPair dlALast dlB dlALast dlBIncremented →
      IsAppendABC dlAUpToLast (pair dlALast dlBIncremented) dlRes →
      IsAppendABC dlA dlB dlRes
    
    def IsAppend: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair a (pair b c) => IsAppendABC a b c
    
    def IsAppendABC.isDefA
      (isAppend: IsAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlA
    :=
      match isAppend with
      | Base _ => trivial
      | Step isUpToLast _ _ _ => isUpToLast.isDefA
    
    def IsAppendABC.isDefB
      (isAppend: IsAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlB
    :=
      match isAppend with
      | Base isDef => isDef
      | Step _ _ isShiftDef _ => isShiftDef.isDefB
    
    def IsAppendABC.isDefRes
      (isAppend: IsAppendABC dlA dlB dlRes)
    :
      IsDefEncoding dlRes
    :=
      -- Lean, get better at automatic termination-showing, pls.
      -- match isAppend with
      -- | Base isDef => isDef
      -- | Step _ _ _ isAppendPrev => isAppendPrev.isDefRes
      isAppend.rec id (fun _ _ _ _ => id)
    
    structure IsAppendABC.AppendResult
      (isDefA: IsDefEncoding a)
      (isDefB: IsDefEncoding b)
    where
      dl: Pair
      isAppend: IsAppendABC a b dl
    
    noncomputable def IsAppendABC.append
      (isDefA: IsDefEncoding a)
      (isDefB: IsDefEncoding b)
    :
      AppendResult isDefA isDefB
    :=
      match a with
      | zero => {
        dl := b
        isAppend := IsAppendABC.Base isDefB
      }
      | pair aHead aTail =>
        let isUpToLast := IsUpToLastPair.fn isDefA
        let isLast := IsLastExprPair.fn isDefA
        let isShiftDef := IsShiftDefPair.fn isLast.isExprB isDefB
        
        have := arrayUpToLast.lengthLt aHead aTail
        
        let ⟨dl, isAppend⟩ :=
          append isUpToLast.isDefB isShiftDef.isDefC
        
        {
          dl := dl
          isAppend :=
            IsAppendABC.Step isUpToLast isLast isShiftDef isAppend
        }
    termination_by IsAppendABC.append isDefA isDefB => a.arrayLength
    
    def IsAppendABC.lengthEq
      (isAppend: IsAppendABC a b c)
    :
      a.arrayLength + b.arrayLength = c.arrayLength
    :=
      -- Lean cannot prove termination automatically here:
      -- match isAppend with
      -- | Base _ => Nat.zero_add _
      -- | Step isUpToLast isLast isShift isAppendPrev =>
        
      --   isUpToLast.lengthEq ▸
      --   isShift.lengthEqTail ▸
      --   isAppendPrev.lengthEq ▸
      --   sorry
      
      isAppend.rec
        (fun _isDef => Nat.zero_add _)
        (fun isUpToLast _isLast isShift _isAppendPrev ih =>
          isUpToLast.lengthEq ▸
          isShift.lengthEqTail ▸
          ih ▸
          (Nat.succ_add_eq_succ_add _ _) ▸
          rfl)
    
    def IsAppendABC.isUnique
      (isAppendA: IsAppendABC dl0 dl1 dlA)
      (isAppendB: IsAppendABC dl0 dl1 dlB)
    :
      dlA = dlB
    :=
      -- Lean, you got issues with automatic termination-showing.
      
      match isAppendA, isAppendB with
      | Base _isDefA, Base _isDefB => rfl
      | Step isUpToLastA isLastA isShiftA isAppendPrevA,
        Step isUpToLastB isLastB isShiftB isAppendPrevB
      =>
        let eqUpToLast := isUpToLastA.isUnique isUpToLastB
        let eqLast := isLastA.isUnique isLastB
        
        let eqShift :=
          isShiftA.isUniqueTail (eqLast.symm ▸ isShiftB)
        
        have := isUpToLastA.arrayLengthLt
        
        isAppendPrevA.isUnique
          (eqUpToLast ▸ eqLast ▸ eqShift ▸ isAppendPrevB)
    
    termination_by IsAppendABC.isUnique a b => dl0.arrayLength
    
    
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
      -- What's your problem, Lean? What universes?
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
      (nNotZero: n ≠ 0)
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
        
        dlNEq ▸ Nat.lt_add_rite isAppend.lengthEq nthDlPosLength
    
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
    
    noncomputable def IsEnumUpToPair.exNthDef.loop
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
        
        exNthDef.loop n i.succ Nat.noConfusion
    
    termination_by IsEnumUpToPair.exNthDef.loop n i iNotZero =>
      n.succ - (nthIteration i).dlEncoding.arrayLength
    
    noncomputable def IsEnumUpToPair.exNthDef
      (n: Nat)
    :
      DlWithNthDef n
    :=
      exNthDef.loop n 1 Nat.one_ne_zero
    
    structure IsDefListToSetABC (a b c: Pair): Prop where
      isDef: IsDefEncoding a
      isNat: IsNatEncoding b
      eq: a.arrayAt b.depth = c
    
    def IsDefListToSet: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair a (pair b c) => IsDefListToSetABC a b c
    
    def IsDefListToSetABC.defNonempty
      (is: IsDefListToSetABC zero b c)
    :
      P
    :=
      let eqNone: none = zero.arrayAt b.depth := rfl
      
      Option.noConfusion (eqNone.trans is.eq)
    
  end uniSet3
end Pair
