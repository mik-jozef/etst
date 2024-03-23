/-
  This file defines descriptions of the sets
  defined by the definition list in `UniDefList`.
-/

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
    
    
    def nat501Neq500: 501 ≠ 500 := by decide
    def nat502Neq500: 502 ≠ 500 := by decide
    def nat502Neq501: 502 ≠ 501 := by decide
    def nat503Neq500: 503 ≠ 500 := by decide
    def nat503Neq501: 503 ≠ 501 := by decide
    def nat503Neq502: 503 ≠ 502 := by decide
    def nat504Neq500: 504 ≠ 500 := by decide
    
    def nat500NeqNat: 500 ≠ 0 := by decide
    def nat500NeqNatLe: 500 ≠ 2 := by decide
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
    
    
    structure IsNatPairAAOfN (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAAOfN p n
    def NatPairAA := { p // IsNatPairAA p }
    
    
    structure IsNatLePair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: a.depth ≤ b.depth
    
    def IsNatLe: Pair → Prop
    | zero => False
    | pair a b => IsNatLePair a b
    
    def IsNatPairAA.toIsNatLe (isAA: IsNatPairAA p): IsNatLe p :=
      let ⟨_n, isAA⟩ := isAA.unwrap
      isAA.eq ▸ {
        isNatA := isAA.isNat,
        isNatB := isAA.isNat
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
    
    
    inductive IsNthDefListPair: Pair → Pair → Prop where
    | IsZeroA: IsNthDefListPair zero zero
    | IsPairA:
        IsNthDefListPair aPred bPred →
        IsNextDefPair bPred b →
        IsNthDefListPair (pair aPred zero) b
    
    def IsNthDefList: Pair → Prop
    | zero => False
    | pair a b => IsNthDefListPair a b
    
    
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
        IsShiftExprPair (pair n (pair x b)) (pair n (pair x bs))
    
    def IsShiftExprEncoding: Pair → Prop
    | zero => False
    | pair a b => IsShiftExprPair a b
    
    structure IsShiftExprPair.IsExpr (a b: Pair): Prop where
      isExpr: IsExprEncoding a
      isExprShifted: IsExprEncoding b
    
    def IsShiftExprPair.toIsExpr: IsShiftExprPair a b → IsExpr a b
    | IsVar isNat => {
      isExpr := IsExprEncoding.IsVar isNat
      isExprShifted := IsExprEncoding.IsVar (And.intro isNat rfl)
    }
    | IsZero => {
      isExpr := IsExprEncoding.IsZero
      isExprShifted := IsExprEncoding.IsZero
    }
    | IsBin isBin isShiftA isShiftB => {
      isExpr :=
        IsExprEncoding.IsBin
          isBin
          isShiftA.toIsExpr.isExpr
          isShiftB.toIsExpr.isExpr
      isExprShifted :=
        IsExprEncoding.IsBin
          isBin
          isShiftA.toIsExpr.isExprShifted
          isShiftB.toIsExpr.isExprShifted
    }
    | IsCpl isShift => {
      isExpr := IsExprEncoding.IsCpl isShift.toIsExpr.isExpr
      isExprShifted := IsExprEncoding.IsCpl isShift.toIsExpr.isExprShifted
    }
    | IsQuantifier isQuantifier isNat isShift => {
      isExpr :=
        IsExprEncoding.IsQuantifier
          isQuantifier
          isNat
          isShift.toIsExpr.isExpr
      isExprShifted :=
        IsExprEncoding.IsQuantifier
          isQuantifier
          isNat
          isShift.toIsExpr.isExprShifted
    }
    
    
    inductive IsIncrementExprsPair: Pair → Pair → Prop where
    | EmptyDefList: IsIncrementExprsPair zero zero
    | NonemptyDefList:
      IsShiftExprPair exprA exprB →
      IsIncrementExprsPair defListA defListB →
      IsIncrementExprsPair (pair exprA defListA) (pair exprB defListB)
    
    def IsIncrementExprs: Pair → Prop
    | zero => False
    | pair a b => IsIncrementExprsPair a b
    
    structure IsIncrementExprsPair.IsDef (a b: Pair): Prop where
      isDef: IsDefEncoding a
      isDefShifted: IsDefEncoding b
    
    def IsIncrementExprsPair.toIsDef:
      IsIncrementExprsPair a b → IsDef a b
    | IsIncrementExprsPair.EmptyDefList => {
        isDef := trivial
        isDefShifted := trivial
      }
    | IsIncrementExprsPair.NonemptyDefList isShift isInc => {
      isDef :=
        And.intro
          isShift.toIsExpr.isExpr
          isInc.toIsDef.isDef
      isDefShifted :=
        And.intro
          isShift.toIsExpr.isExprShifted
          isInc.toIsDef.isDefShifted
    }
    
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
    
    
    structure IsShiftDefPair (a b cA cB: Pair): Prop where
      isExprA: IsExprEncoding a
      isDefB: IsDefEncoding b
      eqA: a = cA
      isShiftedB: IsIncrementExprsPair b cB
    
    def IsShiftDefEncoding: Pair → Prop
    | zero => False
    | pair _ zero => False
    | pair _ (pair _ zero) => False
    | pair a (pair b (pair cA cB)) => IsShiftDefPair a b cA cB
    
    
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
    
  end uniSet3
end Pair
