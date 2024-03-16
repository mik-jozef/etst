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
    
    
    structure IsNatPairAAOfN (p n: Pair): Prop where
      isNat: IsNatEncoding n
      eq: p = Pair.pair n n
    
    def IsNatPairAA p := ∃ n, IsNatPairAAOfN p n
    def NatPairAA := { p // IsNatPairAA p }
    
    
    structure IsNatLe.Pair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: a.depth ≤ b.depth
    
    def IsNatLe: Pair → Prop
    | zero => False
    | pair a b => IsNatLe.Pair a b
    
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
    | Pair.zero => True
    | Pair.pair a b => IsExprEncoding a ∧ IsDefEncoding b
    
    
    def IsPairDictLt: Pair → Prop
    | zero => False
    | pair a b => dictOrder.Lt a b
    
    
    structure IsNatLeFn.Pair (a b: Pair): Prop where
      isNatA: IsNatEncoding a
      isNatB: IsNatEncoding b
      isLe: b.depth ≤ a.depth
    
    def IsNatLeFn: Pair → Prop
    | zero => False
    | pair a b => IsNatLeFn.Pair a b
    
    
    structure IsPairOfDepthAB (n p: Pair): Prop where
      isNat: IsNatEncoding n
      eqDepth: n.depth = p.depth
    
    def IsPairOfDepth: Pair → Prop
    | zero => False
    | pair n p => IsPairOfDepthAB n p
    
  end uniSet3
end Pair
