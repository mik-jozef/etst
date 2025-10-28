import Etst.WFC.Utils.PairExprDecideEq
import Etst.Subtyping.Syntax.FiniteDefList
import Etst.Subtyping.ProofSystem

namespace Etst
open PairDl
open PairDl.SubsetStx

set_option pp.raw true

pairDefList TestDl
  s3 Nat := null | (Nat, null)
  
  s3 Even := null | ((Even, null), null)
  s3 Odd := (Even, null)
  
  s3 EvenMut := null | (OddMut, null)
  s3 OddMut := (EvenMut, null)
  
  s3 EvenNeg := !(EvenNeg, null)
  
  s3 succ := Ex x: Nat, (x, (x, null))
  
  s3 add :=
    | (Ex n: Nat, (n, (null, n)))
    | (Ex a: Nat,
      Ex b: Nat,
        (a, (succ b, succ (add a b))))
  
  s3 mul :=
    | (Ex n: Nat, (n, (null, null)))
    | (Ex a: Nat,
      Ex b: Nat,
        (a, (succ b, add (mul a b) b)))
  
  s3 Prime :=
    & !succ null
    & (Ex n: Nat,
      All m: Nat,
        mul m Nat & n then (?some m & succ null) | (?some m & n) then n)
  
  s3 InList :=
    Ex v,
    Ex tail,
    | (v, ((v, tail), Any))
    | (Ex h,
      InList v tail then (v, (h, tail)))
  
  s3 PrimesInf := All list, Ex p: Prime, !InList p list
pairDefList.

local macro "s3(" e:s3_pair_expr ")" : term => `(s3(TestDl, $e))


def DecEq
  (a b: SingleLanePairExpr)
:
  Prop
:=
  ∀ (neq: a ≠ b), PairExpr.decidePairExprEq a b ≠ .isFalse neq

def eq_of_decide
  {a b: SingleLanePairExpr}
  (decEq: DecEq a b)
:
  a = b
:=
  match h: PairExpr.decidePairExprEq a b with
    | isTrue eq => eq
    | isFalse neq => absurd h (decEq neq)

def SubsetStx.convertA
  (decEq: DecEq srcA destA)
  (sub: SubsetStx dl srcA b)
:
  SubsetStx dl destA b
:=
  eq_of_decide decEq ▸ sub

def SubsetStx.convertB
  (decEq: DecEq srcB destB)
  (sub: SubsetStx dl a srcB)
:
  SubsetStx dl a destB
:=
  eq_of_decide decEq ▸ sub

abbrev IsSub := SubsetStx TestDl.toDefList


def SubsetStx.natSub: IsSub s3(.Nat) s3(:Nat) :=
  simpleInduction
    TestDl.vars.Nat
    rfl
    (SubsetStx.convertA
      (srcA := s3((null) | (((:Nat) & (.Nat), null))))
      (fun _ => Decidable.noConfusion)
      (.foldB
        (SubsetStx.convertB
          (srcB := s3(null | (:Nat, null)))
          (fun _ => Decidable.noConfusion)
          (.subUn
            (.subUnL .subNull)
            (.subUnR
              (.subPair
                (.subIrL
                  .varDef)
                .subNull))))))

def SubsetStx.infinitudeOfPrimes: IsSub s3(.Any) s3(:PrimesInf) := sorry
