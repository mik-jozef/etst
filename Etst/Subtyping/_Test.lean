import Etst.Subtyping.Syntax.FiniteDefList
import Etst.Subtyping.SubsetStx

namespace Etst
open DefList
open DefList.SubsetStx

pairDefList TestDl
  s3 Nat := null | (Nat, null)
  
  s3 Even := null | ((Even, null), null)
  s3 Odd := (Even, null)
  
  s3 EvenMut := null | (OddMut, null)
  s3 OddMut := (EvenMut, null)
  
  s3 EvenNeg := !(EvenNeg, null)
  
  
  s3 Eq := Ex t, (t, (t, Any))
  s3 EqSymm := All a, All b, Eq a b -> Eq b a
  
  s3 zth := Ex a, Ex b, ((a, b), a)
  s3 fst := Ex a, Ex b, ((a, b), b)
  
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
  
  
  s3 NatLe :=
    | ((null, (Nat, Any)))
    | (Ex le: NatLe, (succ (zth le), (succ (fst le), Any)))
  
  s3 NatLeZero := NatLe null
  s3 AllNatLeZero := All n: Nat, NatLeZero n
  
  s3 ThenNatLeZero := Ex n: Nat, NatLeZero n then n
  s3 ThoseNatLeZero := Ex n: Nat, (n, NatLeZero n)
  
  s3 Prime :=
    & !succ null
    & (Ex n: Nat,
      All m: Nat,
        mul m Nat & n then (?some m & succ null) | (?some m & n) then n)
  
  s3 InList :=
    Ex e,
    Ex tail,
    | (e, ((e, tail), Any))
    | (Ex h,
      InList e tail then (e, (h, tail)))
  
  s3 PrimesInf := All list, Ex p: Prime, !InList p list
pairDefList.

local macro "s3(" e:s3_pair_expr ")" : term => `(s3(TestDl, $e))


abbrev IsSub := SubsetStx TestDl.toDefList


def SubsetStx.natSub: IsSub [] s3(.Nat) s3(:Nat) :=
  simpleInduction
    TestDl.vars.Nat
    rfl
    (foldB
      (subUn
        (unL
          subId)
        (unR
          (subPair
            (irL
              subId)
            subId))))

def SubsetStx.natNotNat: IsSub [] s3(.Any) s3(:Nat | !.Nat) :=
  em.trans (subUnLR natSub subId)


def natLeZeroThen: IsSub [] s3(.Nat) s3(:ThenNatLeZero) :=
  simpleInduction
    TestDl.vars.Nat
    rfl
    (foldB
      (subUn
        sorry
        sorry))










def SubsetStx.AddSymm :=
  BasicExpr.toDefLane
    s3(All a: Nat, All b: Nat, Eq (add a b) (add b a))

def SubsetStx.addSymmNat:
  IsSub [] s3(.Nat) AddSymm
:=
  simpleInduction
    TestDl.vars.Nat
    rfl
    sorry

def SubsetStx.addSymm:
  IsSub [] s3(:Any) AddSymm
:=
  sorry


def SubsetStx.infinitudeOfPrimes:
  IsSub [] s3(.Any) s3(:PrimesInf)
:=
  sorry


/-
Any ⊆ Ex x, (A & x) | ~A & x then x
Any ⊆ Ex x, (A & x) | ~A & x then x

A ⊆ B | C
A & ~B ⊆ C

Ex n: Nat, n  ===  Nat
Nat  ⊆  Ex n: Nat, n

TODO:
Un a, a
Un a, full a
full Un a, a


Un a, full Un b: a & null, b
Ir a, full Un b: a & null, b


(Ex a, (a, (a, Any))) & (Ex a, (Any, (a, a)))  ⊆  Ex a, (a, (a, a))
  Ex a b, (a, (a, Any)) & (Any, (b, b))
  Ex a b, (a & Any, (a & b, Any & b))
  Ex a b, (a, (a & b, b))

Ex a b, a & b then (a, b)  ⊆  Ex a, (a, a)


Any ⊆ T := null | (T, T)

Nat ⊆ zth (Ex n: Nat, (n, foo n))  ->  All n: Nat, condSome (foo n)
(Nat, Any) ⊆ (Ex n: Nat, (n, foo n))  ->  All n: Nat, condFull (foo n)

~Nat  ==  All n: Nat, ~n


Desirables:
(Un a, X) |& (Un b, Y) === (Un a b, X |& Y)
Un a b, X === Un b a, X
Ir a b, X === Ir b a, X


Un a b, X  ⊆  Un b a, X

-/


/-
Un t: T, B  ==  Un t, (condSome t & T) & B
Ir t: T, B  ==  Ir t, (condSome t & ~T) | B

Un t: T, B  ==  Un t, (condFull ~t | T) & B
Ir t: T, B  ==  Ir t, (condFull ~t | ~T) | B
-/
