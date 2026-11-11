import Etst.WFC.Utils.NamedDefList.NamedPairExpr
import Etst.WFC.Utils.SubsetStx.Basic

namespace Etst
open DefList
open DefList.SubsetStx


-- TODO fix and move to an appropriate place.

pairDefList TestDl
  p3 Any := Ex t, t
  p3 None := All t, !t
  
  p3 Pair := null | Pair × Pair
  p3 Nat := null | Nat × null
  
  p3 Even := null | (Even × null) × null
  p3 Odd := Even × null
  
  p3 EvenMut := null | OddMut × null
  p3 OddMut := EvenMut × null
  
  p3 EvenNeg := !(EvenNeg × null)
  
  
  p3 Eq := Ex t, t × t × Any
  p3 EqSymm := All a, All b, Eq a b -> Eq b a
  
  p3 zth := Ex a, Ex b, (a × b) × a
  p3 fst := Ex a, Ex b, (a × b) × b
  
  p3 succ := Ex x: Nat, x × x × null
  
  p3 add :=
    | (Ex n: Nat, n × null × n)
    | (Ex a: Nat,
      Ex b: Nat,
        a × succ b × succ (add a b))
  
  p3 mul :=
    | (Ex n: Nat, n × null × null)
    | (Ex a: Nat,
      Ex b: Nat,
        a × succ b × add (mul a b) b)
  
  
  p3 NatLe :=
    | null × Nat × Any
    | (Ex le: NatLe, succ (zth le) × succ (fst le) × Any)
  
  p3 NatLeZero := NatLe null
  p3 AllNatLeZero := All n: Nat, NatLeZero n
  
  p3 ThenNatLeZero := Ex n: Nat, NatLeZero n then n
  p3 ThoseNatLeZero := Ex n: Nat, n × NatLeZero n
  
  p3 Prime :=
    & !succ null
    & (Ex n: Nat,
      All m: Nat,
        mul m Nat & n then (?some m & succ null) | (?some m & n) then n)
  
  p3 InList :=
    Ex e,
    Ex tail,
    | e × (e × tail) × Any
    | (Ex h,
      InList e tail then e × h × tail)
  
  p3 PrimesInf := All list, Ex p: Prime, !InList p list
pairDefList.

-- local macro "p3(" e:s3_pair_expr ")" : term => `(p3(TestDl, $e))


abbrev IsSub
  (a b: NamedPairExpr ExprKind.lane [])
:=
  TestDl.dl.SubsetStx
    (a.compile TestDl.consts)
    (b.compile TestDl.consts)


def SubsetStx.natSub: IsSub p3(.Nat) p3(:Nat) :=
  subSimpleInduction
    (fold
      (subId.unElimSub
        (unL
          subId)
        (unR
          (subProdMono
            (irCtxL
              subId)
            subId))))

def SubsetStx.natNotNat: IsSub p3(.Any) p3(:Nat | !.Nat) :=
  em.unElimSub
    (unL natSub)
    (unR subId)


/-
def natLeZeroThen: IsSub p3(.Nat) p3(:ThenNatLeZero) :=
  fold
    (unCtx
      sorry
      sorry)
-/










def SubsetStx.AddSymm :=
  p3(All a: Nat, All b: Nat, Eq (add a b) (add b a))

/-
def SubsetStx.addSymmNat:
  IsSub p3(.Nat) AddSymm
:=
  sorry

def SubsetStx.addSymm:
  IsSub p3(:Any) AddSymm
:=
  sorry


def SubsetStx.infinitudeOfPrimes:
  IsSub p3(.Any) p3(:PrimesInf)
:=
  sorry
-/


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


pair a b <= not null
not null <= pair any any

Ex n: Nat, (some n & !null) & n  ⊆  succ Nat


(Ex a, (a, (a, Any))) & (Ex a, (Any, (a, a)))  ⊆  Ex a, (a, (a, a))
  Ex a b, (a, (a, Any)) & (Any, (b, b))
  Ex a b, (a & Any, (a & b, Any & b))
  Ex a b, (a, (a & b, b))

Ex a b, a & b then (a, b)  ⊆  Ex a, (a, a)

some expr     ===  Ex x, (full ~x | expr)
~full ~expr   ===  ~All x, ~(full ~x | expr)


Any ⊆ T := null | (T, T)

Nat ⊆ zth (Ex n: Nat, (n, foo n))  ->  All n: Nat, some (foo n)
(Nat, Any) ⊆ (Ex n: Nat, (n, foo n))  ->  All n: Nat, full (foo n)

~Nat  ==  All n: Nat, ~n


Desirables:
(Un a, X) |& (Un b, Y) === (Un a b, X |& Y)
Un a b, X === Un b a, X
Ir a b, X === Ir b a, X


Un a b, X  ⊆  Un b a, X

full null  <=  none

condX expr |& condX expr'  ==?  condX (expr |& expr')

full B  ==  arbIr (full B)
some B  ==  arbUn (some B)


-/


/-
Un t: T, B  ==  Un t, (some t & T) & B
Ir t: T, B  ==  Ir t, (some t & ~T) | B

Un t: T, B  ==  Un t, (full ~t | T) & B
Ir t: T, B  ==  Ir t, (full ~t | ~T) | B



find an example A, B, C and D st.
(A|B) & (C|D) rsub T  and  A|B not sub T, C|D not sub T
(A|B) & (C|D) not rsub T   A&C | A&D | B&C | B&D rsub T
-/
