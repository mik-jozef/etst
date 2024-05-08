import Arities
import UniSet3.UniDefList

/-
  See `exprEncoding.exprList`.
-/
def Pair.exprToEncoding: Expr pairSignature → Pair
| Expr.var x => pair zero (fromNat x)
| Expr.op pairSignature.Op.zero _ => pair (fromNat 1) zero

| Expr.op pairSignature.Op.pair args =>
  pair
    (fromNat 2)
    (pair
      (exprToEncoding (args ArityTwo.zth))
      (exprToEncoding (args ArityTwo.fst)))

| Expr.un left rite =>
  pair
    (fromNat 3)
    (pair
      (exprToEncoding left)
      (exprToEncoding rite))

| Expr.ir left rite =>
  pair
    (fromNat 4)
    (pair
      (exprToEncoding left)
      (exprToEncoding rite))

| Expr.cpl expr =>
  pair
    (fromNat 5)
    (exprToEncoding expr)

| Expr.ifThen cond body =>
  pair
    (fromNat 6)
    (pair
      (exprToEncoding cond)
      (exprToEncoding body))

| Expr.Un x body =>
  pair
    (fromNat 7)
    (pair
      (fromNat x)
      (exprToEncoding body))

| Expr.Ir x body =>
  pair
    (fromNat 8)
    (pair
      (fromNat x)
      (exprToEncoding body))


def Pair.defListToEncoding
  (dl: DefList pairSignature)
  (iStart iEnd: Nat)
:
  Pair
:=
  if h: iEnd ≤ iStart then
    Pair.zero
  else
    have: iEnd - iStart.succ < iEnd - iStart :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_not_le h)
        (Nat.lt_succ_self iStart)
    
    Pair.pair
      (exprToEncoding (dl.getDef iStart))
      (defListToEncoding dl (Nat.succ iStart) iEnd)
termination_by Pair.defListToEncoding dl iStart iEnd => iEnd - iStart
