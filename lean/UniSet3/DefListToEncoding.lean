import Arities
import UniSet3.UniDefList
import UniSet3.Defs

/-
  See `exprEncoding.exprList`.
-/
def Pair.exprToEncoding
  (expr: Expr pairSignature)
:
  { p // uniSet3.IsExprEncoding p }
:=
  open uniSet3.IsExprEncoding in
  open uniSet3.IsExprEncoding.Bin in
  open uniSet3.IsExprEncoding.Quantifier in
  match expr with
  | Expr.var x => ⟨
      pair zero (fromNat x),
      IsVar (fromNat.isNatEncoding _)
    ⟩
  | Expr.op pairSignature.Op.zero _ => ⟨
      pair (fromNat 1) zero,
      IsZero
    ⟩

  | Expr.op pairSignature.Op.pair args =>
    let ⟨l, isEncL⟩ := exprToEncoding (args ArityTwo.zth)
    let ⟨r, isEncR⟩ := exprToEncoding (args ArityTwo.fst)
    ⟨
      pair (fromNat 2) (pair l r),
      IsBin (Is2 rfl) isEncL isEncR
    ⟩

  | Expr.un left rite =>
    let ⟨l, isEncL⟩ := exprToEncoding left
    let ⟨r, isEncR⟩ := exprToEncoding rite
    ⟨
      pair (fromNat 3) (pair l r),
      IsBin (Is3 rfl) isEncL isEncR,
    ⟩

  | Expr.ir left rite =>
    let ⟨l, isEncL⟩ := exprToEncoding left
    let ⟨r, isEncR⟩ := exprToEncoding rite
    ⟨
      pair (fromNat 4) (pair l r),
      IsBin (Is4 rfl) isEncL isEncR,
    ⟩

  | Expr.cpl expr =>
    let ⟨e, isEncE⟩ := exprToEncoding expr
    ⟨pair (fromNat 5) e, IsCpl isEncE⟩

  | Expr.ifThen cond body =>
    let ⟨c, isEncC⟩ := exprToEncoding cond
    let ⟨b, isEncB⟩ := exprToEncoding body
    ⟨
      pair (fromNat 6) (pair c b),
      IsBin (Is6 rfl) isEncC isEncB,
    ⟩

  | Expr.Un x body =>
    let ⟨b, isEncB⟩ := exprToEncoding body
    ⟨
      pair (fromNat 7) (pair (fromNat x) b),
      IsQuantifier (Is7 rfl) (fromNat.isNatEncoding _) isEncB
    ⟩

  | Expr.Ir x body =>
    let ⟨b, isEncB⟩ := exprToEncoding body
    ⟨
      pair (fromNat 8) (pair (fromNat x) b),
      IsQuantifier (Is8 rfl) (fromNat.isNatEncoding _) isEncB
    ⟩


structure Pair.DefListToEncoding
  (dl: DefList pairSignature)
where
  val: Pair
  isDef: uniSet3.IsDefEncoding val

def Pair.defListToEncoding
  (dl: DefList pairSignature)
  (iStart iEnd: Nat)
:
  DefListToEncoding dl
:=
  if h: iEnd ≤ iStart then
    ⟨Pair.zero, trivial⟩
  else
    have: iEnd - iStart.succ < iEnd - iStart :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_not_le h)
        (Nat.lt_succ_self iStart)
    
    let ⟨headEncoding, isExprHead⟩ :=
      exprToEncoding (dl.getDef iStart)
    
    let ⟨tailEncoding, isDefTail⟩ :=
      defListToEncoding dl (Nat.succ iStart) iEnd
    
    ⟨
      Pair.pair headEncoding tailEncoding,
      And.intro isExprHead isDefTail
    ⟩
      
termination_by Pair.defListToEncoding dl iStart iEnd => iEnd - iStart

namespace Pair
  noncomputable def encodingToExpr
    (p: Pair)
  :
    Expr pairSignature
  :=
    if h: ∃ expr, exprToEncoding expr = p then
      h.unwrap
    else
      Expr.var 0
  
end Pair    
