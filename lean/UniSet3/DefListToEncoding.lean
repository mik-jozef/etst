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

def Pair.exprToEncoding.injEq
  (eq: exprToEncoding a = exprToEncoding b)
:
  a = b
:=
  match a, b with
  | Expr.var _, Expr.var _ =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ => congr rfl ∘ fromNat.injEq
  
  | Expr.op pairSignature.Op.zero _,
    Expr.op pairSignature.Op.zero _
  =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ _ => congr rfl (funext fun.)
  
  | Expr.op pairSignature.Op.pair _argsA,
    Expr.op pairSignature.Op.pair _argsB
  =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun zthEncEq fstEncEq =>
            let zthEq := exprToEncoding.injEq (Subtype.eq zthEncEq)
            let fstEq := exprToEncoding.injEq (Subtype.eq fstEncEq)
            congr
              rfl
              (funext fun arg =>
                match arg with
                | ArityTwo.zth => zthEq
                | ArityTwo.fst => fstEq)
  
  | Expr.un _leftA _riteA, Expr.un _leftB _riteB =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun leftEq riteEq =>
            let leftEq := exprToEncoding.injEq (Subtype.eq leftEq)
            let riteEq := exprToEncoding.injEq (Subtype.eq riteEq)
            congrBin rfl leftEq riteEq
  
  | Expr.ir _leftA _riteA, Expr.ir _leftB _riteB =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun leftEq riteEq =>
            let leftEq := exprToEncoding.injEq (Subtype.eq leftEq)
            let riteEq := exprToEncoding.injEq (Subtype.eq riteEq)
            congrBin rfl leftEq riteEq
  
  | Expr.cpl _exprA, Expr.cpl _exprB =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        congr rfl (exprToEncoding.injEq (Subtype.eq eqP))
  
  | Expr.ifThen _condA _bodyA, Expr.ifThen _condB _bodyB =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun condEq bodyEq =>
            let condEq := exprToEncoding.injEq (Subtype.eq condEq)
            let bodyEq := exprToEncoding.injEq (Subtype.eq bodyEq)
            congrBin rfl condEq bodyEq
  
  | Expr.Un _xA _bodyA, Expr.Un _xB _bodyB =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun xEq bodyEq =>
            let xEq := fromNat.injEq xEq
            let bodyEq := exprToEncoding.injEq (Subtype.eq bodyEq)
            congrBin rfl xEq bodyEq
  
  | Expr.Ir _xA _bodyA, Expr.Ir _xB _bodyB =>
    Pair.noConfusion
      (Subtype.eqVal eq)
      fun _ eqP =>
        Pair.noConfusion
          eqP
          fun xEq bodyEq =>
            let xEq := fromNat.injEq xEq
            let bodyEq := exprToEncoding.injEq (Subtype.eq bodyEq)
            congrBin rfl xEq bodyEq


structure Pair.DefListToEncoding
  (dl: DefList pairSignature)
  (iStart: Nat)
where
  val: Pair
  isDef: uniSet3.IsDefEncoding val
  eqAt:
    ∀ i < val.arrayLength,
      val.arrayAt i = Pair.exprToEncoding (dl.getDef (iStart + i))

def Pair.defListToEncoding
  (dl: DefList pairSignature)
  (iStart iEnd: Nat)
:
  DefListToEncoding dl iStart
:=
  if h: iEnd ≤ iStart then
    ⟨Pair.zero, trivial, fun.⟩
  else
    have: iEnd - iStart.succ < iEnd - iStart :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_not_le h)
        (Nat.lt_succ_self iStart)
    
    -- let ⟨headEncoding, isExprHead⟩ :=
    let tmp :=
      exprToEncoding (dl.getDef iStart)
    let headEncoding := tmp.val
    let isExprHead := tmp.property
    
    let ⟨tailEncoding, isDefTail, eqAtTail⟩ :=
      defListToEncoding dl iStart.succ iEnd
    
    {
      val := Pair.pair headEncoding tailEncoding
      isDef := And.intro isExprHead isDefTail
      eqAt :=
        fun i iWithinBounds =>
          match i with
          | Nat.zero => Nat.add_zero _ ▸ rfl
          | Nat.succ iPred =>
            let iPredWithinBounds :=
              Nat.lt_of_succ_lt_succ iWithinBounds
            
            Nat.succ_add_eq_succ_add iStart iPred ▸
            arrayAt.consEq
              (eqAtTail iPred iPredWithinBounds)
              headEncoding
    }
      
termination_by Pair.defListToEncoding dl iStart iEnd => iEnd - iStart

def Pair.defListToEncoding.eqIfEndLe
  (dl: DefList pairSignature)
  {iStart iEnd: Nat}
  (le: iEnd ≤ iStart)
:
  (defListToEncoding dl iStart iEnd).val = Pair.zero
:=
  by unfold defListToEncoding; rw [dif_pos le]

def Pair.defListToEncoding.eqIfStartLt
  (dl: DefList pairSignature)
  {iStart iEnd: Nat}
  (lt: iStart < iEnd)
:
  (defListToEncoding dl iStart iEnd).val
    =
  Pair.pair
    (exprToEncoding (dl.getDef iStart)).val
    (defListToEncoding dl iStart.succ iEnd).val
:=
  let notLe: ¬ iEnd ≤ iStart := Nat.not_le_of_lt lt
  
  by
    conv => lhs; unfold defListToEncoding; rfl
    exact dif_neg notLe ▸ rfl

def Pair.defListToEncoding.lengthEq
  (dl: DefList pairSignature)
  (iStart iEnd: Nat)
:
  (defListToEncoding dl iStart iEnd).val.arrayLength = iEnd - iStart
:=
  if h: iEnd ≤ iStart then
    eqIfEndLe dl h ▸
    Nat.sub_eq_zero_of_le h ▸
    rfl
  else
    have: iEnd - iStart.succ < iEnd - iStart :=
      Nat.sub_lt_sub_left
        (Nat.lt_of_not_le h)
        (Nat.lt_succ_self iStart)
    
    let natEqL :=
      Nat.succ_sub_comm_of_lt (Nat.succ_le_of_lt (Nat.lt_of_not_le h))
    
    let natEqR := Nat.succ_sub_succ_eq_sub iEnd iStart
    
    eqIfStartLt dl (Nat.lt_of_not_le h) ▸
    (arrayLength.eqSuccTail _ _).trans
      (lengthEq dl iStart.succ iEnd ▸
      (natEqL.trans natEqR))
termination_by
  Pair.defListToEncoding.lengthEq dl iStart iEnd
=>
  iEnd - iStart

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
  
  def encodingToExpr.eqOfExists
    {p: Pair}
    (ex: ∃ expr, exprToEncoding expr = p)
  :
    encodingToExpr p = ex.unwrap
  := by
    unfold encodingToExpr
    exact dif_pos ex ▸ rfl
  
  def encodingToExpr.isInverse
    (expr: Expr pairSignature)
  :
    encodingToExpr (exprToEncoding expr) = expr
  :=
    let ex := ⟨expr, rfl⟩
    let eq := encodingToExpr.eqOfExists ex
    
    eq ▸ exprToEncoding.injEq (Subtype.eq ex.unwrap.property)
  
end Pair    
