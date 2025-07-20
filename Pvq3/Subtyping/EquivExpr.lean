import Pvq3.Subtyping.OfSubExpr
import Pvq3.Syntax.PExpr

namespace Pvq3.Desirables
  
  /-
    The subtyping algorithm ought to give the same results up to
    this equivalence.
  -/
  inductive EquivExpr: (a b: PaintedPExpr) → Prop
  | refl (a: PaintedPExpr): EquivExpr a a
  | trans (ab: EquivExpr a b) (bc: EquivExpr b c): EquivExpr a c
  
  -- Equivalent sub-expressions may be replaced with each other
  -- to form an equivalent expression.
  | subst
      (equiv: EquivExpr a b)
      (ofSub: OfSubExpr a b resA resB)
    :
      EquivExpr resA resB
  
  | unionSymm (a b: PaintedPExpr): EquivExpr (.un a b) (.un b a)
  | unionAssoc (a b c: PaintedPExpr):
      EquivExpr (.un a (.un b c)) (.un (.un a b) c)
  
  | interSymm (a b: PaintedPExpr): EquivExpr (.ir a b) (.ir b a)
  | interAssoc (a b c: PaintedPExpr):
      EquivExpr (.ir a (.ir b c)) (.ir (.ir a b) c)
  
  | cplZero:
      EquivExpr
        (.cpl .zero)
        (.pair (.arbUn 0 (.solidVar 0)) (.arbUn 0 (.solidVar 0)))
  | cplPair
      (a b: PaintedPExpr)
    :
      EquivExpr
        (.cpl (.pair a b))
        (.un .zero (.un (.pair a.cpl .anyExpr) (.pair .anyExpr b.cpl)))
  
  | cplUn (a b: PaintedPExpr):
      EquivExpr (.cpl (.un a b)) (.ir (.cpl a) (.cpl b))
  | cplIr (a b: PaintedPExpr):
      EquivExpr (.cpl (.ir a b)) (.un (.cpl a) (.cpl b))
  | cplCondSome (a: PaintedPExpr):
      EquivExpr (.cpl (.condSome a)) (.condFull (.cpl a))
  | cplCondFull (a: PaintedPExpr):
      EquivExpr (.cpl (.condFull a)) (.condSome (.cpl a))
  
  | cplArbUn
      (x: Nat)
      (body: PaintedPExpr)
    :
      EquivExpr
        (.cpl (.arbUn x body))
        (.arbIr x (.cpl body))
  | cplArbIr
      (x: Nat)
      (body: PaintedPExpr)
    :
      EquivExpr
        (.cpl (.arbIr x body))
        (.arbUn x (.cpl body))
  
  | arbUnSplit
      (x: Nat)
      (l r: PaintedPExpr)
    :
      EquivExpr
        (.arbUn x (.un l r))
        (.un (.arbUn x l) (.arbUn x r))
  | arbUnUnused
      (x: Nat)
      (notFree: ¬body.toExpr.IsFreeVar Set.empty x)
    :
      EquivExpr (.arbUn x body) body
  | arbUnIr
      (x: Nat)
      (l: PaintedPExpr)
      (notFree: ¬r.toExpr.IsFreeVar Set.empty x)
    :
      EquivExpr
        (.arbUn x (.ir l r))
        (.ir (.arbUn x l) r)
  
  | arbIrSplit
      (x: Nat)
      (l r: PaintedPExpr)
    :
      EquivExpr
        (.arbIr x (.ir l r))
        (.ir (.arbIr x l) (.arbIr x r))
  | arbIrUnused
      (x: Nat)
      (notFree: ¬body.toExpr.IsFreeVar Set.empty x)
    :
      EquivExpr (.arbIr x body) body
  | arbIrUn
      (x: Nat)
      (l: PaintedPExpr)
      (notFree: ¬r.toExpr.IsFreeVar Set.empty x)
    :
      EquivExpr
        (.arbIr x (.un l r))
        (.un (.arbIr x l) r)
  
  def EquivExpr.unionAssocRev
    (a b c: PaintedPExpr)
  :
    EquivExpr
      (.un (.un a b) c)
      (.un a (.un b c))
  :=
    (unionSymm _ _).trans
      ((unionAssoc _ _ _).trans
        ((unionSymm _ _).trans
          ((unionAssoc _ _ _).trans
            ((unionSymm _ _).trans
              (refl _)))))
    
    def EquivExpr.interAssocRev
      (a b c: PaintedPExpr)
    :
      EquivExpr
        (.ir (.ir a b) c)
        (.ir a (.ir b c))
    :=
      (interSymm _ _).trans
        ((interAssoc _ _ _).trans
          ((interSymm _ _).trans
            ((interAssoc _ _ _).trans
              ((interSymm _ _).trans
                (refl _)))))
    
    
    def EquivExpr.arbUnUn
      (x: Nat)
      (l: PaintedPExpr)
      (notFree: ¬r.toExpr.IsFreeVar Set.empty x)
    :
      EquivExpr
        (.arbUn x (.un l r))
        (.un (.arbUn x l) r)
    :=
      trans
        (arbUnSplit x l r)
        (subst (arbUnUnused x notFree) (.UnR _))
    
    def EquivExpr.arbIrIr
      (x: Nat)
      (l: PaintedPExpr)
      (notFree: ¬r.toExpr.IsFreeVar Set.empty x)
    :
      EquivExpr
        (.arbIr x (.ir l r))
        (.ir (.arbIr x l) r)
    :=
      trans
        (arbIrSplit x l r)
        (subst (arbIrUnused x notFree) (.IrR _))
    
    
    def EquivExpr.equivInterp
      (isEquiv: EquivExpr a b)
      (v: Valuation Pair)
    :
      a.intp v = b.intp v
    :=
      -- Trying to match on `isEquiv` be like:
      -- 
      -- """
      --   The termination measure's type must not depend on the function's
      --   varying parameters, but Pvq3.Desirables.EquivExpr.equivInterp's
      --   termination measure does:
      --   ∀ {a b : PaintedPExpr}, EquivExpr a b → Valuation Pair → EquivExpr a b
      --   Try using `sizeOf` explicitly
      -- """
      -- 
      -- Also, trying sizeof induces False as the goal 🙃
      
    isEquiv.recOn
      (motive := fun a b _ => (v: Valuation Pair) → a.intp v = b.intp v)
      (fun _ _ => rfl)
      (fun _ _ abIh bcIh v => (abIh v).trans (bcIh v))
      (fun
        | _, .PairL r, ih, v => PairExpr.pair_eq_of_eq (ih v) rfl
        | _, .PairR l, ih, v => PairExpr.pair_eq_of_eq rfl (ih v)
        | _, .UnL r, ih, v => PairExpr.un_eq_of_eq (ih v) rfl
        | _, .UnR l, ih, v => PairExpr.un_eq_of_eq rfl (ih v)
        | _, .IrL r, ih, v => PairExpr.ir_eq_of_eq (ih v) rfl
        | _, .IrR l, ih, v => PairExpr.ir_eq_of_eq rfl (ih v)
        | _, .CondSome, ih, v => PairExpr.condSome_eq_of_eq (ih v)
        | _, .CondFull, ih, v => PairExpr.condFull_eq_of_eq (ih v)
        | _, .Cpl, ih, v => PairExpr.cpl_eq_of_eq v (ih v)
        | _, .ArbUn x, ih, v =>
            PairExpr.arbUn_eq_of_eq x fun p => ih (v.update x p)
        | _, .ArbIr x, ih, v =>
            PairExpr.arbIr_eq_of_eq x fun p => ih (v.update x p))
      (fun _ _ _ => PairExpr.un_symm _ _ _ _)
      (fun _ _ _ _ => PairExpr.un_assoc _ _ _ _ _)
      (fun _ _ _ => PairExpr.ir_symm _ _ _ _)
      (fun _ _ _ _ => PairExpr.ir_assoc _ _ _ _ _)
      PairExpr.cpl_zero_eq
      (fun _ _ _ => PairExpr.cpl_pair_eq _ _ _)
      (fun _ _ _ => PairExpr.cpl_un_eq _ _ _)
      (fun _ _ _ => PairExpr.cpl_ir_eq _ _ _)
      (fun _ _ => PairExpr.cpl_condSome_eq _ _)
      (fun _ _ => PairExpr.cpl_condFull_eq _ _)
      (fun _ _ _ => PairExpr.cpl_arbUn_eq _ _ _)
      (fun _ _ _ => PairExpr.cpl_arbIr_eq _ _ _)
      (fun _ _ _ _ => PairExpr.arbUn_eq_split _ _ _ _)
      (fun _ notFree _ => PairExpr.arbUn_eq_unused _ _ notFree)
      (fun _ _ notFree _ => PairExpr.arbUn_ir_eq _ _ _ notFree)
      (fun _ _ _ _ => PairExpr.arbIr_eq_split _ _ _ _)
      (fun _ notFree _ => PairExpr.arbIr_eq_unused _ _ notFree)
      (fun _ _ notFree _ => PairExpr.arbIr_un_eq _ _ _ notFree)
      v
    
end Pvq3.Desirables
