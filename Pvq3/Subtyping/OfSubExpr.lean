/-
  Helpers for expressing properties that ought to hold for
  expressions if they hold for some sub-expressions.
-/
import Pvq3.Syntax.PExpr

namespace Pvq3.Desirables
  -- A helper type to allow easily expressing properties that ought
  -- to hold for expressions if they hold for some sub-expressions.
  inductive OfSubExprStep
    (eA eB: PaintedPExpr)
  :
    (resA resB: PaintedPExpr) → Prop
  | PairL
      (r: PaintedPExpr)
    :
      OfSubExprStep eA eB (.pair eA r) (.pair eB r)
  |
    PairR
      (l: PaintedPExpr)
    :
      OfSubExprStep eA eB (.pair l eA) (.pair l eB)
  |
    UnL
      (r: PaintedPExpr)
    :
      OfSubExprStep eA eB (.un eA r) (.un eB r)
  |
    UnR
      (l: PaintedPExpr)
    :
      OfSubExprStep eA eB (.un l eA) (.un l eB)
  |
    IrL
      (r: PaintedPExpr)
    :
      OfSubExprStep eA eB (.ir eA r) (.ir eB r)
  |
    IrR
      (l: PaintedPExpr)
    :
      OfSubExprStep eA eB (.ir l eA) (.ir l eB)
  |
    CondSome:
      OfSubExprStep eA eB (.condSome eA) (.condSome eB)
  |
    CondFull:
      OfSubExprStep eA eB (.condFull eA) (.condFull eB)
  |
    ArbUn
      (x: Nat)
    :
      OfSubExprStep eA eB (.arbUn x eA) (.arbUn x eB)
  |
    ArbIr
      (x: Nat)
    :
      OfSubExprStep eA eB (.arbIr x eA) (.arbIr x eB)
  
  mutual
    inductive OfSubExprPos
      (eA eB: PaintedPExpr)
    :
      (resA resB: PaintedPExpr) → Prop
    |
      id:
        OfSubExprPos eA eB eA eB
    |
      step
        (ofSub: OfSubExprStep eA eB resA resB)
      :
        OfSubExprPos eA eB resA resB
    |
      cplOfNeg
        (ofSub: OfSubExprNeg eA eB resA resB)
      :
        OfSubExprPos eA eB (.cpl resA) (.cpl resB)
    
    inductive OfSubExprNeg
      (eA eB: PaintedPExpr)
    :
      (resA resB: PaintedPExpr) → Prop
    |
      cplOfPos
        (ofSub: OfSubExprPos eA eB resA resB)
      :
        OfSubExprNeg eA eB (.cpl resA) (.cpl resB)
  end
  
  def OfSubExprPosOrNeg (eA eB resA resB: PaintedPExpr) :=
    OfSubExprPos eA eB resA resB ∨ OfSubExprNeg eA eB resA resB
  
  inductive OfSubExpr
    (eA eB: PaintedPExpr)
  :
    (resA resB: PaintedPExpr) → Prop
  |
    PairL
      (r: PaintedPExpr)
    :
      OfSubExpr eA eB (.pair eA r) (.pair eB r)
  |
    PairR
      (l: PaintedPExpr)
    :
      OfSubExpr eA eB (.pair l eA) (.pair l eB)
  |
    UnL
      (r: PaintedPExpr)
    :
      OfSubExpr eA eB (.un eA r) (.un eB r)
  |
    UnR
      (l: PaintedPExpr)
    :
      OfSubExpr eA eB (.un l eA) (.un l eB)
  |
    IrL
      (r: PaintedPExpr)
    :
      OfSubExpr eA eB (.ir eA r) (.ir eB r)
  |
    IrR
      (l: PaintedPExpr)
    :
      OfSubExpr eA eB (.ir l eA) (.ir l eB)
  |
    CondSome:
      OfSubExpr eA eB (.condSome eA) (.condSome eB)
  |
    CondFull:
      OfSubExpr eA eB (.condFull eA) (.condFull eB)
  |
    Cpl:
      OfSubExpr eA eB (.cpl eA) (.cpl eB)
  |
    ArbUn
      (x: Nat)
    :
      OfSubExpr eA eB (.arbUn x eA) (.arbUn x eB)
  |
    ArbIr
      (x: Nat)
    :
      OfSubExpr eA eB (.arbIr x eA) (.arbIr x eB)
  
end Pvq3.Desirables
