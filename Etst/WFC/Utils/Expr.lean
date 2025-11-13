import Etst.WFC.Ch2_Interpretation

namespace Etst


namespace SingleLaneExpr
  def var (lane: SingleLaneVarType) (x: Nat): SingleLaneExpr sig .expr :=
    Expr.var lane x
  def bvar (x: Nat): SingleLaneExpr sig .expr :=
    Expr.bvar x
  def op
    (opr: sig.Op)
    (args: SingleLaneExpr sig (.args (sig.arity opr)))
  :
    SingleLaneExpr sig .expr
  :=
    Expr.op opr args
  def compl (body: SingleLaneExpr sig .expr): SingleLaneExpr sig .expr :=
    Expr.compl body
  def arbUn (body: SingleLaneExpr sig .expr): SingleLaneExpr sig .expr :=
    Expr.arbUn body
  def arbIr (body: SingleLaneExpr sig .expr): SingleLaneExpr sig .expr :=
    Expr.arbIr body
end SingleLaneExpr

/-
  This proposition asserts that the "context" part of an expression
  (anything not under a complement) only refers to variables from
  the given lane.
-/
inductive Expr.LaneEqCtx (lane: SingleLaneVarType): Expr E sig kind → Prop
| var (x: Nat): Expr.LaneEqCtx lane (Expr.var lane x)
| bvar (x: Nat): Expr.LaneEqCtx lane (Expr.bvar x)
| op
    {opr: sig.Op}
    {args: Expr E sig (.args (sig.arity opr))}
    (argsLaneEq: Expr.LaneEqCtx lane args)
  :
    Expr.LaneEqCtx lane (Expr.op opr args)
| compl (body: Expr E sig .expr): Expr.LaneEqCtx lane body.compl
| arbUn
    (laneEqBody: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.arbUn body)
| arbIr
    (laneEqBody: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.arbIr body)
| nil: Expr.LaneEqCtx lane Expr.nil
| cons
    (headLaneEq: Expr.LaneEqCtx lane head)
    (tailLaneEq: Expr.LaneEqCtx lane tail)
  :
    Expr.LaneEqCtx lane (Expr.cons head tail)

-- TODO delete?
-- def Expr.LaneEqCtx.elimOp
--   {sig: Signature}
--   {opr: sig.Op}
--   {args: (param: sig.Params opr) → Expr E sig}
--   (laneEq: Expr.LaneEqCtx lane (Expr.op opr args))
--   (param: sig.Params opr)
-- :
--   Expr.LaneEqCtx lane (args param)
-- :=
--   match laneEq with
--   | .op _ _ argsLaneEq => argsLaneEq param

def Expr.LaneEqCtx.elimArbUn
  (laneEq: Expr.LaneEqCtx lane (body.arbUn))
:
  Expr.LaneEqCtx lane body
:=
  match laneEq with
  | .arbUn laneEqBody => laneEqBody

def Expr.LaneEqCtx.elimArbIr
  (laneEq: Expr.LaneEqCtx lane (body.arbIr))
:
  Expr.LaneEqCtx lane body
:=
  match laneEq with
  | .arbIr laneEqBody => laneEqBody


def BasicExpr.posLaneEqCtx
  (expr: BasicExpr sig kind)
  (lane: SingleLaneVarType)
:
  Expr.LaneEqCtx lane (expr.toLane lane)
:=
  match expr with
  | Expr.var _ x => .var x
  | .bvar x => .bvar x
  | .op _ args => .op (posLaneEqCtx args lane)
  | .compl body => .compl (body.toLane lane.toggle)
  | .arbUn body => .arbUn (body.posLaneEqCtx lane)
  | .arbIr body => .arbIr (body.posLaneEqCtx lane)
  | .nil => .nil
  | .cons head tail => .cons (posLaneEqCtx head lane) (posLaneEqCtx tail lane)


def Expr.eq_args_of_eq_op
  (eq: Expr.op opr argsL = Expr.op opr argsR)
:
  argsL = argsR
:=
  Expr.noConfusion eq (fun _ => eq_of_heq)
