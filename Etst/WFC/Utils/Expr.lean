import Etst.WFC.Ch2_Interpretation

namespace Etst


namespace SingleLaneExpr
  def var (lane: SingleLaneVarType) (x: Nat): SingleLaneExpr sig :=
    Expr.var lane x
  def bvar (x: Nat): SingleLaneExpr sig :=
    Expr.bvar x
  def op
    (opr: sig.Op)
    (args: (param: sig.Params opr) → SingleLaneExpr sig)
  :
    SingleLaneExpr sig
  :=
    Expr.op opr args
  def compl (body: SingleLaneExpr sig): SingleLaneExpr sig :=
    Expr.compl body
  def arbUn (body: SingleLaneExpr sig): SingleLaneExpr sig :=
    Expr.arbUn body
  def arbIr (body: SingleLaneExpr sig): SingleLaneExpr sig :=
    Expr.arbIr body
end SingleLaneExpr

/-
  This proposition asserts that the "context" part of an expression
  (anything not under a complement) only refers to variables from
  the given lane.
-/
inductive Expr.LaneEqCtx (lane: SingleLaneVarType): Expr E sig → Prop
| var (x: Nat): Expr.LaneEqCtx lane (Expr.var lane x)
| bvar (x: Nat): Expr.LaneEqCtx lane (Expr.bvar x)
| op
    (opr: sig.Op)
    (args: (param: sig.Params opr) → Expr E sig)
    (argsLaneEq: (param: sig.Params opr) → Expr.LaneEqCtx lane (args param))
  :
    Expr.LaneEqCtx lane (Expr.op opr args)
| compl (body: Expr E sig): Expr.LaneEqCtx lane (body.compl)
| arbUn
    (laneEqBody: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.arbUn body)
| arbIr
    (laneEqBody: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.arbIr body)

def Expr.LaneEqCtx.elimOp
  {sig: Signature}
  {opr: sig.Op}
  {args: (param: sig.Params opr) → Expr E sig}
  (laneEq: Expr.LaneEqCtx lane (Expr.op opr args))
  (param: sig.Params opr)
:
  Expr.LaneEqCtx lane (args param)
:=
  match laneEq with
  | .op _ _ argsLaneEq => argsLaneEq param

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
  (expr: BasicExpr sig)
  (lane: SingleLaneVarType)
:
  Expr.LaneEqCtx lane (expr.toLane lane)
:=
  match expr with
  | .var x => .var x
  | .bvar x => .bvar x
  | .op opr args =>
    .op opr _ (fun param => (args param).posLaneEqCtx lane)
  | .compl body => .compl (body.toLane lane.toggle)
  | .arbUn body => .arbUn (body.posLaneEqCtx lane)
  | .arbIr body => .arbIr (body.posLaneEqCtx lane)
