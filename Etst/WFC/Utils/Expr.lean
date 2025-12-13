import Etst.WFC.Ch2_Interpretation

namespace Etst


namespace SingleLaneExpr
  def var (lane: SingleLaneVarType) (x: Nat): SingleLaneExpr :=
    Expr.var lane x
  def bvar (x: Nat): SingleLaneExpr :=
    Expr.bvar x
  def null: SingleLaneExpr := Expr.null
  def pair (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.pair left rite
  def un (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.un left rite
  def ir (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.ir left rite
  def condSome (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.condSome body
  def condFull (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.condFull body
  def compl (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.compl body
  def arbUn (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.arbUn body
  def arbIr (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.arbIr body
  def impl (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.un left.compl rite
end SingleLaneExpr

/-
  This proposition asserts that the "context" part of an expression
  (anything not under a complement) only refers to variables from
  the given lane.
-/
inductive Expr.LaneEqCtx (lane: SingleLaneVarType): Expr E → Prop
| var (x: Nat): Expr.LaneEqCtx lane (Expr.var lane x)
| bvar (x: Nat): Expr.LaneEqCtx lane (Expr.bvar x)
| null: Expr.LaneEqCtx lane Expr.null
| pair
    (leftEq: Expr.LaneEqCtx lane left)
    (riteEq: Expr.LaneEqCtx lane rite)
  :
    Expr.LaneEqCtx lane (Expr.pair left rite)
| un
    (leftEq: Expr.LaneEqCtx lane left)
    (riteEq: Expr.LaneEqCtx lane rite)
  :
    Expr.LaneEqCtx lane (Expr.un left rite)
| ir
    (leftEq: Expr.LaneEqCtx lane left)
    (riteEq: Expr.LaneEqCtx lane rite)
  :
    Expr.LaneEqCtx lane (Expr.ir left rite)
| condSome
    (bodyEq: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.condSome body)
| condFull
    (bodyEq: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.condFull body)
| compl (body: Expr E): Expr.LaneEqCtx lane (body.compl)
| arbUn
    (laneEqBody: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.arbUn body)
| arbIr
    (laneEqBody: Expr.LaneEqCtx lane body)
  :
    Expr.LaneEqCtx lane (Expr.arbIr body)


def Expr.LaneEqCtx.elimPairLeft
  (laneEq: Expr.LaneEqCtx lane (Expr.pair left rite))
:
  Expr.LaneEqCtx lane left
:=
  match laneEq with
  | .pair leftEq _ => leftEq

def Expr.LaneEqCtx.elimPairRite
  (laneEq: Expr.LaneEqCtx lane (Expr.pair left rite))
:
  Expr.LaneEqCtx lane rite
:=
  match laneEq with
  | .pair _ riteEq => riteEq

def Expr.LaneEqCtx.elimUnLeft
  (laneEq: Expr.LaneEqCtx lane (Expr.un left rite))
:
  Expr.LaneEqCtx lane left
:=
  match laneEq with
  | .un leftEq _ => leftEq

def Expr.LaneEqCtx.elimUnRite
  (laneEq: Expr.LaneEqCtx lane (Expr.un left rite))
:
  Expr.LaneEqCtx lane rite
:=
  match laneEq with
  | .un _ riteEq => riteEq

def Expr.LaneEqCtx.elimIrLeft
  (laneEq: Expr.LaneEqCtx lane (Expr.ir left rite))
:
  Expr.LaneEqCtx lane left
:=
  match laneEq with
  | .ir leftEq _ => leftEq

def Expr.LaneEqCtx.elimIrRite
  (laneEq: Expr.LaneEqCtx lane (Expr.ir left rite))
:
  Expr.LaneEqCtx lane rite
:=
  match laneEq with
  | .ir _ riteEq => riteEq

def Expr.LaneEqCtx.elimCondSome
  (laneEq: Expr.LaneEqCtx lane (Expr.condSome body))
:
  Expr.LaneEqCtx lane body
:=
  match laneEq with
  | .condSome bodyEq => bodyEq

def Expr.LaneEqCtx.elimCondFull
  (laneEq: Expr.LaneEqCtx lane (Expr.condFull body))
:
  Expr.LaneEqCtx lane body
:=
  match laneEq with
  | .condFull bodyEq => bodyEq

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


def BasicExpr.laneEqCtx
  (expr: BasicExpr)
  (lane: SingleLaneVarType)
:
  Expr.LaneEqCtx lane (expr.toLane lane)
:=
  match expr with
  | .var x => .var x
  | .bvar x => .bvar x
  | .null => .null
  | .pair left rite =>
      .pair (left.laneEqCtx lane) (rite.laneEqCtx lane)
  | .un left rite =>
      .un (left.laneEqCtx lane) (rite.laneEqCtx lane)
  | .ir left rite =>
      .ir (left.laneEqCtx lane) (rite.laneEqCtx lane)
  | .condSome body =>
      .condSome (body.laneEqCtx lane)
  | .condFull body =>
      .condFull (body.laneEqCtx lane)
  | .compl body => .compl (body.toLane lane.toggle)
  | .arbUn body => .arbUn (body.laneEqCtx lane)
  | .arbIr body => .arbIr (body.laneEqCtx lane)
