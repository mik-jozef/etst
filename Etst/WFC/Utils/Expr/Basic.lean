import Etst.WFC.Ch2_Interpretation

namespace Etst

universe u


namespace SingleLaneExpr
  def const (lane: Set3.Lane) (x: Nat): SingleLaneExpr :=
    Expr.const lane x
  def oracle (lane: Set3.Lane) (x: Nat): SingleLaneExpr :=
    Expr.oracle lane x
  def var (x: Nat): SingleLaneExpr :=
    Expr.var x
  def null: SingleLaneExpr := Expr.null
  def prod (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.prod left rite
  def un (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.un left rite
  def ir (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.ir left rite
  def some (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.some body
  def full (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.full body
  def compl (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.compl body
  def arbUn (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.arbUn body
  def arbIr (body: SingleLaneExpr): SingleLaneExpr :=
    Expr.arbIr body
  def impl (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.un left.compl rite
  
  
  /-
    `LaneEq even odd expr` constrains the lanes of constants in
    `expr` by parity. At even depth, constants must use `even`
    when that option is present. At odd depth, the constraint is
    given by `odd`.
  -/
  inductive LaneEq:
    (even odd: Option Set3.Lane) →
    SingleLaneExpr →
    Prop
  | constNone {odd lane x}:
      LaneEq .none odd (const lane x)
  | constSome {odd lane x}:
      LaneEq (.some lane) odd (const lane x)
  | oracle {even odd lane x}:
      LaneEq even odd (oracle lane x)
  | var {even odd x}:
      LaneEq even odd (var x)
  | null {even odd}:
      LaneEq even odd null
  | prod {even odd left rite}
      (leftEq: LaneEq even odd left)
      (riteEq: LaneEq even odd rite)
    :
      LaneEq even odd (prod left rite)
  | ir {even odd left rite}
      (leftEq: LaneEq even odd left)
      (riteEq: LaneEq even odd rite)
    :
      LaneEq even odd (ir left rite)
  | full {even odd body}
      (bodyEq: LaneEq even odd body)
    :
      LaneEq even odd (full body)
  | compl {even odd body}
      (bodyEq: LaneEq odd even body)
    :
      LaneEq even odd (compl body)
  | arbIr {even odd body}
      (bodyEq: LaneEq even odd body)
    :
      LaneEq even odd (arbIr body)
  
  namespace LaneEq
    variable
      {even odd: Option Set3.Lane}
      {left rite body: SingleLaneExpr}
    
    def elimProdLeft
      (laneEq: LaneEq even odd (.prod left rite))
    :
      LaneEq even odd left
    :=
      match laneEq with
      | .prod leftEq _ => leftEq
    
    def elimProdRite
      (laneEq: LaneEq even odd (.prod left rite))
    :
      LaneEq even odd rite
    :=
      match laneEq with
      | .prod _ riteEq => riteEq
    
    def elimIrLeft
      (laneEq: LaneEq even odd (Expr.ir left rite))
    :
      LaneEq even odd left
    :=
      match laneEq with
      | .ir leftEq _ => leftEq
    
    def elimIrRite
      (laneEq: LaneEq even odd (Expr.ir left rite))
    :
      LaneEq even odd rite
    :=
      match laneEq with
      | .ir _ riteEq => riteEq
    
    def elimFull
      (laneEq: LaneEq even odd (Expr.full body))
    :
      LaneEq even odd body
    :=
      match laneEq with
      | .full bodyEq => bodyEq
    
    def elimCompl
      (laneEq: LaneEq even odd (Expr.compl body))
    :
      LaneEq odd even body
    :=
      match laneEq with
      | .compl bodyEq => bodyEq
    
    def elimArbIr
      (laneEq: LaneEq even odd (Expr.arbIr body))
    :
      LaneEq even odd body
    :=
      match laneEq with
      | .arbIr bodyEq => bodyEq
  end LaneEq
end SingleLaneExpr

def BasicExpr.laneEq
  (expr: BasicExpr)
  (lane: Set3.Lane)
:
  SingleLaneExpr.LaneEq
    (.some lane)
    (.some lane.toggle)
    (expr.toLane lane)
:=
  match expr, lane with
  | .const _, .defLane => .constSome
  | .const _, .posLane => .constSome
  | .oracle _, .defLane => .oracle
  | .oracle _, .posLane => .oracle
  | .var _, .defLane => .var
  | .var _, .posLane => .var
  | .null, .defLane => .null
  | .null, .posLane => .null
  | .prod left rite, .defLane =>
    .prod (left.laneEq .defLane) (rite.laneEq .defLane)
  | .prod left rite, .posLane =>
    .prod (left.laneEq .posLane) (rite.laneEq .posLane)
  | .ir left rite, .defLane =>
    .ir (left.laneEq .defLane) (rite.laneEq .defLane)
  | .ir left rite, .posLane =>
    .ir (left.laneEq .posLane) (rite.laneEq .posLane)
  | .full body, .defLane => .full (body.laneEq .defLane)
  | .full body, .posLane => .full (body.laneEq .posLane)
  | .compl body, .defLane => .compl (body.laneEq .posLane)
  | .compl body, .posLane => .compl (body.laneEq .defLane)
  | .arbIr body, .defLane => .arbIr (body.laneEq .defLane)
  | .arbIr body, .posLane => .arbIr (body.laneEq .posLane)


def Expr.toString {E} (serializeVar: E → Nat → String):
  Expr E → String
| .un left rite =>
  let left := left.toString serializeVar
  let rite := rite.toString serializeVar
  s!"({left}) | ({rite})"
| .some body =>
  let cond := body.toString serializeVar
  s!"(◇ {cond})"
| .arbUn body =>
  let bodyStr := body.toString serializeVar
  s!"Ex ({bodyStr})"
| .const l x => serializeVar l x
| .oracle l x => s!"o:{serializeVar l x}"
| .var x => s!"v{x}"
| .null =>
  "null"
| .prod left rite =>
  let left := left.toString serializeVar
  let rite := rite.toString serializeVar
  s!"({left}, {rite})"
| .ir left rite =>
  let left := left.toString serializeVar
  let rite := rite.toString serializeVar
  s!"({left}) & ({rite})"
| .full body =>
  let cond := body.toString serializeVar
  s!"(□ {cond})"
| .compl expr =>
  let exprStr := expr.toString serializeVar
  s!"!({exprStr})"
| .arbIr body =>
  let bodyStr := body.toString serializeVar
  s!"All ({bodyStr})"

def BasicExpr.toString: BasicExpr → String :=
  Expr.toString fun _ x => s!"{x}"

def SingleLaneExpr.toString: SingleLaneExpr → String :=
  Expr.toString fun
    | .defLane, x => s!":{x}"
    | .posLane, x => s!".{x}"

instance: ToString BasicExpr where
  toString := BasicExpr.toString

instance: ToString SingleLaneExpr where
  toString := SingleLaneExpr.toString

instance: ToString (Expr Unit) := instToStringBasicExpr
instance: ToString (Expr Set3.Lane) := instToStringSingleLaneExpr
