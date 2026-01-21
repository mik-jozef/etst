import Etst.WFC.Ch2_Interpretation

namespace Etst

universe u


namespace SingleLaneExpr
  def const (lane: Set3.Lane) (x: Nat): SingleLaneExpr :=
    Expr.const lane x
  def var (x: Nat): SingleLaneExpr :=
    Expr.var x
  def null: SingleLaneExpr := Expr.null
  def pair (left rite: SingleLaneExpr): SingleLaneExpr :=
    Expr.pair left rite
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
    This proposition asserts that all variables under an
    even number of complements refer to the given lane.
  -/
  inductive LaneEqEven
    (lane: Set3.Lane)
  :
    (isEvenDepth: Bool) →
    SingleLaneExpr →
    Prop
  | constEven (x: Nat):
      LaneEqEven lane true (const lane x)
  | constOdd (varLane: Set3.Lane) (x: Nat):
      LaneEqEven lane false (const varLane x)
  | var (x: Nat) (isEvenDepth: Bool):
      LaneEqEven lane isEvenDepth (var x)
  | null (isEvenDepth: Bool): LaneEqEven lane isEvenDepth null
  | pair {isEvenDepth left rite}
      (leftEq: LaneEqEven lane isEvenDepth left)
      (riteEq: LaneEqEven lane isEvenDepth rite)
    :
      LaneEqEven lane isEvenDepth (pair left rite)
  | ir {isEvenDepth left rite}
      (leftEq: LaneEqEven lane isEvenDepth left)
      (riteEq: LaneEqEven lane isEvenDepth rite)
    :
      LaneEqEven lane isEvenDepth (ir left rite)
  | full {isEvenDepth body}
      (bodyEq: LaneEqEven lane isEvenDepth body)
    :
      LaneEqEven lane isEvenDepth (full body)
  | compl {isEvenDepth body}
      (bodyEq: LaneEqEven lane (!isEvenDepth) body)
    :
      LaneEqEven lane isEvenDepth (compl body)
  | arbIr {isEvenDepth body}
      (laneEqBody: LaneEqEven lane isEvenDepth body)
    :
      LaneEqEven lane isEvenDepth (arbIr body)
  
  namespace LaneEqEven
    variable {lane: Set3.Lane}
    variable {ed: Bool}
    variable {left rite body: SingleLaneExpr}
    
    def elimPairLeft
      (laneEq: LaneEqEven lane ed (Expr.pair left rite))
    :
      LaneEqEven lane ed left
    :=
      match laneEq with
      | .pair leftEq _ => leftEq
    
    def elimPairRite
      (laneEq: LaneEqEven lane ed (Expr.pair left rite))
    :
      LaneEqEven lane ed rite
    :=
      match laneEq with
      | .pair _ riteEq => riteEq
    
    def elimIrLeft
      (laneEq: LaneEqEven lane ed (Expr.ir left rite))
    :
      LaneEqEven lane ed left
    :=
      match laneEq with
      | .ir leftEq _ => leftEq
    
    def elimIrRite
      (laneEq: LaneEqEven lane ed (Expr.ir left rite))
    :
      LaneEqEven lane ed rite
    :=
      match laneEq with
      | .ir _ riteEq => riteEq
    
    def elimFull
      (laneEq: LaneEqEven lane ed (Expr.full body))
    :
      LaneEqEven lane ed body
    :=
      match laneEq with
      | .full bodyEq => bodyEq
    
    def elimCompl
      (laneEq: LaneEqEven lane ed (Expr.compl body))
    :
      LaneEqEven lane (!ed) body
    :=
      match laneEq with
      | .compl bodyEq => bodyEq
    
    def elimArbIr
      (laneEq: LaneEqEven lane ed (Expr.arbIr body))
    :
      LaneEqEven lane ed body
    :=
      match laneEq with
      | .arbIr laneEqBody => laneEqBody
  end LaneEqEven
end SingleLaneExpr


def BasicExpr.laneEqEven
  (expr: BasicExpr)
  (lane: Set3.Lane)
  (isEvenDepth: Bool)
:
  SingleLaneExpr.LaneEqEven
    lane
    isEvenDepth
    (expr.toLane (ite isEvenDepth lane lane.toggle))
:=
  match expr, isEvenDepth with
  | .const x, true => .constEven x
  | .const x, false => .constOdd lane.toggle x
  | .var x, true => .var x true
  | .var x, false => .var x false
  | .null, true => .null true
  | .null, false => .null false
  | .pair left rite, true =>
      .pair
        (left.laneEqEven lane true)
        (rite.laneEqEven lane true)
  | .pair left rite, false =>
      .pair
        (left.laneEqEven lane false)
        (rite.laneEqEven lane false)
  | .ir left rite, true =>
      .ir
        (left.laneEqEven lane true)
        (rite.laneEqEven lane true)
  | .ir left rite, false =>
      .ir
        (left.laneEqEven lane false)
        (rite.laneEqEven lane false)
  | .full body, true =>
      .full (body.laneEqEven lane true)
  | .full body, false =>
      .full (body.laneEqEven lane false)
  | .compl body, true =>
      .compl (body.laneEqEven lane false)
  | .compl body, false =>
      match lane with
      | .posLane => .compl (body.laneEqEven .posLane true)
      | .defLane => .compl (body.laneEqEven .defLane true)
  | .arbIr body, true => .arbIr (body.laneEqEven lane true)
  | .arbIr body, false => .arbIr (body.laneEqEven lane false)


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
| .const info x => serializeVar info x
| .var x => s!"v{x}"
| .null =>
  "null"
| .pair left rite =>
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
