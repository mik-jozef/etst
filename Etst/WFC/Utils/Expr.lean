import Etst.WFC.Ch2_Interpretation

namespace Etst


namespace SingleLaneExpr
  def var (lane: Set3.Lane) (x: Nat): SingleLaneExpr :=
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
  | varEven (x: Nat):
      LaneEqEven lane true (var lane x)
  | varOdd (varLane: Set3.Lane) (x: Nat):
      LaneEqEven lane false (var varLane x)
  | bvar (x: Nat) (isEvenDepth: Bool):
      LaneEqEven lane isEvenDepth (bvar x)
  | null (isEvenDepth: Bool): LaneEqEven lane isEvenDepth null
  | pair
      (leftEq: LaneEqEven lane isEvenDepth left)
      (riteEq: LaneEqEven lane isEvenDepth rite)
    :
      LaneEqEven lane isEvenDepth (pair left rite)
  | ir
      (leftEq: LaneEqEven lane isEvenDepth left)
      (riteEq: LaneEqEven lane isEvenDepth rite)
    :
      LaneEqEven lane isEvenDepth (ir left rite)
  | condFull
      (bodyEq: LaneEqEven lane isEvenDepth body)
    :
      LaneEqEven lane isEvenDepth (condFull body)
  | compl
      (bodyEq: LaneEqEven lane (!isEvenDepth) body)
    :
      LaneEqEven lane isEvenDepth (compl body)
  | arbIr
      (laneEqBody: LaneEqEven lane isEvenDepth body)
    :
      LaneEqEven lane isEvenDepth (arbIr body)
  
  namespace LaneEqEven
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
    
    def elimCondFull
      (laneEq: LaneEqEven lane ed (Expr.condFull body))
    :
      LaneEqEven lane ed body
    :=
      match laneEq with
      | .condFull bodyEq => bodyEq
    
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
  | .var x, true => .varEven x
  | .var x, false => .varOdd lane.toggle x
  | .bvar x, true => .bvar x true
  | .bvar x, false => .bvar x false
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
  | .condFull body, true =>
      .condFull (body.laneEqEven lane true)
  | .condFull body, false =>
      .condFull (body.laneEqEven lane false)
  | .compl body, true =>
      .compl (body.laneEqEven lane false)
  | .compl body, false =>
      match lane with
      | .posLane => .compl (body.laneEqEven .posLane true)
      | .defLane => .compl (body.laneEqEven .defLane true)
  | .arbIr body, true => .arbIr (body.laneEqEven lane true)
  | .arbIr body, false => .arbIr (body.laneEqEven lane false)


def Expr.toString (serializeVar: E → Nat → String):
  Expr E → String
| .un left rite =>
  let left := left.toString serializeVar
  let rite := rite.toString serializeVar
  s!"({left}) | ({rite})"
| .condSome body =>
  let cond := body.toString serializeVar
  s!"(?i {cond})"
| .arbUn body =>
  let bodyStr := body.toString serializeVar
  s!"Ex ({bodyStr})"
| .var info x => serializeVar info x
| .bvar x => s!"b{x}"
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
| .condFull body =>
  let cond := body.toString serializeVar
  s!"(?f {cond})"
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
