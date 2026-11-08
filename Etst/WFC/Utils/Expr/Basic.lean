module
public import Etst.WFC.Ch2_Interpretation

public section
namespace Etst
universe u

  
/-
  For expressions with lanes, `LaneEq even odd expr` constrains the
  lanes of constants in `expr` by parity. At even depth, constants
  must use the `even` lane when that option is present. At odd depth,
  the constraint is given by `odd`.
  
  For expressions without lanes, `LaneEq` always holds.
-/
inductive Expr.LaneEq:
  {kind: ExprKind} →
  Expr kind →
  (even odd: Option Set3.Lane) →
  Prop
| constBasic {x even odd}:
    (const (kind := .basic) () x).LaneEq even odd
| constLaneNone {lane x odd}:
    (const (kind := .lane) lane x).LaneEq .none odd
| constLaneSome {lane x odd}:
    (const (kind := .lane) lane x).LaneEq (.some lane) odd
| var {x even odd}:
    (var x).LaneEq even odd
| null {even odd}:
    (null).LaneEq even odd
| prod {left rite even odd}
    (leftEq: left.LaneEq even odd)
    (riteEq: rite.LaneEq even odd)
  :
    (prod left rite).LaneEq even odd
| ir {left rite even odd}
    (leftEq: left.LaneEq even odd)
    (riteEq: rite.LaneEq even odd)
  :
    (ir left rite).LaneEq even odd
| full {body even odd}
    (bodyEq: body.LaneEq even odd)
  :
    (full body).LaneEq even odd
| compl {body even odd}
    (bodyEq: body.LaneEq odd even)
  :
    (compl body).LaneEq even odd
| arbIr {body even odd}
    (bodyEq: body.LaneEq even odd)
  :
    (arbIr body).LaneEq even odd

namespace Expr.LaneEq
  variable
    {kind: ExprKind}
    {even odd: Option Set3.Lane}
    {left rite body: Expr kind}
  
  theorem of_basic {even odd}:
    (expr: Expr .basic) → expr.LaneEq even odd
  | .const _ _ => constBasic
  | .var _ => var
  | .null => null
  | .prod left rite => prod (of_basic left) (of_basic rite)
  | .ir left rite => ir (of_basic left) (of_basic rite)
  | .full body => full (of_basic body)
  | .compl body => compl (of_basic body)
  | .arbIr body => arbIr (of_basic body)
  
  
  theorem elimProdLeft
    (laneEq: LaneEq (.prod left rite) even odd)
  :
    left.LaneEq even odd
  :=
    match laneEq with
    | .prod leftEq _ => leftEq
  
  theorem elimProdRite
    (laneEq: LaneEq (.prod left rite) even odd)
  :
    rite.LaneEq even odd
  :=
    match laneEq with
    | .prod _ riteEq => riteEq
  
  theorem elimIrLeft
    (laneEq: LaneEq (.ir left rite) even odd)
  :
    left.LaneEq even odd
  :=
    match laneEq with
    | .ir leftEq _ => leftEq
  
  theorem elimIrRite
    (laneEq: LaneEq (.ir left rite) even odd)
  :
    rite.LaneEq even odd
  :=
    match laneEq with
    | .ir _ riteEq => riteEq
  
  theorem elimFull
    (laneEq: LaneEq (.full body) even odd)
  :
    body.LaneEq even odd
  :=
    match laneEq with
    | .full bodyEq => bodyEq
  
  theorem elimCompl
    (laneEq: LaneEq (.compl body) even odd)
  :
    body.LaneEq odd even
  :=
    match laneEq with
    | .compl bodyEq => bodyEq
  
  theorem elimArbIr
    (laneEq: LaneEq (.arbIr body) even odd)
  :
    body.LaneEq even odd
  :=
    match laneEq with
    | .arbIr bodyEq => bodyEq
end Expr.LaneEq


def Expr.toString {kind}
  (serializeVar: kind.ConstTag → Nat → String)
:
  Expr kind → String
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

def Expr.toStringBasic: Expr .basic → String :=
  Expr.toString fun _ x => s!"{x}"

def Expr.toStringLane: Expr .lane → String :=
  Expr.toString fun
    | .defLane, x => s!":{x}"
    | .posLane, x => s!".{x}"

instance: ToString (Expr .basic) where
  toString := Expr.toStringBasic

instance: ToString (Expr .lane) where
  toString := Expr.toStringLane
