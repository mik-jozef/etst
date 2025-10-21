import Etst.WFC.Ch2_Interpretation

namespace Etst


inductive SingleLaneExpr.IsPosVarLaneOnly (lane: SingleLaneVarType):
  SingleLaneExpr sig → Prop
| var (x: Nat): IsPosVarLaneOnly lane (.var lane x)
| bvar (x: Nat): IsPosVarLaneOnly lane (.bvar x)
| op
    (opr: sig.Op)
    (args: sig.Params opr → SingleLaneExpr sig)
    (argsLaneOnly:
      (param: sig.Params opr) → IsPosVarLaneOnly lane (args param))
  :
    IsPosVarLaneOnly lane (.op opr args)
  -- Complements satisfy the condition vacuously.
| compl (body: SingleLaneExpr sig): IsPosVarLaneOnly lane (.compl body)
| arbUn 
    (bodyLaneOnly: IsPosVarLaneOnly lane body)
  :
    IsPosVarLaneOnly lane (.arbUn body)
| arbIr 
    (bodyLaneOnly: IsPosVarLaneOnly lane body)
  :
    IsPosVarLaneOnly lane (.arbIr body)


def SingleLaneExpr.IsPosVarLaneOnly.elimOp
  {sig: Signature}
  {opr: sig.Op}
  {args: sig.Params opr → SingleLaneExpr sig}
  (isConstrained: IsPosVarLaneOnly lane (.op opr args))
  (param: sig.Params opr)
:
  IsPosVarLaneOnly lane (args param)
:=
  match isConstrained with
  | .op _ _ argsLaneOnly => argsLaneOnly param

def SingleLaneExpr.IsPosVarLaneOnly.elimArbUn
  (isConstrained: IsPosVarLaneOnly lane (.arbUn body))
:
  IsPosVarLaneOnly lane body
:=
  match isConstrained with
  | .arbUn bodyLaneOnly => bodyLaneOnly

def SingleLaneExpr.IsPosVarLaneOnly.elimArbIr
  (isConstrained: IsPosVarLaneOnly lane (.arbIr body))
:
  IsPosVarLaneOnly lane body
:=
  match isConstrained with
  | .arbIr bodyLaneOnly => bodyLaneOnly


def BasicExpr.toIsLaneOnly:
  (expr: BasicExpr sig) →
  (expr.toLane lane).IsPosVarLaneOnly lane
| .var x => .var x
| .bvar x => .bvar x
| .op opr args => .op opr _ (fun param => (args param).toIsLaneOnly)
| .compl body => .compl (body.toLane lane.toggle)
| .arbUn body => .arbUn body.toIsLaneOnly
| .arbIr body => .arbIr body.toIsLaneOnly
