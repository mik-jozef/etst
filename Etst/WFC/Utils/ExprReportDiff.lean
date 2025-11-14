import Etst.WFC.Utils.PairExpr

namespace Etst


instance: ToString SingleLaneVarType where
  toString
  | .posLane => "posLane"
  | .defLane => "defLane"

def reportDiff
  [DecidableEq E]
  [ToString E]
  (a b: Expr E)
  (path: String := "")
:
  Option String
:=
  match a, b with
  | .var infoA xA, .var infoB xB =>
    if infoA != infoB then
      s!"{path}.info: {infoA} != {infoB}"
    else if xA != xB then
      s!"{path}.x: {xA} != {xB}"
    else
      none
  | .bvar xA, .bvar xB =>
    if xA != xB then
      s!"{path}.x: {xA} != {xB}"
    else
      none
  | .null, .null => none
  | .pair aLeft aRite, .pair bLeft bRite =>
    match reportDiff aLeft bLeft (path ++ ".pairL") with
    | some diff => some diff
    | none => reportDiff aRite bRite (path ++ ".pairR")
  | .un aLeft aRite, .un bLeft bRite =>
    match reportDiff aLeft bLeft (path ++ ".unL") with
    | some diff => some diff
    | none => reportDiff aRite bRite (path ++ ".unR")
  | .ir aLeft aRite, .ir bLeft bRite =>
    match reportDiff aLeft bLeft (path ++ ".irL") with
    | some diff => some diff
    | none => reportDiff aRite bRite (path ++ ".irR")
  | .condSome bodyA, .condSome bodyB =>
    reportDiff bodyA bodyB (path ++ ".condSome")
  | .condFull bodyA, .condFull bodyB =>
    reportDiff bodyA bodyB (path ++ ".condFull")
  | .compl exprA, .compl exprB =>
    reportDiff exprA exprB (path ++ ".compl")
  | .arbUn bodyA, .arbUn bodyB =>
    reportDiff bodyA bodyB (path ++ ".arbUn")
  | .arbIr bodyA, .arbIr bodyB =>
    reportDiff bodyA bodyB (path ++ ".arbIr")
  | .var _ _, .bvar _ => s!"{path}: var vs bvar"
  | .var _ _, .null => s!"{path}: var vs null"
  | .var _ _, .pair _ _ => s!"{path}: var vs pair"
  | .var _ _, .un _ _ => s!"{path}: var vs un"
  | .var _ _, .ir _ _ => s!"{path}: var vs ir"
  | .var _ _, .condSome _ => s!"{path}: var vs condSome"
  | .var _ _, .condFull _ => s!"{path}: var vs condFull"
  | .var _ _, .compl _ => s!"{path}: var vs compl"
  | .var _ _, .arbUn _ => s!"{path}: var vs arbUn"
  | .var _ _, .arbIr _ => s!"{path}: var vs arbIr"
  | .bvar _, .var _ _ => s!"{path}: bvar vs var"
  | .bvar _, .null => s!"{path}: bvar vs null"
  | .bvar _, .pair _ _ => s!"{path}: bvar vs pair"
  | .bvar _, .un _ _ => s!"{path}: bvar vs un"
  | .bvar _, .ir _ _ => s!"{path}: bvar vs ir"
  | .bvar _, .condSome _ => s!"{path}: bvar vs condSome"
  | .bvar _, .condFull _ => s!"{path}: bvar vs condFull"
  | .bvar _, .compl _ => s!"{path}: bvar vs compl"
  | .bvar _, .arbUn _ => s!"{path}: bvar vs arbUn"
  | .bvar _, .arbIr _ => s!"{path}: bvar vs arbIr"
  | .null, .var _ _ => s!"{path}: null vs var"
  | .null, .bvar _ => s!"{path}: null vs bvar"
  | .null, .pair _ _ => s!"{path}: null vs pair"
  | .null, .un _ _ => s!"{path}: null vs un"
  | .null, .ir _ _ => s!"{path}: null vs ir"
  | .null, .condSome _ => s!"{path}: null vs condSome"
  | .null, .condFull _ => s!"{path}: null vs condFull"
  | .null, .compl _ => s!"{path}: null vs compl"
  | .null, .arbUn _ => s!"{path}: null vs arbUn"
  | .null, .arbIr _ => s!"{path}: null vs arbIr"
  | .pair _ _, .var _ _ => s!"{path}: pair vs var"
  | .pair _ _, .bvar _ => s!"{path}: pair vs bvar"
  | .pair _ _, .null => s!"{path}: pair vs null"
  | .pair _ _, .un _ _ => s!"{path}: pair vs un"
  | .pair _ _, .ir _ _ => s!"{path}: pair vs ir"
  | .pair _ _, .condSome _ => s!"{path}: pair vs condSome"
  | .pair _ _, .condFull _ => s!"{path}: pair vs condFull"
  | .pair _ _, .compl _ => s!"{path}: pair vs compl"
  | .pair _ _, .arbUn _ => s!"{path}: pair vs arbUn"
  | .pair _ _, .arbIr _ => s!"{path}: pair vs arbIr"
  | .un _ _, .var _ _ => s!"{path}: un vs var"
  | .un _ _, .bvar _ => s!"{path}: un vs bvar"
  | .un _ _, .null => s!"{path}: un vs null"
  | .un _ _, .pair _ _ => s!"{path}: un vs pair"
  | .un _ _, .ir _ _ => s!"{path}: un vs ir"
  | .un _ _, .condSome _ => s!"{path}: un vs condSome"
  | .un _ _, .condFull _ => s!"{path}: un vs condFull"
  | .un _ _, .compl _ => s!"{path}: un vs compl"
  | .un _ _, .arbUn _ => s!"{path}: un vs arbUn"
  | .un _ _, .arbIr _ => s!"{path}: un vs arbIr"
  | .ir _ _, .var _ _ => s!"{path}: ir vs var"
  | .ir _ _, .bvar _ => s!"{path}: ir vs bvar"
  | .ir _ _, .null => s!"{path}: ir vs null"
  | .ir _ _, .pair _ _ => s!"{path}: ir vs pair"
  | .ir _ _, .un _ _ => s!"{path}: ir vs un"
  | .ir _ _, .condSome _ => s!"{path}: ir vs condSome"
  | .ir _ _, .condFull _ => s!"{path}: ir vs condFull"
  | .ir _ _, .compl _ => s!"{path}: ir vs compl"
  | .ir _ _, .arbUn _ => s!"{path}: ir vs arbUn"
  | .ir _ _, .arbIr _ => s!"{path}: ir vs arbIr"
  | .condSome _, .var _ _ => s!"{path}: condSome vs var"
  | .condSome _, .bvar _ => s!"{path}: condSome vs bvar"
  | .condSome _, .null => s!"{path}: condSome vs null"
  | .condSome _, .pair _ _ => s!"{path}: condSome vs pair"
  | .condSome _, .un _ _ => s!"{path}: condSome vs un"
  | .condSome _, .ir _ _ => s!"{path}: condSome vs ir"
  | .condSome _, .condFull _ => s!"{path}: condSome vs condFull"
  | .condSome _, .compl _ => s!"{path}: condSome vs compl"
  | .condSome _, .arbUn _ => s!"{path}: condSome vs arbUn"
  | .condSome _, .arbIr _ => s!"{path}: condSome vs arbIr"
  | .condFull _, .var _ _ => s!"{path}: condFull vs var"
  | .condFull _, .bvar _ => s!"{path}: condFull vs bvar"
  | .condFull _, .null => s!"{path}: condFull vs null"
  | .condFull _, .pair _ _ => s!"{path}: condFull vs pair"
  | .condFull _, .un _ _ => s!"{path}: condFull vs un"
  | .condFull _, .ir _ _ => s!"{path}: condFull vs ir"
  | .condFull _, .condSome _ => s!"{path}: condFull vs condSome"
  | .condFull _, .compl _ => s!"{path}: condFull vs compl"
  | .condFull _, .arbUn _ => s!"{path}: condFull vs arbUn"
  | .condFull _, .arbIr _ => s!"{path}: condFull vs arbIr"
  | .compl _, .var _ _ => s!"{path}: compl vs var"
  | .compl _, .bvar _ => s!"{path}: compl vs bvar"
  | .compl _, .null => s!"{path}: compl vs null"
  | .compl _, .pair _ _ => s!"{path}: compl vs pair"
  | .compl _, .un _ _ => s!"{path}: compl vs un"
  | .compl _, .ir _ _ => s!"{path}: compl vs ir"
  | .compl _, .condSome _ => s!"{path}: compl vs condSome"
  | .compl _, .condFull _ => s!"{path}: compl vs condFull"
  | .compl _, .arbUn _ => s!"{path}: compl vs arbUn"
  | .compl _, .arbIr _ => s!"{path}: compl vs arbIr"
  | .arbUn _, .var _ _ => s!"{path}: arbUn vs var"
  | .arbUn _, .bvar _ => s!"{path}: arbUn vs bvar"
  | .arbUn _, .null => s!"{path}: arbUn vs null"
  | .arbUn _, .pair _ _ => s!"{path}: arbUn vs pair"
  | .arbUn _, .un _ _ => s!"{path}: arbUn vs un"
  | .arbUn _, .ir _ _ => s!"{path}: arbUn vs ir"
  | .arbUn _, .condSome _ => s!"{path}: arbUn vs condSome"
  | .arbUn _, .condFull _ => s!"{path}: arbUn vs condFull"
  | .arbUn _, .compl _ => s!"{path}: arbUn vs compl"
  | .arbUn _, .arbIr _ => s!"{path}: arbUn vs arbIr"
  | .arbIr _, .var _ _ => s!"{path}: arbIr vs var"
  | .arbIr _, .bvar _ => s!"{path}: arbIr vs bvar"
  | .arbIr _, .null => s!"{path}: arbIr vs null"
  | .arbIr _, .pair _ _ => s!"{path}: arbIr vs pair"
  | .arbIr _, .un _ _ => s!"{path}: arbIr vs un"
  | .arbIr _, .ir _ _ => s!"{path}: arbIr vs ir"
  | .arbIr _, .condSome _ => s!"{path}: arbIr vs condSome"
  | .arbIr _, .condFull _ => s!"{path}: arbIr vs condFull"
  | .arbIr _, .compl _ => s!"{path}: arbIr vs compl"
  | .arbIr _, .arbUn _ => s!"{path}: arbIr vs arbUn"
