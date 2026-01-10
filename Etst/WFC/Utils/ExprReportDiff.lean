import Etst.WFC.Utils.PairExpr

namespace Etst


instance: ToString Set3.Lane where
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
  | .df infoA xA, .df infoB xB =>
    if infoA != infoB then
      s!"{path}.info: {infoA} != {infoB}"
    else if xA != xB then
      s!"{path}.x: {xA} != {xB}"
    else
      none
  | .var xA, .var xB =>
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
  | .df _ _, .var _ => s!"{path}: df vs var"
  | .df _ _, .null => s!"{path}: df vs null"
  | .df _ _, .pair _ _ => s!"{path}: df vs pair"
  | .df _ _, .un _ _ => s!"{path}: df vs un"
  | .df _ _, .ir _ _ => s!"{path}: df vs ir"
  | .df _ _, .condSome _ => s!"{path}: df vs condSome"
  | .df _ _, .condFull _ => s!"{path}: df vs condFull"
  | .df _ _, .compl _ => s!"{path}: df vs compl"
  | .df _ _, .arbUn _ => s!"{path}: df vs arbUn"
  | .df _ _, .arbIr _ => s!"{path}: df vs arbIr"
  | .var _, .df _ _ => s!"{path}: var vs df"
  | .var _, .null => s!"{path}: var vs null"
  | .var _, .pair _ _ => s!"{path}: var vs pair"
  | .var _, .un _ _ => s!"{path}: var vs un"
  | .var _, .ir _ _ => s!"{path}: var vs ir"
  | .var _, .condSome _ => s!"{path}: var vs condSome"
  | .var _, .condFull _ => s!"{path}: var vs condFull"
  | .var _, .compl _ => s!"{path}: var vs compl"
  | .var _, .arbUn _ => s!"{path}: var vs arbUn"
  | .var _, .arbIr _ => s!"{path}: var vs arbIr"
  | .null, .df _ _ => s!"{path}: null vs df"
  | .null, .var _ => s!"{path}: null vs var"
  | .null, .pair _ _ => s!"{path}: null vs pair"
  | .null, .un _ _ => s!"{path}: null vs un"
  | .null, .ir _ _ => s!"{path}: null vs ir"
  | .null, .condSome _ => s!"{path}: null vs condSome"
  | .null, .condFull _ => s!"{path}: null vs condFull"
  | .null, .compl _ => s!"{path}: null vs compl"
  | .null, .arbUn _ => s!"{path}: null vs arbUn"
  | .null, .arbIr _ => s!"{path}: null vs arbIr"
  | .pair _ _, .df _ _ => s!"{path}: pair vs df"
  | .pair _ _, .var _ => s!"{path}: pair vs var"
  | .pair _ _, .null => s!"{path}: pair vs null"
  | .pair _ _, .un _ _ => s!"{path}: pair vs un"
  | .pair _ _, .ir _ _ => s!"{path}: pair vs ir"
  | .pair _ _, .condSome _ => s!"{path}: pair vs condSome"
  | .pair _ _, .condFull _ => s!"{path}: pair vs condFull"
  | .pair _ _, .compl _ => s!"{path}: pair vs compl"
  | .pair _ _, .arbUn _ => s!"{path}: pair vs arbUn"
  | .pair _ _, .arbIr _ => s!"{path}: pair vs arbIr"
  | .un _ _, .df _ _ => s!"{path}: un vs df"
  | .un _ _, .var _ => s!"{path}: un vs var"
  | .un _ _, .null => s!"{path}: un vs null"
  | .un _ _, .pair _ _ => s!"{path}: un vs pair"
  | .un _ _, .ir _ _ => s!"{path}: un vs ir"
  | .un _ _, .condSome _ => s!"{path}: un vs condSome"
  | .un _ _, .condFull _ => s!"{path}: un vs condFull"
  | .un _ _, .compl _ => s!"{path}: un vs compl"
  | .un _ _, .arbUn _ => s!"{path}: un vs arbUn"
  | .un _ _, .arbIr _ => s!"{path}: un vs arbIr"
  | .ir _ _, .df _ _ => s!"{path}: ir vs df"
  | .ir _ _, .var _ => s!"{path}: ir vs var"
  | .ir _ _, .null => s!"{path}: ir vs null"
  | .ir _ _, .pair _ _ => s!"{path}: ir vs pair"
  | .ir _ _, .un _ _ => s!"{path}: ir vs un"
  | .ir _ _, .condSome _ => s!"{path}: ir vs condSome"
  | .ir _ _, .condFull _ => s!"{path}: ir vs condFull"
  | .ir _ _, .compl _ => s!"{path}: ir vs compl"
  | .ir _ _, .arbUn _ => s!"{path}: ir vs arbUn"
  | .ir _ _, .arbIr _ => s!"{path}: ir vs arbIr"
  | .condSome _, .df _ _ => s!"{path}: condSome vs df"
  | .condSome _, .var _ => s!"{path}: condSome vs var"
  | .condSome _, .null => s!"{path}: condSome vs null"
  | .condSome _, .pair _ _ => s!"{path}: condSome vs pair"
  | .condSome _, .un _ _ => s!"{path}: condSome vs un"
  | .condSome _, .ir _ _ => s!"{path}: condSome vs ir"
  | .condSome _, .condFull _ => s!"{path}: condSome vs condFull"
  | .condSome _, .compl _ => s!"{path}: condSome vs compl"
  | .condSome _, .arbUn _ => s!"{path}: condSome vs arbUn"
  | .condSome _, .arbIr _ => s!"{path}: condSome vs arbIr"
  | .condFull _, .df _ _ => s!"{path}: condFull vs df"
  | .condFull _, .var _ => s!"{path}: condFull vs var"
  | .condFull _, .null => s!"{path}: condFull vs null"
  | .condFull _, .pair _ _ => s!"{path}: condFull vs pair"
  | .condFull _, .un _ _ => s!"{path}: condFull vs un"
  | .condFull _, .ir _ _ => s!"{path}: condFull vs ir"
  | .condFull _, .condSome _ => s!"{path}: condFull vs condSome"
  | .condFull _, .compl _ => s!"{path}: condFull vs compl"
  | .condFull _, .arbUn _ => s!"{path}: condFull vs arbUn"
  | .condFull _, .arbIr _ => s!"{path}: condFull vs arbIr"
  | .compl _, .df _ _ => s!"{path}: compl vs df"
  | .compl _, .var _ => s!"{path}: compl vs var"
  | .compl _, .null => s!"{path}: compl vs null"
  | .compl _, .pair _ _ => s!"{path}: compl vs pair"
  | .compl _, .un _ _ => s!"{path}: compl vs un"
  | .compl _, .ir _ _ => s!"{path}: compl vs ir"
  | .compl _, .condSome _ => s!"{path}: compl vs condSome"
  | .compl _, .condFull _ => s!"{path}: compl vs condFull"
  | .compl _, .arbUn _ => s!"{path}: compl vs arbUn"
  | .compl _, .arbIr _ => s!"{path}: compl vs arbIr"
  | .arbUn _, .df _ _ => s!"{path}: arbUn vs df"
  | .arbUn _, .var _ => s!"{path}: arbUn vs var"
  | .arbUn _, .null => s!"{path}: arbUn vs null"
  | .arbUn _, .pair _ _ => s!"{path}: arbUn vs pair"
  | .arbUn _, .un _ _ => s!"{path}: arbUn vs un"
  | .arbUn _, .ir _ _ => s!"{path}: arbUn vs ir"
  | .arbUn _, .condSome _ => s!"{path}: arbUn vs condSome"
  | .arbUn _, .condFull _ => s!"{path}: arbUn vs condFull"
  | .arbUn _, .compl _ => s!"{path}: arbUn vs compl"
  | .arbUn _, .arbIr _ => s!"{path}: arbUn vs arbIr"
  | .arbIr _, .df _ _ => s!"{path}: arbIr vs df"
  | .arbIr _, .var _ => s!"{path}: arbIr vs var"
  | .arbIr _, .null => s!"{path}: arbIr vs null"
  | .arbIr _, .pair _ _ => s!"{path}: arbIr vs pair"
  | .arbIr _, .un _ _ => s!"{path}: arbIr vs un"
  | .arbIr _, .ir _ _ => s!"{path}: arbIr vs ir"
  | .arbIr _, .condSome _ => s!"{path}: arbIr vs condSome"
  | .arbIr _, .condFull _ => s!"{path}: arbIr vs condFull"
  | .arbIr _, .compl _ => s!"{path}: arbIr vs compl"
  | .arbIr _, .arbUn _ => s!"{path}: arbIr vs arbUn"
