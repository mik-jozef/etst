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
  | .const infoA xA, .const infoB xB =>
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
  | .const _ _, .const _ => s!"{path}: const vs const"
  | .const _ _, .null => s!"{path}: const vs null"
  | .const _ _, .pair _ _ => s!"{path}: const vs pair"
  | .const _ _, .un _ _ => s!"{path}: const vs un"
  | .const _ _, .ir _ _ => s!"{path}: const vs ir"
  | .const _ _, .condSome _ => s!"{path}: const vs condSome"
  | .const _ _, .condFull _ => s!"{path}: const vs condFull"
  | .const _ _, .compl _ => s!"{path}: const vs compl"
  | .const _ _, .arbUn _ => s!"{path}: const vs arbUn"
  | .const _ _, .arbIr _ => s!"{path}: const vs arbIr"
  | .var _, .const _ _ => s!"{path}: const vs const"
  | .var _, .null => s!"{path}: const vs null"
  | .var _, .pair _ _ => s!"{path}: const vs pair"
  | .var _, .un _ _ => s!"{path}: const vs un"
  | .var _, .ir _ _ => s!"{path}: const vs ir"
  | .var _, .condSome _ => s!"{path}: const vs condSome"
  | .var _, .condFull _ => s!"{path}: const vs condFull"
  | .var _, .compl _ => s!"{path}: const vs compl"
  | .var _, .arbUn _ => s!"{path}: const vs arbUn"
  | .var _, .arbIr _ => s!"{path}: const vs arbIr"
  | .null, .var _ _ => s!"{path}: null vs const"
  | .null, .var _ => s!"{path}: null vs const"
  | .null, .pair _ _ => s!"{path}: null vs pair"
  | .null, .un _ _ => s!"{path}: null vs un"
  | .null, .ir _ _ => s!"{path}: null vs ir"
  | .null, .condSome _ => s!"{path}: null vs condSome"
  | .null, .condFull _ => s!"{path}: null vs condFull"
  | .null, .compl _ => s!"{path}: null vs compl"
  | .null, .arbUn _ => s!"{path}: null vs arbUn"
  | .null, .arbIr _ => s!"{path}: null vs arbIr"
  | .pair _ _, .var _ _ => s!"{path}: pair vs const"
  | .pair _ _, .var _ => s!"{path}: pair vs const"
  | .pair _ _, .null => s!"{path}: pair vs null"
  | .pair _ _, .un _ _ => s!"{path}: pair vs un"
  | .pair _ _, .ir _ _ => s!"{path}: pair vs ir"
  | .pair _ _, .condSome _ => s!"{path}: pair vs condSome"
  | .pair _ _, .condFull _ => s!"{path}: pair vs condFull"
  | .pair _ _, .compl _ => s!"{path}: pair vs compl"
  | .pair _ _, .arbUn _ => s!"{path}: pair vs arbUn"
  | .pair _ _, .arbIr _ => s!"{path}: pair vs arbIr"
  | .un _ _, .var _ _ => s!"{path}: un vs const"
  | .un _ _, .var _ => s!"{path}: un vs const"
  | .un _ _, .null => s!"{path}: un vs null"
  | .un _ _, .pair _ _ => s!"{path}: un vs pair"
  | .un _ _, .ir _ _ => s!"{path}: un vs ir"
  | .un _ _, .condSome _ => s!"{path}: un vs condSome"
  | .un _ _, .condFull _ => s!"{path}: un vs condFull"
  | .un _ _, .compl _ => s!"{path}: un vs compl"
  | .un _ _, .arbUn _ => s!"{path}: un vs arbUn"
  | .un _ _, .arbIr _ => s!"{path}: un vs arbIr"
  | .ir _ _, .var _ _ => s!"{path}: ir vs const"
  | .ir _ _, .var _ => s!"{path}: ir vs const"
  | .ir _ _, .null => s!"{path}: ir vs null"
  | .ir _ _, .pair _ _ => s!"{path}: ir vs pair"
  | .ir _ _, .un _ _ => s!"{path}: ir vs un"
  | .ir _ _, .condSome _ => s!"{path}: ir vs condSome"
  | .ir _ _, .condFull _ => s!"{path}: ir vs condFull"
  | .ir _ _, .compl _ => s!"{path}: ir vs compl"
  | .ir _ _, .arbUn _ => s!"{path}: ir vs arbUn"
  | .ir _ _, .arbIr _ => s!"{path}: ir vs arbIr"
  | .condSome _, .var _ _ => s!"{path}: condSome vs const"
  | .condSome _, .var _ => s!"{path}: condSome vs const"
  | .condSome _, .null => s!"{path}: condSome vs null"
  | .condSome _, .pair _ _ => s!"{path}: condSome vs pair"
  | .condSome _, .un _ _ => s!"{path}: condSome vs un"
  | .condSome _, .ir _ _ => s!"{path}: condSome vs ir"
  | .condSome _, .condFull _ => s!"{path}: condSome vs condFull"
  | .condSome _, .compl _ => s!"{path}: condSome vs compl"
  | .condSome _, .arbUn _ => s!"{path}: condSome vs arbUn"
  | .condSome _, .arbIr _ => s!"{path}: condSome vs arbIr"
  | .condFull _, .var _ _ => s!"{path}: condFull vs const"
  | .condFull _, .var _ => s!"{path}: condFull vs const"
  | .condFull _, .null => s!"{path}: condFull vs null"
  | .condFull _, .pair _ _ => s!"{path}: condFull vs pair"
  | .condFull _, .un _ _ => s!"{path}: condFull vs un"
  | .condFull _, .ir _ _ => s!"{path}: condFull vs ir"
  | .condFull _, .condSome _ => s!"{path}: condFull vs condSome"
  | .condFull _, .compl _ => s!"{path}: condFull vs compl"
  | .condFull _, .arbUn _ => s!"{path}: condFull vs arbUn"
  | .condFull _, .arbIr _ => s!"{path}: condFull vs arbIr"
  | .compl _, .var _ _ => s!"{path}: compl vs const"
  | .compl _, .var _ => s!"{path}: compl vs const"
  | .compl _, .null => s!"{path}: compl vs null"
  | .compl _, .pair _ _ => s!"{path}: compl vs pair"
  | .compl _, .un _ _ => s!"{path}: compl vs un"
  | .compl _, .ir _ _ => s!"{path}: compl vs ir"
  | .compl _, .condSome _ => s!"{path}: compl vs condSome"
  | .compl _, .condFull _ => s!"{path}: compl vs condFull"
  | .compl _, .arbUn _ => s!"{path}: compl vs arbUn"
  | .compl _, .arbIr _ => s!"{path}: compl vs arbIr"
  | .arbUn _, .var _ _ => s!"{path}: arbUn vs const"
  | .arbUn _, .var _ => s!"{path}: arbUn vs const"
  | .arbUn _, .null => s!"{path}: arbUn vs null"
  | .arbUn _, .pair _ _ => s!"{path}: arbUn vs pair"
  | .arbUn _, .un _ _ => s!"{path}: arbUn vs un"
  | .arbUn _, .ir _ _ => s!"{path}: arbUn vs ir"
  | .arbUn _, .condSome _ => s!"{path}: arbUn vs condSome"
  | .arbUn _, .condFull _ => s!"{path}: arbUn vs condFull"
  | .arbUn _, .compl _ => s!"{path}: arbUn vs compl"
  | .arbUn _, .arbIr _ => s!"{path}: arbUn vs arbIr"
  | .arbIr _, .var _ _ => s!"{path}: arbIr vs const"
  | .arbIr _, .var _ => s!"{path}: arbIr vs const"
  | .arbIr _, .null => s!"{path}: arbIr vs null"
  | .arbIr _, .pair _ _ => s!"{path}: arbIr vs pair"
  | .arbIr _, .un _ _ => s!"{path}: arbIr vs un"
  | .arbIr _, .ir _ _ => s!"{path}: arbIr vs ir"
  | .arbIr _, .condSome _ => s!"{path}: arbIr vs condSome"
  | .arbIr _, .condFull _ => s!"{path}: arbIr vs condFull"
  | .arbIr _, .compl _ => s!"{path}: arbIr vs compl"
  | .arbIr _, .arbUn _ => s!"{path}: arbIr vs arbUn"
