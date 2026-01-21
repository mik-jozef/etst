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
  | .un _ _, .some _ => s!"{path}: un vs some"
  | .un _ _, .arbUn _ => s!"{path}: un vs arbUn"
  | .un _ _, .const _ _ => s!"{path}: un vs const"
  | .un _ _, .var _ => s!"{path}: un vs var"
  | .un _ _, .null => s!"{path}: un vs null"
  | .un _ _, .pair _ _ => s!"{path}: un vs pair"
  | .un _ _, .ir _ _ => s!"{path}: un vs ir"
  | .un _ _, .full _ => s!"{path}: un vs full"
  | .un _ _, .arbIr _ => s!"{path}: un vs arbIr"
  | .some _, .un _ _ => s!"{path}: some vs un"
  | .some _, .arbUn _ => s!"{path}: some vs arbUn"
  | .some _, .const _ _ => s!"{path}: some vs const"
  | .some _, .var _ => s!"{path}: some vs var"
  | .some _, .null => s!"{path}: some vs null"
  | .some _, .pair _ _ => s!"{path}: some vs pair"
  | .some _, .ir _ _ => s!"{path}: some vs ir"
  | .some _, .full _ => s!"{path}: some vs full"
  | .some _, .arbIr _ => s!"{path}: some vs arbIr"
  | .arbUn _, .un _ _ => s!"{path}: arbUn vs un"
  | .arbUn _, .some _ => s!"{path}: arbUn vs some"
  | .arbUn _, .const _ _ => s!"{path}: arbUn vs const"
  | .arbUn _, .var _ => s!"{path}: arbUn vs var"
  | .arbUn _, .null => s!"{path}: arbUn vs null"
  | .arbUn _, .pair _ _ => s!"{path}: arbUn vs pair"
  | .arbUn _, .ir _ _ => s!"{path}: arbUn vs ir"
  | .arbUn _, .full _ => s!"{path}: arbUn vs full"
  | .arbUn _, .arbIr _ => s!"{path}: arbUn vs arbIr"
  | .un aLeft aRite, .un bLeft bRite =>
    match reportDiff aLeft bLeft (path ++ ".unL") with
    | some diff => some diff
    | none => reportDiff aRite bRite (path ++ ".unR")
  | .some bodyA, .some bodyB =>
    reportDiff bodyA bodyB (path ++ ".some")
  | .arbUn bodyA, .arbUn bodyB =>
    reportDiff bodyA bodyB (path ++ ".arbUn")
  | .un _ _, .compl _ => s!"{path}: un vs compl"
  | .some _, .compl _ => s!"{path}: some vs compl"
  | .arbUn _, .compl _ => s!"{path}: arbUn vs compl"
  | .compl _, .un _ _ => s!"{path}: compl vs un"
  | .compl _, .some _ => s!"{path}: compl vs some"
  | .compl _, .arbUn _ => s!"{path}: compl vs arbUn"
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
  | .ir aLeft aRite, .ir bLeft bRite =>
    match reportDiff aLeft bLeft (path ++ ".irL") with
    | some diff => some diff
    | none => reportDiff aRite bRite (path ++ ".irR")
  | .full bodyA, .full bodyB =>
    reportDiff bodyA bodyB (path ++ ".full")
  | .compl exprA, .compl exprB =>
    reportDiff exprA exprB (path ++ ".compl")
  | .arbIr bodyA, .arbIr bodyB =>
    reportDiff bodyA bodyB (path ++ ".arbIr")
  | .const _ _, .un _ _ => s!"{path}: const vs un"
  | .const _ _, .some _ => s!"{path}: const vs some"
  | .const _ _, .arbUn _ => s!"{path}: const vs arbUn"
  | .const _ _, .var _ => s!"{path}: const vs var"
  | .const _ _, .null => s!"{path}: const vs null"
  | .const _ _, .pair _ _ => s!"{path}: const vs pair"
  | .const _ _, .ir _ _ => s!"{path}: const vs ir"
  | .const _ _, .full _ => s!"{path}: const vs full"
  | .const _ _, .compl _ => s!"{path}: const vs compl"
  | .const _ _, .arbIr _ => s!"{path}: const vs arbIr"
  | .var _, .un _ _ => s!"{path}: var vs un"
  | .var _, .arbUn _ => s!"{path}: var vs arbUn"
  | .var _, .const _ _ => s!"{path}: var vs const"
  | .var _, .null => s!"{path}: var vs null"
  | .var _, .pair _ _ => s!"{path}: var vs pair"
  | .var _, .ir _ _ => s!"{path}: var vs ir"
  | .var _, .some _ => s!"{path}: var vs some"
  | .var _, .full _ => s!"{path}: var vs full"
  | .var _, .compl _ => s!"{path}: var vs compl"
  | .var _, .arbIr _ => s!"{path}: var vs arbIr"
  | .null, .un _ _ => s!"{path}: null vs un"
  | .null, .some _ => s!"{path}: null vs some"
  | .null, .arbUn _ => s!"{path}: null vs arbUn"
  | .null, .const _ _ => s!"{path}: null vs const"
  | .null, .var _ => s!"{path}: null vs var"
  | .null, .pair _ _ => s!"{path}: null vs pair"
  | .null, .ir _ _ => s!"{path}: null vs ir"
  | .null, .full _ => s!"{path}: null vs full"
  | .null, .compl _ => s!"{path}: null vs compl"
  | .null, .arbIr _ => s!"{path}: null vs arbIr"
  | .pair _ _, .un _ _ => s!"{path}: pair vs un"
  | .pair _ _, .some _ => s!"{path}: pair vs some"
  | .pair _ _, .arbUn _ => s!"{path}: pair vs arbUn"
  | .pair _ _, .const _ _ => s!"{path}: pair vs const"
  | .pair _ _, .var _ => s!"{path}: pair vs var"
  | .pair _ _, .null => s!"{path}: pair vs null"
  | .pair _ _, .ir _ _ => s!"{path}: pair vs ir"
  | .pair _ _, .full _ => s!"{path}: pair vs full"
  | .pair _ _, .compl _ => s!"{path}: pair vs compl"
  | .pair _ _, .arbIr _ => s!"{path}: pair vs arbIr"
  | .ir _ _, .un _ _ => s!"{path}: ir vs un"
  | .ir _ _, .some _ => s!"{path}: ir vs some"
  | .ir _ _, .arbUn _ => s!"{path}: ir vs arbUn"
  | .ir _ _, .const _ _ => s!"{path}: ir vs const"
  | .ir _ _, .var _ => s!"{path}: ir vs var"
  | .ir _ _, .null => s!"{path}: ir vs null"
  | .ir _ _, .pair _ _ => s!"{path}: ir vs pair"
  | .ir _ _, .full _ => s!"{path}: ir vs full"
  | .ir _ _, .compl _ => s!"{path}: ir vs compl"
  | .ir _ _, .arbIr _ => s!"{path}: ir vs arbIr"
  | .full _, .un _ _ => s!"{path}: full vs un"
  | .full _, .some _ => s!"{path}: full vs some"
  | .full _, .arbUn _ => s!"{path}: full vs arbUn"
  | .full _, .const _ _ => s!"{path}: full vs const"
  | .full _, .var _ => s!"{path}: full vs var"
  | .full _, .null => s!"{path}: full vs null"
  | .full _, .pair _ _ => s!"{path}: full vs pair"
  | .full _, .ir _ _ => s!"{path}: full vs ir"
  | .full _, .compl _ => s!"{path}: full vs compl"
  | .full _, .arbIr _ => s!"{path}: full vs arbIr"
  | .compl _, .const _ _ => s!"{path}: compl vs const"
  | .compl _, .var _ => s!"{path}: compl vs var"
  | .compl _, .null => s!"{path}: compl vs null"
  | .compl _, .pair _ _ => s!"{path}: compl vs pair"
  | .compl _, .ir _ _ => s!"{path}: compl vs ir"
  | .compl _, .full _ => s!"{path}: compl vs full"
  | .compl _, .arbIr _ => s!"{path}: compl vs arbIr"
  | .arbIr _, .un _ _ => s!"{path}: arbIr vs un"
  | .arbIr _, .some _ => s!"{path}: arbIr vs some"
  | .arbIr _, .arbUn _ => s!"{path}: arbIr vs arbUn"
  | .arbIr _, .const _ _ => s!"{path}: arbIr vs const"
  | .arbIr _, .var _ => s!"{path}: arbIr vs var"
  | .arbIr _, .null => s!"{path}: arbIr vs null"
  | .arbIr _, .pair _ _ => s!"{path}: arbIr vs pair"
  | .arbIr _, .ir _ _ => s!"{path}: arbIr vs ir"
  | .arbIr _, .full _ => s!"{path}: arbIr vs full"
  | .arbIr _, .compl _ => s!"{path}: arbIr vs compl"
