import Etst.WFC.Utils.PairExpr

namespace Etst

namespace PairExpr
  instance decidePairExprEq
    [DecidableEq E]
    (a b: Expr E pairSignature)
  :
    Decidable (a = b)
  :=
    match a, b with
    | .var infoA xA, .var infoB xB =>
      if h: infoA = infoB ∧ xA = xB then
        let ⟨hi, hx⟩ := h
        isTrue (hi ▸ hx ▸ rfl)
      else
        isFalse (fun eq => h (Expr.noConfusion eq And.intro))
    | .bvar xA, .bvar xB =>
      if h: xA = xB then
        isTrue (h ▸ rfl)
      else
        isFalse (fun eq => h (Expr.noConfusion eq id))
    | .op .null _, .op .null _ => isTrue null_eq
    | .op .pair argsA, .op .pair argsB =>
      let ihZth := decidePairExprEq (argsA .zth) (argsB .zth)
      let ihFst := decidePairExprEq (argsA .fst) (argsB .fst)
      match ihZth, ihFst with
      | isTrue hZth, isTrue hFst =>
        isTrue (congr rfl (funext (fun
          | .zth => hZth
          | .fst => hFst)))
      | isFalse nZth, _ =>
        isFalse (fun eq =>
          nZth (congr (Expr.eq_args_of_eq_op eq) rfl))
      | _, isFalse nFst =>
        isFalse (fun eq =>
          nFst (congr (Expr.eq_args_of_eq_op eq) rfl))
    | .op .un argsA, .op .un argsB =>
      let ihZth := decidePairExprEq (argsA .zth) (argsB .zth)
      let ihFst := decidePairExprEq (argsA .fst) (argsB .fst)
      match ihZth, ihFst with
      | isTrue hZth, isTrue hFst =>
        isTrue (congr rfl (funext (fun
          | .zth => hZth
          | .fst => hFst)))
      | isFalse nZth, _ =>
        isFalse (fun eq =>
          nZth (congr (Expr.eq_args_of_eq_op eq) rfl))
      | _, isFalse nFst =>
        isFalse (fun eq =>
          nFst (congr (Expr.eq_args_of_eq_op eq) rfl))
    | .op .ir argsA, .op .ir argsB =>
      let ihZth := decidePairExprEq (argsA .zth) (argsB .zth)
      let ihFst := decidePairExprEq (argsA .fst) (argsB .fst)
      match ihZth, ihFst with
      | isTrue hZth, isTrue hFst =>
        isTrue (congr rfl (funext (fun
          | .zth => hZth
          | .fst => hFst)))
      | isFalse nZth, _ =>
        isFalse (fun eq =>
          nZth (congr (Expr.eq_args_of_eq_op eq) rfl))
      | _, isFalse nFst =>
        isFalse (fun eq =>
          nFst (congr (Expr.eq_args_of_eq_op eq) rfl))
    | .op .condSome argsA, .op .condSome argsB =>
      let ih := decidePairExprEq (argsA .zth) (argsB .zth)
      match ih with
      | isTrue h =>
        isTrue (congr rfl (funext (fun _ => h)))
      | isFalse n =>
        isFalse (fun eq =>
          n (congr (Expr.eq_args_of_eq_op eq) rfl))
    | .op .condFull argsA, .op .condFull argsB =>
      let ih := decidePairExprEq (argsA .zth) (argsB .zth)
      match ih with
      | isTrue h =>
        isTrue (congr rfl (funext (fun _ => h)))
      | isFalse n =>
        isFalse (fun eq =>
          n (congr (Expr.eq_args_of_eq_op eq) rfl))
    | .compl exprA, .compl exprB =>
      match decidePairExprEq exprA exprB with
      | isTrue h => isTrue (congr rfl h)
      | isFalse n =>
        isFalse (fun eq => n (Expr.noConfusion eq id))
    | .arbUn bodyA, .arbUn bodyB =>
      match decidePairExprEq bodyA bodyB with
      | isTrue h => isTrue (congr rfl h)
      | isFalse n =>
        isFalse (fun eq => n (Expr.noConfusion eq id))
    | .arbIr bodyA, .arbIr bodyB =>
      match decidePairExprEq bodyA bodyB with
      | isTrue h => isTrue (congr rfl h)
      | isFalse n =>
        isFalse (fun eq => n (Expr.noConfusion eq id))
    | .var _ _, .bvar _ => isFalse Expr.noConfusion
    | .var _ _, .op _ _ => isFalse Expr.noConfusion
    | .var _ _, .compl _ => isFalse Expr.noConfusion
    | .var _ _, .arbUn _ => isFalse Expr.noConfusion
    | .var _ _, .arbIr _ => isFalse Expr.noConfusion
    | .bvar _, .var _ _ => isFalse Expr.noConfusion
    | .bvar _, .op _ _ => isFalse Expr.noConfusion
    | .bvar _, .compl _ => isFalse Expr.noConfusion
    | .bvar _, .arbUn _ => isFalse Expr.noConfusion
    | .bvar _, .arbIr _ => isFalse Expr.noConfusion
    | .op _ _, .var _ _ => isFalse Expr.noConfusion
    | .op _ _, .bvar _ => isFalse Expr.noConfusion
    | .op _ _, .compl _ => isFalse Expr.noConfusion
    | .op _ _, .arbUn _ => isFalse Expr.noConfusion
    | .op _ _, .arbIr _ => isFalse Expr.noConfusion
    | .compl _, .var _ _ => isFalse Expr.noConfusion
    | .compl _, .bvar _ => isFalse Expr.noConfusion
    | .compl _, .op _ _ => isFalse Expr.noConfusion
    | .compl _, .arbUn _ => isFalse Expr.noConfusion
    | .compl _, .arbIr _ => isFalse Expr.noConfusion
    | .arbUn _, .var _ _ => isFalse Expr.noConfusion
    | .arbUn _, .bvar _ => isFalse Expr.noConfusion
    | .arbUn _, .op _ _ => isFalse Expr.noConfusion
    | .arbUn _, .compl _ => isFalse Expr.noConfusion
    | .arbUn _, .arbIr _ => isFalse Expr.noConfusion
    | .arbIr _, .var _ _ => isFalse Expr.noConfusion
    | .arbIr _, .bvar _ => isFalse Expr.noConfusion
    | .arbIr _, .op _ _ => isFalse Expr.noConfusion
    | .arbIr _, .compl _ => isFalse Expr.noConfusion
    | .arbIr _, .arbUn _ => isFalse Expr.noConfusion
    | .op .null _, .op .pair _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .null _, .op .un _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .null _, .op .ir _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .null _, .op .condSome _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .null _, .op .condFull _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .pair _, .op .null _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .pair _, .op .un _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .pair _, .op .ir _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .pair _, .op .condSome _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .pair _, .op .condFull _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .un _, .op .null _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .un _, .op .pair _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .un _, .op .ir _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .un _, .op .condSome _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .un _, .op .condFull _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .ir _, .op .null _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .ir _, .op .pair _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .ir _, .op .un _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .ir _, .op .condSome _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .ir _, .op .condFull _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condSome _, .op .null _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condSome _, .op .pair _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condSome _, .op .un _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condSome _, .op .ir _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condSome _, .op .condFull _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condFull _, .op .null _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condFull _, .op .pair _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condFull _, .op .un _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condFull _, .op .ir _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)
    | .op .condFull _, .op .condSome _ =>
      isFalse (fun eq =>
        let opEq := Expr.noConfusion eq (Function.const _)
        pairSignature.Op.noConfusion opEq)


instance: ToString SingleLaneVarType where
  toString
  | .posLane => "posLane"
  | .defLane => "defLane"

def reportDiff
  [DecidableEq E]
  [ToString E]
  (a b: Expr E pairSignature)
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
  | .op .null _, .op .null _ => none
  | .op .pair argsA, .op .pair argsB =>
    match reportDiff (argsA .zth) (argsB .zth) (path ++ ".pairL") with
    | some diff => some diff
    | none => reportDiff (argsA .fst) (argsB .fst) (path ++ ".pairR")
  | .op .un argsA, .op .un argsB =>
    match reportDiff (argsA .zth) (argsB .zth) (path ++ ".unL") with
    | some diff => some diff
    | none => reportDiff (argsA .fst) (argsB .fst) (path ++ ".unR")
  | .op .ir argsA, .op .ir argsB =>
    match reportDiff (argsA .zth) (argsB .zth) (path ++ ".irL") with
    | some diff => some diff
    | none => reportDiff (argsA .fst) (argsB .fst) (path ++ ".irR")
  | .op .condSome argsA, .op .condSome argsB =>
    reportDiff (argsA .zth) (argsB .zth) (path ++ ".condSome")
  | .op .condFull argsA, .op .condFull argsB =>
    reportDiff (argsA .zth) (argsB .zth) (path ++ ".condFull")
  | .compl exprA, .compl exprB =>
    reportDiff exprA exprB (path ++ ".compl")
  | .arbUn bodyA, .arbUn bodyB =>
    reportDiff bodyA bodyB (path ++ ".arbUn")
  | .arbIr bodyA, .arbIr bodyB =>
    reportDiff bodyA bodyB (path ++ ".arbIr")
  | .var _ _, .bvar _ => s!"{path}: var vs bvar"
  | .var _ _, .op _ _ => s!"{path}: var vs op"
  | .var _ _, .compl _ => s!"{path}: var vs compl"
  | .var _ _, .arbUn _ => s!"{path}: var vs arbUn"
  | .var _ _, .arbIr _ => s!"{path}: var vs arbIr"
  | .bvar _, .var _ _ => s!"{path}: bvar vs var"
  | .bvar _, .op _ _ => s!"{path}: bvar vs op"
  | .bvar _, .compl _ => s!"{path}: bvar vs compl"
  | .bvar _, .arbUn _ => s!"{path}: bvar vs arbUn"
  | .bvar _, .arbIr _ => s!"{path}: bvar vs arbIr"
  | .op _ _, .var _ _ => s!"{path}: op vs var"
  | .op _ _, .bvar _ => s!"{path}: op vs bvar"
  | .op _ _, .compl _ => s!"{path}: op vs compl"
  | .op _ _, .arbUn _ => s!"{path}: op vs arbUn"
  | .op _ _, .arbIr _ => s!"{path}: op vs arbIr"
  | .compl _, .var _ _ => s!"{path}: compl vs var"
  | .compl _, .bvar _ => s!"{path}: compl vs bvar"
  | .compl _, .op _ _ => s!"{path}: compl vs op"
  | .compl _, .arbUn _ => s!"{path}: compl vs arbUn"
  | .compl _, .arbIr _ => s!"{path}: compl vs arbIr"
  | .arbUn _, .var _ _ => s!"{path}: arbUn vs var"
  | .arbUn _, .bvar _ => s!"{path}: arbUn vs bvar"
  | .arbUn _, .op _ _ => s!"{path}: arbUn vs op"
  | .arbUn _, .compl _ => s!"{path}: arbUn vs compl"
  | .arbUn _, .arbIr _ => s!"{path}: arbUn vs arbIr"
  | .arbIr _, .var _ _ => s!"{path}: arbIr vs var"
  | .arbIr _, .bvar _ => s!"{path}: arbIr vs bvar"
  | .arbIr _, .op _ _ => s!"{path}: arbIr vs op"
  | .arbIr _, .compl _ => s!"{path}: arbIr vs compl"
  | .arbIr _, .arbUn _ => s!"{path}: arbIr vs arbUn"
  | .op .null _, .op .pair _ => s!"{path}: null vs pair"
  | .op .null _, .op .un _ => s!"{path}: null vs un"
  | .op .null _, .op .ir _ => s!"{path}: null vs ir"
  | .op .null _, .op .condSome _ => s!"{path}: null vs condSome"
  | .op .null _, .op .condFull _ => s!"{path}: null vs condFull"
  | .op .pair _, .op .null _ => s!"{path}: pair vs null"
  | .op .pair _, .op .un _ => s!"{path}: pair vs un"
  | .op .pair _, .op .ir _ => s!"{path}: pair vs ir"
  | .op .pair _, .op .condSome _ => s!"{path}: pair vs condSome"
  | .op .pair _, .op .condFull _ => s!"{path}: pair vs condFull"
  | .op .un _, .op .null _ => s!"{path}: un vs null"
  | .op .un _, .op .pair _ => s!"{path}: un vs pair"
  | .op .un _, .op .ir _ => s!"{path}: un vs ir"
  | .op .un _, .op .condSome _ => s!"{path}: un vs condSome"
  | .op .un _, .op .condFull _ => s!"{path}: un vs condFull"
  | .op .ir _, .op .null _ => s!"{path}: ir vs null"
  | .op .ir _, .op .pair _ => s!"{path}: ir vs pair"
  | .op .ir _, .op .un _ => s!"{path}: ir vs un"
  | .op .ir _, .op .condSome _ => s!"{path}: ir vs condSome"
  | .op .ir _, .op .condFull _ => s!"{path}: ir vs condFull"
  | .op .condSome _, .op .null _ => s!"{path}: condSome vs null"
  | .op .condSome _, .op .pair _ => s!"{path}: condSome vs pair"
  | .op .condSome _, .op .un _ => s!"{path}: condSome vs un"
  | .op .condSome _, .op .ir _ => s!"{path}: condSome vs ir"
  | .op .condSome _, .op .condFull _ => s!"{path}: condSome vs condFull"
  | .op .condFull _, .op .null _ => s!"{path}: condFull vs null"
  | .op .condFull _, .op .pair _ => s!"{path}: condFull vs pair"
  | .op .condFull _, .op .un _ => s!"{path}: condFull vs un"
  | .op .condFull _, .op .ir _ => s!"{path}: condFull vs ir"
  | .op .condFull _, .op .condSome _ => s!"{path}: condFull vs condSome"
