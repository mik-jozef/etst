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
  