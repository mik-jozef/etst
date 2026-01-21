import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono
import Etst.Subtyping.Utils.ExprVars

namespace Etst


/-
  `ExpandsInto dl a b` iff `a` expands into `b` using definitions from `dl`.
  
  Eg. if `dl` contains `Nat = 0 | succ Nat`, then `Nat` can expand into
  `0 | succ (0 | succ Nat)`.
-/
inductive Expr.ExpandsInto
  (dl: DefList)
:
  Bool → BasicExpr → BasicExpr → Type

| refl e: ExpandsInto dl ed e e
| const (x: Nat)
    (exp: ExpandsInto dl true (dl.getDef x) xExp)
  :
    ExpandsInto dl true (.const x) xExp
| pair
    (left: ExpandsInto dl ed l lExp)
    (rite: ExpandsInto dl ed r rExp)
  :
    ExpandsInto dl ed (.pair l r) (.pair lExp rExp)
| full
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.full body) (.full bodyExp)
| ir
    (left: ExpandsInto dl ed l lExp)
    (rite: ExpandsInto dl ed r rExp)
  :
    ExpandsInto dl ed (.ir l r) (.ir lExp rExp)
| compl
    (exp: ExpandsInto dl (!ed) body bodyExp)
  :
    ExpandsInto dl ed (.compl body) (.compl bodyExp)
| arbIr
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.arbIr body) (.arbIr bodyExp)

namespace Expr.ExpandsInto
  open Expr
  
  def rfl {dl ed e}: ExpandsInto dl ed e e := .refl e
  
  def some
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.some body) (.some bodyExp)
  :=
    compl (full (compl (Bool.not_not _ ▸ exp)))
  
  def un
    (left: ExpandsInto dl ed l lExp)
    (rite: ExpandsInto dl ed r rExp)
  :
    ExpandsInto dl ed (.un l r) (.un lExp rExp)
  :=
    compl
      (ir
        (compl (Bool.not_not _ ▸ left))
        (compl (Bool.not_not _ ▸ rite)))
  
  def arbUn
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.arbUn body) (.arbUn bodyExp)
  :=
    compl (arbIr (compl (Bool.not_not _ ▸ exp)))
  
  
  open BasicExpr in
  def triIntp_eq_wfm
    (dl: DefList)
    (fv: List Pair)
  :
    ExpandsInto dl ed left rite →
    left.triIntp fv dl.wfm = rite.triIntp fv dl.wfm
  
  | .refl _ => _root_.rfl
  | .const x expr =>
    let ih := expr.triIntp_eq_wfm (fv := fv)
    let eqDef := dl.wfm_eq_def x
    let eqFv := dl.triIntp2_eq_fv x [] fv dl.wfm dl.wfm
    eqDef.trans (eqFv.trans ih)
  | .pair left rite =>
    eq_triIntp2_pair_of_eq
      (left.triIntp_eq_wfm dl fv)
      (rite.triIntp_eq_wfm dl fv)
  | .full expr =>
    eq_triIntp2_full_of_eq (expr.triIntp_eq_wfm dl fv)
  | .ir left rite =>
    eq_triIntp2_ir_of_eq
      (left.triIntp_eq_wfm dl fv)
      (rite.triIntp_eq_wfm dl fv)
  | .compl expr =>
    eq_triIntp2_compl_of_eq (expr.triIntp_eq_wfm dl fv)
  | .arbIr expr =>
    eq_triIntp2_arbIr_of_eq
      (fun dB => expr.triIntp_eq_wfm dl (dB :: fv))
  
  open BasicExpr in
  open SingleLaneExpr in
  def lfpStage_le_std
    (expInto: ExpandsInto dl ed l r)
    (fv: List Pair)
    (n: Ordinal.{0})
  :
    let _ := Valuation.ordStdLattice
    let op := operatorC dl dl.wfm
    let triIntpE e fv := e.triIntp2 fv dl.wfm (op.lfpStage n)
    let triIntpO e fv := e.triIntp2 fv (op.lfpStage n) dl.wfm
    
    if ed
    then triIntpE l fv ≤ triIntpE r fv
    else triIntpO r fv ≤ triIntpO l fv
  := by
    intro _ op triIntpE triIntpO
    exact
    let _ := Set3.ordStdLattice
    match expInto with
    | refl _ =>
      match ed with
      | true => le_rfl
      | false => le_rfl
    | const x exp =>
      let ih := exp.lfpStage_le_std fv n
      let defX := dl.getDef x
      let leNextStage:
        triIntpE (.const x) [] ≤ triIntpE defX fv
      :=
        let eqNext: triIntpE defX [] = op.lfpStage n.succ x :=
          congr (op.lfpStage_apply_eq_succ n) _root_.rfl
        let eqClear: triIntpE defX [] = triIntpE (dl.getDef x) fv :=
          dl.triIntp2_eq_fv _ _ _ _ _
        
        eqClear ▸ eqNext ▸ op.lfpStage_mono (Order.le_succ n) x
      leNextStage.trans ih
    | pair left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp2_mono_std_pair leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp2_mono_std_pair leLeft leRite
    | ir left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp2_mono_std_ir leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp2_mono_std_ir leLeft leRite
    | full exp =>
      match ed with
      | true => triIntp2_mono_std_full (exp.lfpStage_le_std fv n)
      | false => triIntp2_mono_std_full (exp.lfpStage_le_std fv n)
    | compl exp =>
      match ed with
      | true => triIntp2_mono_std_compl (exp.lfpStage_le_std fv n)
      | false => triIntp2_mono_std_compl (exp.lfpStage_le_std fv n)
    | arbIr exp =>
      match ed with
      | true =>
        triIntp2_mono_std_arbIr (fun dB =>
          exp.lfpStage_le_std (dB :: fv) n)
      | false =>
        triIntp2_mono_std_arbIr (fun dB =>
          exp.lfpStage_le_std (dB :: fv) n)
end Expr.ExpandsInto
