import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono
import Etst.Subtyping.Utils.ExprClearVars

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
| condFull
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.condFull body) (.condFull bodyExp)
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
  
  def condSome
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.condSome body) (.condSome bodyExp)
  :=
    compl (condFull (compl (Bool.not_not _ ▸ exp)))
  
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
    (bv: List Pair)
  :
    ExpandsInto dl ed left rite →
    left.triIntp bv dl.wfm = rite.triIntp bv dl.wfm
  
  | .refl _ => _root_.rfl
  | .const x expr =>
    let ih := expr.triIntp_eq_wfm (bv := bv)
    let eqDef := dl.wfm_eq_def x
    let eqBv := dl.interp_eq_bv x [] bv dl.wfm dl.wfm
    eqDef.trans (eqBv.trans ih)
  | .pair left rite =>
    eq_triIntp2_pair_of_eq
      (left.triIntp_eq_wfm dl bv)
      (rite.triIntp_eq_wfm dl bv)
  | .condFull expr =>
    eq_triIntp2_condFull_of_eq (expr.triIntp_eq_wfm dl bv)
  | .ir left rite =>
    eq_triIntp2_ir_of_eq
      (left.triIntp_eq_wfm dl bv)
      (rite.triIntp_eq_wfm dl bv)
  | .compl expr =>
    eq_triIntp2_compl_of_eq (expr.triIntp_eq_wfm dl bv)
  | .arbIr expr =>
    eq_triIntp2_arbIr_of_eq
      (fun dB => expr.triIntp_eq_wfm dl (dB :: bv))
  
  open BasicExpr in
  open SingleLaneExpr in
  def lfpStage_le_std
    (expInto: ExpandsInto dl ed l r)
    (bv: List Pair)
    (n: Ordinal.{0})
  :
    let _ := Valuation.ordStdLattice
    let op := operatorC dl dl.wfm
    let intpE e bv := e.triIntp2 bv dl.wfm (op.lfpStage n)
    let intpO e bv := e.triIntp2 bv (op.lfpStage n) dl.wfm
    
    if ed
    then intpE l bv ≤ intpE r bv
    else intpO r bv ≤ intpO l bv
  := by
    intro _ op intpE intpO
    exact
    let _ := Set3.ordStdLattice
    match expInto with
    | refl _ =>
      match ed with
      | true => le_rfl
      | false => le_rfl
    | const x exp =>
      let ih := exp.lfpStage_le_std bv n
      let defX := dl.getDef x
      let leNextStage:
        intpE (.const x) [] ≤ intpE defX bv
      :=
        let eqNext: intpE defX [] = op.lfpStage n.succ x :=
          congr (op.lfpStage_apply_eq_succ n) _root_.rfl
        let eqClear: intpE defX [] = intpE (dl.getDef x) bv :=
          dl.isClean x ▸
          clearVars_preserves_interp _ _ _ _
        
        eqClear ▸ eqNext ▸ op.lfpStage_mono (Order.le_succ n) x
      leNextStage.trans ih
    | pair left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std bv n
        let leRite := rite.lfpStage_le_std bv n
        triIntp2_mono_std_pair leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std bv n
        let leRite := rite.lfpStage_le_std bv n
        triIntp2_mono_std_pair leLeft leRite
    | ir left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std bv n
        let leRite := rite.lfpStage_le_std bv n
        triIntp2_mono_std_ir leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std bv n
        let leRite := rite.lfpStage_le_std bv n
        triIntp2_mono_std_ir leLeft leRite
    | condFull exp =>
      match ed with
      | true => triIntp2_mono_std_condFull (exp.lfpStage_le_std bv n)
      | false => triIntp2_mono_std_condFull (exp.lfpStage_le_std bv n)
    | compl exp =>
      match ed with
      | true => triIntp2_mono_std_compl (exp.lfpStage_le_std bv n)
      | false => triIntp2_mono_std_compl (exp.lfpStage_le_std bv n)
    | arbIr exp =>
      match ed with
      | true =>
        triIntp2_mono_std_arbIr (fun dB =>
          exp.lfpStage_le_std (dB :: bv) n)
      | false =>
        triIntp2_mono_std_arbIr (fun dB =>
          exp.lfpStage_le_std (dB :: bv) n)
end Expr.ExpandsInto
