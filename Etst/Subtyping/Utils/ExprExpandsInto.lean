
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono
import Etst.Subtyping.Utils.ExprClearBvars

namespace Etst


/-
  `ExpandsInto dl a b` iff `a` expands into `b` using definitions from `dl`.
  
  Eg. if `dl` contains `Nat = 0 | succ Nat`, then `Nat` can expand into
  `0 | succ (0 | succ Nat)`.
-/
inductive Expr.ExpandsInto
  (dl: DefList)
:
  BasicExpr → BasicExpr → Type

| refl e: ExpandsInto dl e e
| var (x: Nat)
    (exp: ExpandsInto dl (dl.getDef x).clearBvars xExp)
  :
    ExpandsInto dl (.var x) xExp
| pair
    (left: ExpandsInto dl l lExp)
    (rite: ExpandsInto dl r rExp)
  :
    ExpandsInto dl (.pair l r) (.pair lExp rExp)
| condSome
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.condSome body) (.condSome bodyExp)
| condFull
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.condFull body) (.condFull bodyExp)
| un
    (left: ExpandsInto dl l lExp)
    (rite: ExpandsInto dl r rExp)
  :
    ExpandsInto dl (.un l r) (.un lExp rExp)
| ir
    (left: ExpandsInto dl l lExp)
    (rite: ExpandsInto dl r rExp)
  :
    ExpandsInto dl (.ir l r) (.ir lExp rExp)
| compl
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.compl body) (.compl bodyExp)
| arbUn
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.arbUn body) (.arbUn bodyExp)
| arbIr
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.arbIr body) (.arbIr bodyExp)

namespace Expr.ExpandsInto
  open Expr
  
  def rfl {dl e}: ExpandsInto dl e e :=
    ExpandsInto.refl e
  
  open BasicExpr in
  def intp_eq_wfm
    (dl: DefList)
    (bv: List Pair)
  :
    ExpandsInto dl left rite →
    left.triIntp bv dl.wfm = rite.triIntp bv dl.wfm
  
  | .refl _ => _root_.rfl
    | .var x expr =>
      let ih := expr.intp_eq_wfm (bv := bv)
      let eqDef := dl.wfm_eq_def x
      let eqClean :=
        BasicExpr.clearBvars_preserves_interp
          (dl.getDef x) bv dl.wfm dl.wfm
      eqDef.trans (Eq.trans eqClean ih)
    | .pair left rite =>
      eq_triIntp2_pair_of_eq (left.intp_eq_wfm dl bv) (rite.intp_eq_wfm dl bv)
    | .un left rite =>
      eq_triIntp2_un_of_eq (left.intp_eq_wfm dl bv) (rite.intp_eq_wfm dl bv)
        | .ir left rite =>
      eq_triIntp2_ir_of_eq (left.intp_eq_wfm dl bv) (rite.intp_eq_wfm dl bv)
        | .condSome expr =>
      eq_triIntp2_condSome_of_eq (expr.intp_eq_wfm dl bv)
        | .condFull expr =>
      eq_triIntp2_condFull_of_eq (expr.intp_eq_wfm dl bv)
        | .compl expr =>
      eq_triIntp2_compl_of_eq dl.wfm dl.wfm (expr.intp_eq_wfm dl bv)
        | .arbUn expr =>
      eq_triIntp2_arbUn_of_eq (fun dB => expr.intp_eq_wfm dl (dB :: bv))
        | .arbIr expr =>
      eq_triIntp2_arbIr_of_eq (fun dB => expr.intp_eq_wfm dl (dB :: bv))
  
  open BasicExpr in
  open SingleLaneExpr in
  def lfpStage_le_std
    (expInto: ExpandsInto dl l r)
    (bv: List Pair)
    (n: Ordinal.{0})
  :
    let _ := Valuation.ordStdLattice
    let op := operatorC dl dl.wfm
    let intpN e bv n := e.triIntp2 bv dl.wfm (op.lfpStage n)
    
    intpN l bv n ≤ intpN r bv n
  := by
    intro _ op intpN
    exact
    let _ := Set3.ordStdLattice
    match expInto with
    | refl _ => le_rfl
    | var x exp =>
      let ih := exp.lfpStage_le_std bv n
      let defX := dl.getDef x
      let leNextStage:
        op.lfpStage n x ≤ intpN defX.clearBvars bv n
      :=
        let eqNext: intpN defX [] n = op.lfpStage n.succ x :=
          congr (op.lfpStage_apply_eq_succ n) _root_.rfl
        let eqClear: intpN defX [] n = intpN defX.clearBvars bv n :=
          clearBvars_preserves_interp _ _ _ _
        
        eqClear ▸ eqNext ▸ op.lfpStage_mono (Order.le_succ n) x
      leNextStage.trans ih
    | pair left rite =>
      let leLeft := left.lfpStage_le_std bv n
      let leRite := rite.lfpStage_le_std bv n
      triIntp2_mono_std_pair leLeft leRite
    | un left rite =>
      let leLeft := left.lfpStage_le_std bv n
      let leRite := rite.lfpStage_le_std bv n
      triIntp2_mono_std_un leLeft leRite
    | ir left rite =>
      let leLeft := left.lfpStage_le_std bv n
      let leRite := rite.lfpStage_le_std bv n
      triIntp2_mono_std_ir leLeft leRite
    | condSome exp =>
      triIntp2_mono_std_condSome (exp.lfpStage_le_std bv n)
    | condFull exp =>
      triIntp2_mono_std_condFull (exp.lfpStage_le_std bv n)
    | compl exp =>
      let eqBody := exp.intp_eq_wfm dl bv
      triIntp2_mono_std_compl dl.wfm dl.wfm (le_of_eq eqBody.symm)
    | arbUn exp =>
      triIntp2_mono_std_arbUn (fun dB =>
        exp.lfpStage_le_std (dB :: bv) n)
    | arbIr exp =>
      triIntp2_mono_std_arbIr (fun dB =>
        exp.lfpStage_le_std (dB :: bv) n)
end Expr.ExpandsInto
