
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.PairExprMono
import Etst.WFC.Utils.ExprMonoEq
import Etst.Subtyping.Utils.ExprClearBvars

namespace Etst
open PairExpr


/-
  `ExpandsInto dl a b` iff `a` expands into `b` using definitions from `dl`.
  
  Eg. if `dl` contains `Nat = 0 | succ Nat`, then `Nat` can expand into
  `0 | succ (0 | succ Nat)`.
-/
inductive PairExpr.ExpandsInto
  (dl: PairDl)
:
  PairExpr → PairExpr → Type

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
| cpl
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.cpl body) (.cpl bodyExp)
| arbUn
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.arbUn body) (.arbUn bodyExp)
| arbIr
    (exp: ExpandsInto dl body bodyExp)
  :
    ExpandsInto dl (.arbIr body) (.arbIr bodyExp)

namespace PairExpr.ExpandsInto
  open Expr
  
  def rfl {dl e}: ExpandsInto dl e e :=
    ExpandsInto.refl e
  
  def lfpStage_eq_std
    (dl: PairDl)
  :
    ExpandsInto dl l r → l.intp bv dl.wfm = r.intp bv dl.wfm
  
  | .refl _ => _root_.rfl
    | .var x expr =>
      let ih := expr.lfpStage_eq_std (bv := bv)
      let eqDef := dl.wfm_eq_def pairSalgebra x
      let eqClean := clearVars_preserves_interp
        (dl.getDef x) bv dl.wfm dl.wfm
      eqDef.trans (Eq.trans eqClean ih)
    | .pair left rite =>
      eq_pair_of_eq left.lfpStage_eq_std rite.lfpStage_eq_std
    | .un left rite =>
      eq_un_of_eq left.lfpStage_eq_std rite.lfpStage_eq_std
    | .ir left rite =>
      eq_ir_of_eq left.lfpStage_eq_std rite.lfpStage_eq_std
    | .condSome expr =>
      eq_condSome_of_eq expr.lfpStage_eq_std
    | .condFull expr =>
      eq_condFull_of_eq expr.lfpStage_eq_std
    | .cpl expr =>
      eq_cpl_of_eq expr.lfpStage_eq_std
    | .arbUn expr =>
      eq_arbUn_of_eq (fun _ => expr.lfpStage_eq_std)
    | .arbIr expr =>
      eq_arbIr_of_eq (fun _ => expr.lfpStage_eq_std)

  def lfpStage_le_std
    (expInto: ExpandsInto dl l r)
    (bv: List Pair)
    (n: Ordinal.{0})
  :
    let _ := Valuation.ordStdLattice
    let op := operatorC pairSalgebra dl dl.wfm
    let intpN e bv n := intp2 e bv dl.wfm (op.lfpStage n)
    
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
          clearVars_preserves_interp (salg := pairSalgebra) _ _ _ _
        
        eqClear ▸ eqNext ▸ op.lfpStage_mono (Order.le_succ n) x
      leNextStage.trans ih
    | pair left rite =>
      let leLeft := left.lfpStage_le_std bv n
      let leRite := rite.lfpStage_le_std bv n
      intp_mono_std_pair leLeft leRite
    | un left rite =>
      let leLeft := left.lfpStage_le_std bv n
      let leRite := rite.lfpStage_le_std bv n
      intp_mono_std_un leLeft leRite
    | ir left rite =>
      let leLeft := left.lfpStage_le_std bv n
      let leRite := rite.lfpStage_le_std bv n
      intp_mono_std_ir leLeft leRite
    | condSome exp =>
      let leBody := exp.lfpStage_le_std bv n
      intp_mono_std_condSome leBody
    | condFull exp =>
      let leBody := exp.lfpStage_le_std bv n
      intp_mono_std_condFull leBody
    | cpl exp =>
      let eqBody := exp.lfpStage_eq_std
      inter_mono_std_cpl (le_of_eq eqBody.symm)
    | arbUn exp =>
      inter_mono_std_arbUn (fun dB =>
        exp.lfpStage_le_std (dB :: bv) n)
    | arbIr exp =>
      inter_mono_std_arbIr (fun dB =>
        exp.lfpStage_le_std (dB :: bv) n)
end PairExpr.ExpandsInto
