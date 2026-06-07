import Etst.WFC.Ch4_S1_MembershipPs
import Etst.WFC.Utils.Expr.FreeVars
import Etst.WFC.Utils.InterpretationMono

namespace Etst


/-
  `ExpandsInto dl a b` iff `a` expands into `b` using definitions from `dl`.
  Only constants under an even number of complements can be expanded.
  
  Eg. if `dl` contains `Nat = 0 | succ Nat`, then `Nat` can expand into
  `0 | succ (0 | succ Nat)`.
-/
inductive DefList.ExpandsInto
  (dl: DefList)
:
  (isEvenDepth: Bool) → BasicExpr → BasicExpr → Type

| refl {ed} e: ExpandsInto dl ed e e
| const {xExp} (x: Nat)
    (exp: ExpandsInto dl true (dl.getDef x) xExp)
  :
    ExpandsInto dl true (.const x) xExp
| prod {ed l lExp r rExp}
    (left: ExpandsInto dl ed l lExp)
    (rite: ExpandsInto dl ed r rExp)
  :
    ExpandsInto dl ed (.prod l r) (.prod lExp rExp)
| full {ed body bodyExp}
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.full body) (.full bodyExp)
| ir {ed l lExp r rExp}
    (left: ExpandsInto dl ed l lExp)
    (rite: ExpandsInto dl ed r rExp)
  :
    ExpandsInto dl ed (.ir l r) (.ir lExp rExp)
| compl {ed body bodyExp}
    (exp: ExpandsInto dl (!ed) body bodyExp)
  :
    ExpandsInto dl ed (.compl body) (.compl bodyExp)
| arbIr {ed body bodyExp}
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.arbIr body) (.arbIr bodyExp)

namespace DefList.ExpandsInto
  open Expr
  variable {dl}
  
  def rfl {dl ed e}: ExpandsInto dl ed e e := .refl e
  
  def some {ed body bodyExp}
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.some body) (.some bodyExp)
  :=
    compl (full (compl (Bool.not_not _ ▸ exp)))
  
  def un {ed l lExp r rExp}
    (left: ExpandsInto dl ed l lExp)
    (rite: ExpandsInto dl ed r rExp)
  :
    ExpandsInto dl ed (.un l r) (.un lExp rExp)
  :=
    compl
      (ir
        (compl (Bool.not_not _ ▸ left))
        (compl (Bool.not_not _ ▸ rite)))
  
  def arbUn {ed body bodyExp}
    (exp: ExpandsInto dl ed body bodyExp)
  :
    ExpandsInto dl ed (.arbUn body) (.arbUn bodyExp)
  :=
    compl (arbIr (compl (Bool.not_not _ ▸ exp)))
  
  def isClean_expands
    {ed a b}
    (exp: ExpandsInto dl ed a b)
    (shift: Nat)
    {P: Nat → Prop}
    (h: ∀ x, a.UsesFreeVar (x + shift) → P x)
  :
    ∀ x, b.UsesFreeVar (x + shift) → P x
  :=
    match exp with
    | .refl _ => h
    | .const x exp =>
      isClean_expands
        exp
        shift
        (fun y hy => False.elim ((dl.isClean x) (y + shift) hy))
    | .prod left rite =>
      let hL := isClean_expands left shift (fun x hx => h x (Or.inl hx))
      let hR := isClean_expands rite shift (fun x hx => h x (Or.inr hx))
      fun x hx => Or.elim hx (hL x) (hR x)
    | .full exp =>
      let hExp := isClean_expands exp shift (fun x hx => h x hx)
      fun x hx => hExp x hx
    | .ir left rite =>
      let hL := isClean_expands left shift (fun x hx => h x (Or.inl hx))
      let hR := isClean_expands rite shift (fun x hx => h x (Or.inr hx))
      fun x hx => Or.elim hx (hL x) (hR x)
    | .compl exp =>
      fun x hx => isClean_expands exp shift (fun x hx => h x hx) x hx
    | .arbIr exp =>
      fun x hx => isClean_expands exp (shift + 1) (fun x hx => h x hx) x hx
  
  
  open BasicExpr in
  def triIntp_eq_wfm {ed left rite}
    (dl: DefList)
    (fv: List Pair)
    (o: Valuation Pair)
  :
    ExpandsInto dl ed left rite →
    left.triIntp fv (dl.wfm o) o = rite.triIntp fv (dl.wfm o) o
  
  | .refl _ => _root_.rfl
  | .const x expr =>
    let ih := expr.triIntp_eq_wfm (fv := fv) (o := o)
    let eqDef := dl.wfm_eq_def o x
    let eqFv := dl.intpDefs2_eq_fv x [] fv (dl.wfm o) (dl.wfm o) o
    eqDef.trans (eqFv.trans ih)
  | .prod left rite =>
    eq_triIntp2_prod_of_eq
      (left.triIntp_eq_wfm dl fv o)
      (rite.triIntp_eq_wfm dl fv o)
  | .full expr =>
    eq_triIntp2_full_of_eq (expr.triIntp_eq_wfm dl fv o)
  | .ir left rite =>
    eq_triIntp2_ir_of_eq
      (left.triIntp_eq_wfm dl fv o)
      (rite.triIntp_eq_wfm dl fv o)
  | .compl expr =>
    eq_triIntp2_compl_of_eq (expr.triIntp_eq_wfm dl fv o)
  | .arbIr expr =>
    eq_triIntp2_arbIr_of_eq
      (fun pB => expr.triIntp_eq_wfm dl (pB :: fv) o)
  
  open BasicExpr in
  open SingleLaneExpr in
  def lfpStage_le_std {ed l r}
    (expInto: ExpandsInto dl ed l r)
    (fv: List Pair)
    (n: Ordinal.{0})
    (o: Valuation Pair)
  :
    let _ := Valuation.ordStdLattice
    let op := operatorC dl (dl.wfm o) o
    let triIntpE e fv := e.triIntp2 fv (dl.wfm o) (op.lfpStage n) o
    let triIntpO e fv := e.triIntp2 fv (op.lfpStage n) (dl.wfm o) o
    
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
      let ih := exp.lfpStage_le_std fv n o
      let defX := dl.getDef x
      let leNextStage:
        triIntpE (.const x) [] ≤ triIntpE defX fv
      :=
        let eqNext: triIntpE defX [] = op.lfpStage n.succ x :=
          congr (op.lfpStage_apply_eq_succ n) _root_.rfl
        let eqClear: triIntpE defX [] = triIntpE (dl.getDef x) fv :=
          dl.intpDefs2_eq_fv _ _ _ _ _ _
        
        eqClear ▸ eqNext ▸ op.lfpStage_mono (Order.le_succ n) x
      leNextStage.trans ih
    | prod left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std fv n o
        let leRite := rite.lfpStage_le_std fv n o
        triIntp2_mono_std_prod leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std fv n o
        let leRite := rite.lfpStage_le_std fv n o
        triIntp2_mono_std_prod leLeft leRite
    | ir left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std fv n o
        let leRite := rite.lfpStage_le_std fv n o
        triIntp2_mono_std_ir leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std fv n o
        let leRite := rite.lfpStage_le_std fv n o
        triIntp2_mono_std_ir leLeft leRite
    | full exp =>
      match ed with
      | true => triIntp2_mono_std_full (exp.lfpStage_le_std fv n o)
      | false => triIntp2_mono_std_full (exp.lfpStage_le_std fv n o)
    | compl exp =>
      match ed with
      | true => triIntp2_mono_std_compl (exp.lfpStage_le_std fv n o)
      | false => triIntp2_mono_std_compl (exp.lfpStage_le_std fv n o)
    | arbIr exp =>
      match ed with
      | true =>
        triIntp2_mono_std_arbIr (fun pB =>
          exp.lfpStage_le_std (pB :: fv) n o)
      | false =>
        triIntp2_mono_std_arbIr (fun pB =>
          exp.lfpStage_le_std (pB :: fv) n o)
end DefList.ExpandsInto
