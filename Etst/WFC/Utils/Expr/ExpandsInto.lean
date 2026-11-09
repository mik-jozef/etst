module
public import Etst.WFC.Ch3_WellFoundedModel
public import Etst.WFC.Utils.General.LfpStages
import Etst.WFC.Utils.Expr.FreeVars
import Etst.WFC.Utils.InterpretationMono

public section
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
  (isEvenDepth: Bool) → Expr .basic → Expr .basic → Type

| refl {ed} e: ExpandsInto dl ed e e
| const {xExp} (x: Nat)
    (exp: ExpandsInto dl true (dl.getDef x) xExp)
  :
    ExpandsInto dl true (.const () x) xExp
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
  
  theorem isClean_expands
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
  
  
  theorem lfpStage_le_std {ed l r}
    (expInto: ExpandsInto dl ed l r)
    (fv: List Pair)
    (n: Ordinal.{0})
  :
    let _ := Valuation.ordStdLattice
    let op := operatorC dl dl.wfm
    let triIntpE e fv := e.triIntp dl.wfm (op.lfpStage n) fv
    let triIntpO e fv := e.triIntp (op.lfpStage n) dl.wfm fv
    
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
        triIntpE (.const () x) [] ≤ triIntpE defX fv
      :=
        let eqNext: triIntpE defX [] = op.lfpStage n.succ x :=
          congr (op.lfpStage_apply_eq_succ n) _root_.rfl
        let eqClear: triIntpE defX [] = triIntpE (dl.getDef x) fv :=
          dl.triIntp_getDef_eq_fv x dl.wfm (op.lfpStage n) [] fv
        
        eqClear ▸ eqNext ▸ op.lfpStage_mono (Order.le_succ n) x
      leNextStage.trans ih
    | prod left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp_mono_std_prod leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp_mono_std_prod leLeft leRite
    | ir left rite =>
      match ed with
      | true =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp_mono_std_ir leLeft leRite
      | false =>
        let leLeft := left.lfpStage_le_std fv n
        let leRite := rite.lfpStage_le_std fv n
        triIntp_mono_std_ir leLeft leRite
    | full exp =>
      match ed with
      | true => triIntp_mono_std_full (exp.lfpStage_le_std fv n)
      | false => triIntp_mono_std_full (exp.lfpStage_le_std fv n)
    | compl exp =>
      match ed with
      | true => triIntp_antimono_std_compl (exp.lfpStage_le_std fv n)
      | false => triIntp_antimono_std_compl (exp.lfpStage_le_std fv n)
    | arbIr exp =>
      match ed with
      | true =>
        triIntp_mono_std_arbIr (fun pB =>
          exp.lfpStage_le_std (pB :: fv) n)
      | false =>
        triIntp_mono_std_arbIr (fun pB =>
          exp.lfpStage_le_std (pB :: fv) n)
end DefList.ExpandsInto
