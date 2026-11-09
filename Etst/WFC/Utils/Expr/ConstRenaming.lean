/-
  Proves that structurally identical definitions define the same
  (three-valued) sets.
-/
module
public import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.RulesOfInference

public section
namespace Etst


def Expr.substConst {kind}
  (map: (tag: kind.ConstTag) → Nat → Expr kind)
:
  Expr kind → Expr kind
|
  .const tag x => map tag x
| .var x => .var x
| .null => .null
| .prod l r => .prod (l.substConst map) (r.substConst map)
| .ir l r => .ir (l.substConst map) (r.substConst map)
| .full b => .full (b.substConst map)
| .compl b => .compl (b.substConst map)
| .arbIr b => .arbIr (b.substConst map)

def Expr.mapConst {kind}
  (map: Nat → Nat)
  (expr: Expr kind)
:
  Expr kind
:=
  expr.substConst (fun tag x => .const tag (map x))


theorem Expr.substConst_eq_id {kind}
  (expr: Expr kind)
  {map: (tag: kind.ConstTag) → Nat → Expr kind}
  (isId: (tag x: _) → map tag x = .const tag x)
:
  expr.substConst map = expr
:=
  match expr with
  | .const tag x => isId tag x
  | .var _ => rfl
  | .null => rfl
  | .prod left rite =>
    congrArg₂ prod
      (left.substConst_eq_id isId)
      (rite.substConst_eq_id isId)
  | .ir left rite =>
    congrArg₂ ir
      (left.substConst_eq_id isId)
      (rite.substConst_eq_id isId)
  | .full body =>
    congrArg full (body.substConst_eq_id isId)
  | .compl body =>
    congrArg compl (body.substConst_eq_id isId)
  | .arbIr body =>
    congrArg arbIr (body.substConst_eq_id isId)

theorem Expr.mapConst_eq_id {kind}
  (expr: Expr kind)
:
  expr.mapConst id = expr
:=
  expr.substConst_eq_id (fun _ _ => rfl)


/-
  Proves that substituting constants preserves interpretation when
  each replacement expression has the same interpretation as the
  original constant.
-/
theorem Expr.substConst_intp {kind lane bSrc bDst cSrc cDst fv}
  (map: (tag: kind.ConstTag) → Nat → Expr kind)
  {expr: Expr kind}
  (eqBC:
    ∀ tag x fv,
      expr.UsesConst x →
      Eq
        ((map tag x).intp lane bDst cDst fv)
        ((cSrc x).getLane (tag.getLane lane)))
  (eqCB:
    ∀ tag x fv,
      expr.UsesConst x →
      Eq
        ((map tag x).intp lane.toggle cDst bDst fv)
        ((bSrc x).getLane (tag.getLane lane.toggle)))
:
  Eq
    ((expr.substConst map).intp lane bDst cDst fv)
    (expr.intp lane bSrc cSrc fv)
:=
  match expr with
  | .const tag x => eqBC tag x fv rfl
  | .var _ => rfl
  | .null => rfl
  | .prod _ _ =>
    eq_intp_prod_of_eq
      (substConst_intp map
        (fun tag x fv h => eqBC tag x fv (Or.inl h))
        (fun tag x fv h => eqCB tag x fv (Or.inl h)))
      (substConst_intp map
        (fun tag x fv h => eqBC tag x fv (Or.inr h))
        (fun tag x fv h => eqCB tag x fv (Or.inr h)))
  | .ir _ _ =>
    eq_intp_ir_of_eq
      (substConst_intp map
        (fun tag x fv h => eqBC tag x fv (Or.inl h))
        (fun tag x fv h => eqCB tag x fv (Or.inl h)))
      (substConst_intp map
        (fun tag x fv h => eqBC tag x fv (Or.inr h))
        (fun tag x fv h => eqCB tag x fv (Or.inr h)))
  | .full _ =>
    eq_intp_full_of_eq (substConst_intp map eqBC eqCB)
  | .compl _ =>
    eq_intp_compl_of_eq
      (substConst_intp map
        (fun tag x fv h => eqCB tag x fv h)
        (fun tag x fv h => lane.toggle_toggle ▸ eqBC tag x fv h))
  | .arbIr _ =>
    eq_intp_arbIr_of_eq fun _ => substConst_intp map eqBC eqCB

theorem Expr.mapConst_intp {kind lane bSrc bDst cSrc cDst fv}
  (map: Nat → Nat)
  {expr: Expr kind}
  (eqB: ∀ x, expr.UsesConst x → bSrc x = bDst (map x))
  (eqC: ∀ x, expr.UsesConst x → cSrc x = cDst (map x))
:
  Eq
    ((expr.mapConst map).intp lane bDst cDst fv)
    (expr.intp lane bSrc cSrc fv)
:=
  substConst_intp
    (fun tag x => .const tag (map x))
    (fun tag x _ h =>
      (congrArg (fun s => s.getLane (tag.getLane lane)) (eqC x h)).symm)
    (fun tag x _ h =>
      (congrArg
        (fun s => s.getLane (tag.getLane lane.toggle))
        (eqB x h)).symm)


namespace Expr
  theorem substConst_triIntp
    (map: Nat → Expr .basic)
    {expr: Expr .basic}
    {bSrc bDst cSrc cDst fv}
    (eqBC:
      ∀ x fv,
        expr.UsesConst x →
        (map x).triIntp bDst cDst fv = cSrc x)
    (eqCB:
      ∀ x fv,
        expr.UsesConst x →
        (map x).triIntp cDst bDst fv = bSrc x)
  :
    Eq
      (triIntp (expr.substConst (fun _ => map)) bDst cDst fv)
      (expr.triIntp bSrc cSrc fv)
  :=
    match expr with
    | .const _ x => eqBC x fv rfl
    | .var _ => rfl
    | .null => rfl
    | .prod _ _ =>
      eq_triIntp_prod_of_eq
        (substConst_triIntp map
          (fun x fv h => eqBC x fv (Or.inl h))
          (fun x fv h => eqCB x fv (Or.inl h)))
        (substConst_triIntp map
          (fun x fv h => eqBC x fv (Or.inr h))
          (fun x fv h => eqCB x fv (Or.inr h)))
    | .ir _ _ =>
      eq_triIntp_ir_of_eq
        (substConst_triIntp map
          (fun x fv h => eqBC x fv (Or.inl h))
          (fun x fv h => eqCB x fv (Or.inl h)))
        (substConst_triIntp map
          (fun x fv h => eqBC x fv (Or.inr h))
          (fun x fv h => eqCB x fv (Or.inr h)))
    | .full _ =>
      eq_triIntp_full_of_eq (substConst_triIntp map eqBC eqCB)
    | .compl _ =>
      eq_triIntp_compl_of_eq (substConst_triIntp map eqCB eqBC)
    | .arbIr _ =>
      eq_triIntp_arbIr_of_eq fun _ =>
        substConst_triIntp map eqBC eqCB
  
  theorem mapConst_triIntp
    (map: Nat → Nat)
    {expr: Expr .basic}
    {bSrc bDst cSrc cDst fv}
    (eqB: ∀ x, expr.UsesConst x → bSrc x = bDst (map x))
    (eqC: ∀ x, expr.UsesConst x → cSrc x = cDst (map x))
  :
    Eq
      (triIntp (expr.mapConst map) bDst cDst fv)
      (expr.triIntp bSrc cSrc fv)
  :=
    substConst_triIntp
      (fun x => .const () (map x))
      (fun x _ hx => (eqC x hx).symm)
      (fun x _ hx => (eqB x hx).symm)

end Expr
