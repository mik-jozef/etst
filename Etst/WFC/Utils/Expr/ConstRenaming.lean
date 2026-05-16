/-
  Proves that structurally identical definitions define the same
  (three-valued) sets.
-/

import Etst.WFC.Utils.InterpretationMono

namespace Etst


def Expr.substConst {E}
  (map: E → Nat → Expr E)
:
  Expr E → Expr E
|
  .const e x => map e x
| .var x => .var x
| .null => .null
| .pair l r => .pair (l.substConst map) (r.substConst map)
| .ir l r => .ir (l.substConst map) (r.substConst map)
| .full b => .full (b.substConst map)
| .compl b => .compl (b.substConst map)
| .arbIr b => .arbIr (b.substConst map)

def Expr.mapConst {E}
  (map: Nat → Nat)
  (expr: Expr E)
:
  Expr E
:=
  expr.substConst (fun e x => .const e (map x))


def Expr.substConst_eq_id {E}
  (expr: Expr E)
  {map: E → Nat → Expr E}
  (isId: (e x: _) → map e x = .const e x)
:
  expr.substConst map = expr
:=
  match expr with
  | .const e x => isId e x
  | .var _ => rfl
  | .null => rfl
  | .pair left rite =>
    congrArg₂ Expr.pair
      (left.substConst_eq_id isId)
      (rite.substConst_eq_id isId)
  | .ir left rite =>
    congrArg₂ Expr.ir
      (left.substConst_eq_id isId)
      (rite.substConst_eq_id isId)
  | .full body =>
    congrArg Expr.full (body.substConst_eq_id isId)
  | .compl body =>
    congrArg Expr.compl (body.substConst_eq_id isId)
  | .arbIr body =>
    congrArg Expr.arbIr (body.substConst_eq_id isId)

def Expr.mapConst_eq_id {E}
  (expr: Expr E)
:
  expr.mapConst id = expr
:=
  expr.substConst_eq_id (fun _ _ => rfl)


/-
  Proves that substituting constants preserves interpretation when
  each replacement expression has the same interpretation as the
  original constant in both complement polarities.
-/
def SingleLaneExpr.substConst_intp2 {fv bSrc bDst cSrc cDst}
  (map: Set3.Lane → Nat → SingleLaneExpr)
  {expr: SingleLaneExpr}
  (eqBC:
    ∀ fv lane x,
      x ∈ expr.UsesConst →
      intp2 (map lane x) fv bDst cDst = (cSrc x).getLane lane)
  (eqCB:
    ∀ fv lane x,
      x ∈ expr.UsesConst →
      intp2 (map lane x) fv cDst bDst = (bSrc x).getLane lane)
:
  intp2 (expr.substConst map) fv bDst cDst = intp2 expr fv bSrc cSrc
:=
  match expr with
  | .const lane x => eqBC fv lane x rfl
  | .var _ => rfl
  | .null => rfl
  | .pair _ _ =>
    eq_intp2_pair_of_eq
      (substConst_intp2 map
        (fun fv lane x h => eqBC fv lane x (Or.inl h))
        (fun fv lane x h => eqCB fv lane x (Or.inl h)))
      (substConst_intp2 map
        (fun fv lane x h => eqBC fv lane x (Or.inr h))
        (fun fv lane x h => eqCB fv lane x (Or.inr h)))
  | .ir _ _ =>
    eq_intp2_ir_of_eq
      (substConst_intp2 map
        (fun fv lane x h => eqBC fv lane x (Or.inl h))
        (fun fv lane x h => eqCB fv lane x (Or.inl h)))
      (substConst_intp2 map
        (fun fv lane x h => eqBC fv lane x (Or.inr h))
        (fun fv lane x h => eqCB fv lane x (Or.inr h)))
  | .full _ =>
    eq_intp2_full_of_eq (substConst_intp2 map eqBC eqCB)
  | .compl _ =>
    eq_intp2_compl_of_eq (substConst_intp2 map eqCB eqBC)
  | .arbIr _ =>
    eq_intp2_arbIr_of_eq fun _ => substConst_intp2 map eqBC eqCB

def SingleLaneExpr.mapConst_intp2 {fv bSrc bDst cSrc cDst}
  (map: Nat → Nat)
  {expr: SingleLaneExpr}
  (eqB: ∀ x ∈ expr.UsesConst, bSrc x = bDst (map x))
  (eqC: ∀ x ∈ expr.UsesConst, cSrc x = cDst (map x))
:
  intp2 (expr.mapConst map) fv bDst cDst = intp2 expr fv bSrc cSrc
:=
  substConst_intp2
    (fun lane x => .const lane (map x))
    (fun _ lane x h =>
      (congrArg (fun s => s.getLane lane) (eqC x h)).symm)
    (fun _ lane x h =>
      (congrArg (fun s => s.getLane lane) (eqB x h)).symm)


namespace BasicExpr
  def toLane_UsesConst
    (expr: BasicExpr)
    (lane: Set3.Lane)
  :
    (expr.toLane lane).UsesConst = expr.UsesConst
  :=
    funext fun x => by
      induction expr generalizing lane with
      | const y => rfl
      | var y => rfl
      | null => rfl
      | pair left rite ihL ihR =>
        exact propext <| Iff.intro
          (fun h => h.elim
            (Or.inl ∘ ((ihL lane).mp))
            (Or.inr ∘ ((ihR lane).mp)))
          (fun h => h.elim
            (Or.inl ∘ ((ihL lane).mpr))
            (Or.inr ∘ ((ihR lane).mpr)))
      | ir left rite ihL ihR =>
        exact propext <| Iff.intro
          (fun h => h.elim
            (Or.inl ∘ ((ihL lane).mp))
            (Or.inr ∘ ((ihR lane).mp)))
          (fun h => h.elim
            (Or.inl ∘ ((ihL lane).mpr))
            (Or.inr ∘ ((ihR lane).mpr)))
      | full body ih =>
        exact propext <| Iff.intro (ih lane).mp (ih lane).mpr
      | compl body ih =>
        exact propext <| Iff.intro
          (ih lane.toggle).mp
          (ih lane.toggle).mpr
      | arbIr body ih =>
        exact propext <| Iff.intro (ih lane).mp (ih lane).mpr
  
  
  def toLane_substConst
    (expr: BasicExpr)
    (lane: Set3.Lane)
    (map: Nat → BasicExpr)
  :
    Eq
      (BasicExpr.toLane (expr.substConst (fun _ => map)) lane)
      ((expr.toLane lane).substConst
        (fun lane x => (map x).toLane lane))
  :=
    match expr with
    | .const _ => rfl
    | .var _ => rfl
    | .null => rfl
    | .pair left rite =>
      congrArg₂ SingleLaneExpr.pair
        (toLane_substConst left lane map)
        (toLane_substConst rite lane map)
    | .ir left rite =>
      congrArg₂ SingleLaneExpr.ir
        (toLane_substConst left lane map)
        (toLane_substConst rite lane map)
    | .full body =>
      congrArg SingleLaneExpr.full (toLane_substConst body lane map)
    | .compl body =>
      congrArg SingleLaneExpr.compl
        (toLane_substConst body lane.toggle map)
    | .arbIr body =>
      congrArg SingleLaneExpr.arbIr (toLane_substConst body lane map)
  
  def toLane_mapConst
    (expr: BasicExpr)
    (lane: Set3.Lane)
    (map: Nat → Nat)
  :
    Eq
      (BasicExpr.toLane (expr.mapConst map) lane)
      ((expr.toLane lane).mapConst map)
  :=
    toLane_substConst expr lane (.const ∘ map)
  
  
  def substConst_triIntp2
    (map: Nat → BasicExpr)
    {expr: BasicExpr}
    {fv: List Pair}
    {bSrc bDst cSrc cDst: Valuation Pair}
    (eqBC:
      ∀ fv x,
        x ∈ expr.UsesConst →
        triIntp2 (map x) fv bDst cDst = cSrc x)
    (eqCB:
      ∀ fv x,
        x ∈ expr.UsesConst →
        triIntp2 (map x) fv cDst bDst = bSrc x)
  :
    Eq
      (triIntp2 (expr.substConst (fun _ => map)) fv bDst cDst)
      (expr.triIntp2 fv bSrc cSrc)
  :=
    let usesEq := toLane_UsesConst expr
    Set3.eq
      (show SingleLaneExpr.intp2 _ _ _ _ = _ from
      toLane_substConst expr .defLane map ▸
      SingleLaneExpr.substConst_intp2
        (fun lane x => (map x).toLane lane)
        (fun fv lane x hx =>
          BasicExpr.triIntp2_getLane_eq (expr := map x) ▸
          congrArg
            (fun s => s.getLane lane)
            (eqBC fv x ((congrFun (usesEq .defLane) x).mp hx)))
        (fun fv lane x hx =>
          BasicExpr.triIntp2_getLane_eq (expr := map x) ▸
          congrArg
            (fun s => s.getLane lane)
            (eqCB fv x ((congrFun (usesEq .defLane) x).mp hx))))
      (show SingleLaneExpr.intp2 _ _ _ _ = _ from
      toLane_substConst expr .posLane map ▸
      SingleLaneExpr.substConst_intp2
        (fun lane x => (map x).toLane lane)
        (fun fv lane x hx =>
          BasicExpr.triIntp2_getLane_eq (expr := map x) ▸
          congrArg
            (fun s => s.getLane lane)
            (eqBC fv x ((congrFun (usesEq .posLane) x).mp hx)))
        (fun fv lane x hx =>
          BasicExpr.triIntp2_getLane_eq (expr := map x) ▸
          congrArg
            (fun s => s.getLane lane)
            (eqCB fv x ((congrFun (usesEq .posLane) x).mp hx))))
  
  def mapConst_triIntp2
    (map: Nat → Nat)
    {expr: BasicExpr}
    {fv: List Pair}
    {bSrc bDst cSrc cDst: Valuation Pair}
    (eqB: ∀ x ∈ expr.UsesConst, bSrc x = bDst (map x))
    (eqC: ∀ x ∈ expr.UsesConst, cSrc x = cDst (map x))
  :
    Eq
      (triIntp2 (expr.mapConst map) fv bDst cDst)
      (expr.triIntp2 fv bSrc cSrc)
  :=
    substConst_triIntp2
      (fun x => .const (map x))
      (fun _ x hx => (eqC x hx).symm)
      (fun _ x hx => (eqB x hx).symm)

end BasicExpr
