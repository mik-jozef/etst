/-
  Proves that structurally identical definitions define the same
  (three-valued) sets.
-/

import Etst.WFC.Utils.InterpretationMono

namespace Etst


def Expr.mapConst {E}
  (map: Nat → Nat)
:
  Expr E → Expr E
|
  .const e x => .const e (map x)
| .var x => .var x
| .null => .null
| .pair l r => .pair (l.mapConst map) (r.mapConst map)
| .ir l r => .ir (l.mapConst map) (r.mapConst map)
| .full b => .full (b.mapConst map)
| .compl b => .compl (b.mapConst map)
| .arbIr b => .arbIr (b.mapConst map)

def Expr.mapConst_eq_id {E}
  (expr: Expr E)
:
  expr.mapConst id = expr
:=
  match expr with
  | .const _ _ => rfl
  | .var _ => rfl
  | .null => rfl
  | .pair left rite =>
    congrArg₂ Expr.pair
      (Expr.mapConst_eq_id left)
      (Expr.mapConst_eq_id rite)
  | .ir left rite =>
    congrArg₂ Expr.ir
      (Expr.mapConst_eq_id left)
      (Expr.mapConst_eq_id rite)
  | .full body =>
    congrArg Expr.full (Expr.mapConst_eq_id body)
  | .compl body =>
    congrArg Expr.compl (Expr.mapConst_eq_id body)
  | .arbIr body =>
    congrArg Expr.arbIr (Expr.mapConst_eq_id body)


/-
  Proves that renaming constants preserves interpretation when the
  source and target valuations agree on all constants used by the
  expression.
-/
def SingleLaneExpr.mapConst_intp2 {fv bSrc bDst cSrc cDst}
  (map: Nat → Nat)
  {expr: SingleLaneExpr}
  (eqB: ∀ x ∈ expr.UsesConst, bSrc x = bDst (map x))
  (eqC: ∀ x ∈ expr.UsesConst, cSrc x = cDst (map x))
:
  intp2 (expr.mapConst map) fv bDst cDst = intp2 expr fv bSrc cSrc
:=
  match expr with
  | .const lane x =>
    (congrArg (fun s => s.getLane lane) (eqC x rfl)).symm
  | .var _ => rfl
  | .null => rfl
  | .pair _ _ =>
    eq_intp2_pair_of_eq
      (mapConst_intp2 map
        (fun x h => eqB x (Or.inl h))
        (fun x h => eqC x (Or.inl h)))
      (mapConst_intp2 map
        (fun x h => eqB x (Or.inr h))
        (fun x h => eqC x (Or.inr h)))
  | .ir _ _ =>
    eq_intp2_ir_of_eq
      (mapConst_intp2 map
        (fun x h => eqB x (Or.inl h))
        (fun x h => eqC x (Or.inl h)))
      (mapConst_intp2 map
        (fun x h => eqB x (Or.inr h))
        (fun x h => eqC x (Or.inr h)))
  | .full _ =>
    eq_intp2_full_of_eq (mapConst_intp2 map eqB eqC)
  | .compl _ =>
    eq_intp2_compl_of_eq (mapConst_intp2 map eqC eqB)
  | .arbIr _ =>
    eq_intp2_arbIr_of_eq fun _ => mapConst_intp2 map eqB eqC

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
  
  def toLane_mapConst
    (expr: BasicExpr)
    (lane: Set3.Lane)
    (map: Nat → Nat)
  :
    BasicExpr.toLane (expr.mapConst map) lane = (expr.toLane lane).mapConst map
  :=
    match expr with
    | .const _ => rfl
    | .var _ => rfl
    | .null => rfl
    | .pair left rite =>
      congrArg₂ SingleLaneExpr.pair
        (toLane_mapConst left lane map)
        (toLane_mapConst rite lane map)
    | .ir left rite =>
      congrArg₂ SingleLaneExpr.ir
        (toLane_mapConst left lane map)
        (toLane_mapConst rite lane map)
    | .full body =>
      congrArg SingleLaneExpr.full (toLane_mapConst body lane map)
    | .compl body =>
      congrArg SingleLaneExpr.compl (toLane_mapConst body lane.toggle map)
    | .arbIr body =>
      congrArg SingleLaneExpr.arbIr (toLane_mapConst body lane map)
  
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
    let usesEq := toLane_UsesConst expr
    Set3.eq
      (show SingleLaneExpr.intp2 _ _ _ _ = _ from
      toLane_mapConst expr .defLane map ▸
      SingleLaneExpr.mapConst_intp2
        map
        (fun x hx => eqB x ((congrFun (usesEq .defLane) x).mp hx))
        (fun x hx => eqC x ((congrFun (usesEq .defLane) x).mp hx)))
      (show SingleLaneExpr.intp2 _ _ _ _ = _ from
      toLane_mapConst expr .posLane map ▸
      SingleLaneExpr.mapConst_intp2
          map
          (fun x hx => eqB x ((congrFun (usesEq .posLane) x).mp hx))
          (fun x hx => eqC x ((congrFun (usesEq .posLane) x).mp hx)))

end BasicExpr
