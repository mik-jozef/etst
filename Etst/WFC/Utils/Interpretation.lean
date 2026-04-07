import Etst.WFC.Utils.Expr.Basic
import Etst.WFC.Utils.Valuation

namespace Etst


/-
  The interpretation function is monotonic in the context and
  antimonotonic in the background with respect to the standard
  ordering.

  The parameters `even` and `odd` constrain which lanes may occur
  at even and odd complement depth, respectively. When one of them
  is `.none`, that parity is left unconstrained.
-/
def SingleLaneExpr.intp2_mono_std {fv}
  {even odd: Option Set3.Lane}
  {b0 b1 c0 c1}
  (bLe: Valuation.LaneLe b1 b0 odd)
  (cLe: Valuation.LaneLe c0 c1 even)
  {expr: SingleLaneExpr} (laneEq: expr.LaneEq even odd)
:
  expr.intp2 fv b0 c0 ⊆ expr.intp2 fv b1 c1
:=
  fun _ dIn =>
    match expr with
    | .const lane x =>
      match lane, even, laneEq with
      | .defLane, .none, .constNone => (cLe x).defLe dIn
      | .posLane, .none, .constNone => (cLe x).posLe dIn
      | .defLane, .some .defLane, .constSome => cLe x dIn
      | .posLane, .some .posLane, .constSome => cLe x dIn
    | .var _ => dIn
    | .null => dIn
    | .pair _ _ =>
      let ⟨dL, dR, eq, dLIn, dRIn⟩ := dIn
      let ihL := intp2_mono_std bLe cLe laneEq.elimPairLeft dLIn
      let ihR := intp2_mono_std bLe cLe laneEq.elimPairRite dRIn
      ⟨dL, dR, eq, ihL, ihR⟩
    | .ir _ _ =>
      let ⟨dLIn, dRIn⟩ := dIn
      let ihL := intp2_mono_std bLe cLe laneEq.elimIrLeft dLIn
      let ihR := intp2_mono_std bLe cLe laneEq.elimIrRite dRIn
      ⟨ihL, ihR⟩
    | .full _ =>
      fun dB => intp2_mono_std bLe cLe laneEq.elimFull (dIn dB)
    | .compl _ =>
      let ih := intp2_mono_std cLe bLe laneEq.elimCompl
      (Set.compl_subset_compl.mpr ih) dIn
    | .arbIr _ =>
      fun dX => intp2_mono_std bLe cLe laneEq.elimArbIr (dIn dX)

def BasicExpr.triIntp2_mono_std_defMem
  {b0 b1} (bLePos: ∀ x, (b1 x).posMem ≤ (b0 x).posMem)
  {c0 c1} (cLeDef: ∀ x, (c0 x).defMem ≤ (c1 x).defMem)
  {expr: BasicExpr}
  {fv}
:
  Set.Subset
    (expr.triIntp2 fv b0 c0).defMem
    (expr.triIntp2 fv b1 c1).defMem
:=
  SingleLaneExpr.intp2_mono_std
    (even := .some .defLane)
    (odd := .some .posLane)
    bLePos
    cLeDef
    (expr.laneEq .defLane)

def BasicExpr.triIntp2_mono_std_posMem
  {b0 b1} (bLeDef: ∀ x, (b1 x).defMem ≤ (b0 x).defMem)
  {c0 c1} (cLePos: ∀ x, (c0 x).posMem ≤ (c1 x).posMem)
  {expr: BasicExpr}
  {fv}
:
  Set.Subset
    (expr.triIntp2 fv b0 c0).posMem
    (expr.triIntp2 fv b1 c1).posMem
:=
  SingleLaneExpr.intp2_mono_std
    (even := .some .posLane)
    (odd := .some .defLane)
    bLeDef
    cLePos
    (expr.laneEq .posLane)

def BasicExpr.triIntp2_mono_std
  {b0 b1} (bLe: b1 ≤ b0)
  {c0 c1} (cLe: c0 ≤ c1)
  {expr: BasicExpr}
  {fv}
:
  expr.triIntp2 fv b0 c0 ≤ expr.triIntp2 fv b1 c1
:=
  {
    defLe :=
      triIntp2_mono_std_defMem
        (fun x => (bLe x).posLe)
        (fun x => (cLe x).defLe)
    posLe :=
      triIntp2_mono_std_posMem
        (fun x => (bLe x).defLe)
        (fun x => (cLe x).posLe)
  }

def DefList.triIntp2_mono_std
  {dl: DefList}
  {b0 b1} (bLe: b1 ≤ b0)
  {c0 c1} (cLe: c0 ≤ c1)
:
  dl.triIntp2 b0 c0 ≤ dl.triIntp2 b1 c1
:=
  fun _ => BasicExpr.triIntp2_mono_std bLe cLe


def BasicExpr.triIntp2_mono_apx
  {expr: BasicExpr}
  {fv b0 b1 c0 c1}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  expr.triIntp2 fv b0 c0 ⊑ expr.triIntp2 fv b1 c1
:=
  match expr with
  | .const x => {
      defLe := fun _d dIn => (cLe x).defLe dIn
      posLe := fun _d dIn => (cLe x).posLe dIn
    }
  | .var _ => ⟨fun _ => id, fun _ => id⟩
  | .null => ⟨fun _ => id, fun _ => id⟩
  | .pair _ _ =>
      let ihL := triIntp2_mono_apx bLe cLe
      let ihR := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d ⟨dL, dR, eq, dLIn, dRIn⟩ =>
          ⟨dL, dR, eq, ihL.defLe dLIn, ihR.defLe dRIn⟩
        posLe := fun _d ⟨dL, dR, eq, dLIn, dRIn⟩ =>
          ⟨dL, dR, eq, ihL.posLe dLIn, ihR.posLe dRIn⟩
      }
  | .ir _ _ =>
      let ihL := triIntp2_mono_apx bLe cLe
      let ihR := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d ⟨dLIn, dRIn⟩ =>
          ⟨ihL.defLe dLIn, ihR.defLe dRIn⟩
        posLe := fun _d ⟨dLIn, dRIn⟩ =>
          ⟨ihL.posLe dLIn, ihR.posLe dRIn⟩
      }
  | .full _ =>
      let ih := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d dIn dB => ih.defLe (dIn dB)
        posLe := fun _d dIn dB => ih.posLe (dIn dB)
      }
  | .compl _ =>
      let ih := triIntp2_mono_apx cLe bLe
      {
        defLe := fun d dIn =>
          let tmp: (d: Pair) → _ → _ := ih.posLe
          not_imp_not.mpr (tmp d) dIn
        posLe := fun d dIn =>
          let tmp: (d: Pair) → _ → _ := ih.defLe
          not_imp_not.mpr (tmp d) dIn
      }
  | .arbIr _ =>
      let ih _d := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1)
        posLe := fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0)
      }

def BasicExpr.triIntp2_mono_apx_defMem
  {expr: BasicExpr}
  {b0 b1} (bLe: b0 ⊑ b1)
  {c0 c1} (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
  {fv}
:
  Set.Subset
    (expr.triIntp2 fv b0 c0).defMem
    (expr.triIntp2 fv b1 c1).defMem
:=
  let c0LeSelf := (Valuation.ordApx Pair).le_refl c0
  let isMonoB := triIntp2_mono_apx bLe c0LeSelf
  let isMonoC := triIntp2_mono_std_defMem
    (fun _ => le_refl _)
    cLeDef
  isMonoB.defLe.trans isMonoC

def BasicExpr.triIntp2_mono_apx_posMem
  {expr: BasicExpr}
  {b0 b1} (bLe: b0 ⊑ b1)
  {c0 c1} (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
  {fv}
:
  Set.Subset
    (expr.triIntp2 fv b1 c1).posMem
    (expr.triIntp2 fv b0 c0).posMem
:=
  let c0LeSelf := (Valuation.ordApx Pair).le_refl c1
  let isMonoB := triIntp2_mono_apx bLe c0LeSelf
  let isMonoC := triIntp2_mono_std_posMem
    (fun _ => le_refl _)
    cLePos
  isMonoB.posLe.trans isMonoC

def DefList.triIntp2_mono_apx
  {dl: DefList}
  {b0 b1 c0 c1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  dl.triIntp2 b0 c0 ⊑ dl.triIntp2 b1 c1
:=
  fun _ => BasicExpr.triIntp2_mono_apx bLe cLe


def BasicExpr.triIntp2_getLane_eq {fv b c lane}
  (expr: BasicExpr)
:
  Eq
    ((expr.triIntp2 fv b c).getLane lane)
    ((expr.toLane lane).intp2 fv b c)
:=
  match lane with
  | .defLane => rfl
  | .posLane => rfl
