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
  fun _ pIn =>
    match expr with
    | .const lane x =>
      match lane, even, laneEq with
      | .defLane, .none, .constNone => (cLe x).defLe pIn
      | .posLane, .none, .constNone => (cLe x).posLe pIn
      | .defLane, .some .defLane, .constSome => cLe x pIn
      | .posLane, .some .posLane, .constSome => cLe x pIn
    | .var _ => pIn
    | .null => pIn
    | .pair _ _ =>
      let ⟨pL, pR, eq, pLIn, pRIn⟩ := pIn
      let ihL := intp2_mono_std bLe cLe laneEq.elimPairLeft pLIn
      let ihR := intp2_mono_std bLe cLe laneEq.elimPairRite pRIn
      ⟨pL, pR, eq, ihL, ihR⟩
    | .ir _ _ =>
      let ⟨pLIn, pRIn⟩ := pIn
      let ihL := intp2_mono_std bLe cLe laneEq.elimIrLeft pLIn
      let ihR := intp2_mono_std bLe cLe laneEq.elimIrRite pRIn
      ⟨ihL, ihR⟩
    | .full _ =>
      fun pB => intp2_mono_std bLe cLe laneEq.elimFull (pIn pB)
    | .compl _ =>
      let ih := intp2_mono_std cLe bLe laneEq.elimCompl
      (Set.compl_subset_compl.mpr ih) pIn
    | .arbIr _ =>
      fun pX => intp2_mono_std bLe cLe laneEq.elimArbIr (pIn pX)

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

def DefList.intpDefs2_mono_std
  {dl: DefList}
  {b0 b1} (bLe: b1 ≤ b0)
  {c0 c1} (cLe: c0 ≤ c1)
:
  dl.intpDefs2 b0 c0 ≤ dl.intpDefs2 b1 c1
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
      defLe _p pIn := (cLe x).defLe pIn
      posLe _p pIn := (cLe x).posLe pIn
    }
  | .var _ => ⟨fun _ => id, fun _ => id⟩
  | .null => ⟨fun _ => id, fun _ => id⟩
  | .pair _ _ =>
      let ihL := triIntp2_mono_apx bLe cLe
      let ihR := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _p ⟨pL, pR, eq, pLIn, pRIn⟩ =>
          ⟨pL, pR, eq, ihL.defLe pLIn, ihR.defLe pRIn⟩
        posLe := fun _p ⟨pL, pR, eq, pLIn, pRIn⟩ =>
          ⟨pL, pR, eq, ihL.posLe pLIn, ihR.posLe pRIn⟩
      }
  | .ir _ _ =>
      let ihL := triIntp2_mono_apx bLe cLe
      let ihR := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _p ⟨pLIn, pRIn⟩ =>
          ⟨ihL.defLe pLIn, ihR.defLe pRIn⟩
        posLe := fun _p ⟨pLIn, pRIn⟩ =>
          ⟨ihL.posLe pLIn, ihR.posLe pRIn⟩
      }
  | .full _ =>
      let ih := triIntp2_mono_apx bLe cLe
      {
        defLe _p pIn pB := ih.defLe (pIn pB)
        posLe _p pIn pB := ih.posLe (pIn pB)
      }
  | .compl _ =>
      let ih := triIntp2_mono_apx cLe bLe
      {
        defLe p pIn :=
          let tmp: (p: Pair) → _ → _ := ih.posLe
          not_imp_not.mpr (tmp p) pIn
        posLe p pIn :=
          let tmp: (p: Pair) → _ → _ := ih.defLe
          not_imp_not.mpr (tmp p) pIn
      }
  | .arbIr _ =>
      let ih _d := triIntp2_mono_apx bLe cLe
      {
        defLe _p pIn pXPos1 := (ih pXPos1).defLe (pIn pXPos1)
        posLe _p pIn pXPos0 := (ih pXPos0).posLe (pIn pXPos0)
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

def DefList.intpDefs2_mono_apx
  {dl: DefList}
  {b0 b1 c0 c1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  dl.intpDefs2 b0 c0 ⊑ dl.intpDefs2 b1 c1
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
