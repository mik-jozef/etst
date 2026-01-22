import Etst.WFC.Utils.Expr.Basic
import Etst.WFC.Utils.Valuation

namespace Etst


namespace SingleLaneExpr.intp2_mono_std
  def CtxLe {D} (c0 c1: Valuation D):
    Option Set3.Lane → Prop
  | .none => ∀ x: Nat, c0 x ≤ c1 x
  | .some .defLane => ∀ x: Nat, (c0 x).defMem ⊆ (c1 x).defMem
  | .some .posLane => ∀ x: Nat, (c0 x).posMem ⊆ (c1 x).posMem
  
  def LaneEq (expr: SingleLaneExpr) (ed: Bool):
    Option Set3.Lane → Prop
  | .none => True
  | .some lane => expr.LaneEqEven lane ed
  
  def LaneEq.map {expr edIn premiseType}
    (laneEq: LaneEq expr edIn premiseType)
    {edOut exprOut} (laneMap:
      {lane: _} →
      expr.LaneEqEven lane edIn →
      exprOut.LaneEqEven lane edOut)
  :
    LaneEq exprOut edOut premiseType
  :=
    match premiseType with
    | .none => trivial
    | .some _ => laneMap laneEq
  
end SingleLaneExpr.intp2_mono_std


/-
  The interpretation function is monotonic in the context and
  antimonotonic in the background with respect to the standard
  ordering.
  
  The boolean `ed`, short for `isEvenDepth`, can be understood
  in two equivalent ways:
  0. it represents whether the expression is thought of as
     being under an even number of complements in a larger
     expression;
  1. it is a flag indicating whether we're proving monotonicity
     in the context, or antimonotonicity in the background.
-/
open SingleLaneExpr.intp2_mono_std in
def SingleLaneExpr.intp2_mono_std {fv b}
  (premiseType: Option Set3.Lane)
  {c0 c1} (cLe: CtxLe c0 c1 premiseType)
  {expr ed} (laneEq: LaneEq expr ed premiseType)
:
  Set.Subset
    (expr.intp2 fv (ite ed b c1) (ite ed c0 b))
    (expr.intp2 fv (ite ed b c0) (ite ed c1 b))
:=
  fun _ dIn =>
    match expr with
    | .const lane x =>
      match lane, ed, premiseType with
      | _, false, _ => dIn
      | .defLane, true, .none => (cLe x).defLe dIn
      | .posLane, true, .none => (cLe x).posLe dIn
      | .defLane, true, .some .defLane => cLe x dIn
      | .posLane, true, .some .posLane => cLe x dIn
    | .var _ => dIn
    | .null => dIn
    | .pair _ _ =>
      let ⟨dL, dR, eq, dLIn, dRIn⟩ := dIn
      let ihL := intp2_mono_std
        premiseType cLe (laneEq.map .elimPairLeft) dLIn
      let ihR := intp2_mono_std
        premiseType cLe (laneEq.map .elimPairRite) dRIn
      ⟨dL, dR, eq, ihL, ihR⟩
    | .ir _ _ =>
      let ⟨dLIn, dRIn⟩ := dIn
      let ihL := intp2_mono_std
        premiseType cLe (laneEq.map .elimIrLeft) dLIn
      let ihR := intp2_mono_std
        premiseType cLe (laneEq.map .elimIrRite) dRIn
      ⟨ihL, ihR⟩
    | .full _ =>
      fun dB => intp2_mono_std
        premiseType cLe (laneEq.map .elimFull) (dIn dB)
    | .compl _ =>
      match ed with
      | true =>
        let ih := intp2_mono_std
          premiseType cLe (laneEq.map .elimCompl)
        (Set.compl_subset_compl.mpr ih) dIn
      | false =>
        let ih := intp2_mono_std
          premiseType cLe (laneEq.map .elimCompl)
        (Set.compl_subset_compl.mpr ih) dIn
    | .arbIr _ =>
      let laneEq := laneEq.map .elimArbIr
      fun dX => intp2_mono_std premiseType cLe laneEq (dIn dX)

def BasicExpr.triIntp2_mono_std_defMem
  {c0 c1} (cLe: ∀ x, (c0 x).defMem ≤ (c1 x).defMem)
  {expr: BasicExpr}
  (ed: Bool)
  {fv b}
:
  let lane: Set3.Lane := ite ed .defLane .posLane
  Subset
    ((expr.triIntp2 fv (ite ed b c1) (ite ed c0 b)).getLane lane)
    ((expr.triIntp2 fv (ite ed b c0) (ite ed c1 b)).getLane lane)
:= by
  cases ed <;>
  exact
    SingleLaneExpr.intp2_mono_std
      (.some .defLane)
      cLe
      (expr.laneEqEven .defLane _)

def BasicExpr.triIntp2_mono_std_posMem
  {c0 c1: Valuation Pair}
  (cLe: ∀ x, (c0 x).posMem ≤ (c1 x).posMem)
  {expr: BasicExpr}
  (ed: Bool)
  {fv b}
:
  let lane: Set3.Lane := ite ed .posLane .defLane
  Subset
    ((expr.triIntp2 fv (ite ed b c1) (ite ed c0 b)).getLane lane)
    ((expr.triIntp2 fv (ite ed b c0) (ite ed c1 b)).getLane lane)
:= by
  cases ed <;>
  exact
    SingleLaneExpr.intp2_mono_std
      (.some .posLane)
      cLe
      (expr.laneEqEven .posLane _)

def BasicExpr.triIntp2_mono_std
  {c0 c1: Valuation Pair}
  (cLe: c0 ≤ c1)
  {expr: BasicExpr}
  (ed: Bool)
  {fv b}
:
  Set3.LeStd
    (expr.triIntp2 fv (ite ed b c1) (ite ed c0 b))
    (expr.triIntp2 fv (ite ed b c0) (ite ed c1 b))
:=
  match ed with
  | true =>
    {
      defLe := SingleLaneExpr.intp2_mono_std .none cLe trivial
      posLe := SingleLaneExpr.intp2_mono_std .none cLe trivial
    }
  | false =>
    {
      defLe := SingleLaneExpr.intp2_mono_std .none cLe trivial
      posLe := SingleLaneExpr.intp2_mono_std .none cLe trivial
    }

def DefList.triIntp2_mono_std
  {dl: DefList}
  {b: Valuation Pair}
  {c0 c1: Valuation Pair}
  (cLe: c0 ≤ c1)
:
  dl.triIntp2 b c0 ≤ dl.triIntp2 b c1
:=
  fun _ => BasicExpr.triIntp2_mono_std cLe (ed := true)


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
  let isMonoC := triIntp2_mono_std_defMem cLeDef true
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
  let isMonoC := triIntp2_mono_std_posMem cLePos true
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
