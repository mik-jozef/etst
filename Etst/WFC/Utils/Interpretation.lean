import Etst.WFC.Utils.Expr
import Etst.WFC.Utils.Valuation

namespace Etst


namespace SingleLaneExpr.intp2_mono_std
  def CtxLe (c0 c1: Valuation D):
    Option SingleLaneVarType → Prop
  | .none => (x: Nat) → c0 x ≤ c1 x
  | .some .defLane => ∀ x: Nat, (c0 x).defMem ⊆ (c1 x).defMem
  | .some .posLane => ∀ x: Nat, (c0 x).posMem ⊆ (c1 x).posMem
  
  def LaneEq (expr: SingleLaneExpr):
    Option SingleLaneVarType → Prop
  | .none => True
  | .some lane => expr.LaneEqCtx lane
  
  def LaneEq.map
    (laneEq: LaneEq expr premiseType)
    (laneMap:
      {lane: _} →
      expr.LaneEqCtx lane →
      Expr.LaneEqCtx lane exprOut)
  :
    LaneEq exprOut premiseType
  :=
    match premiseType with
    | .none => trivial
    | .some _ => laneMap laneEq
  
end SingleLaneExpr.intp2_mono_std


open SingleLaneExpr.intp2_mono_std in
def SingleLaneExpr.intp2_mono_std
  {c0 c1: Valuation Pair}
  (premiseType: Option SingleLaneVarType)
  (cLe: CtxLe c0 c1 premiseType)
  (laneEq: LaneEq expr premiseType)
:
  Set.Subset
    (expr.intp2 bv b c0)
    (expr.intp2 bv b c1)
:=
  fun _ dIn =>
    match expr with
    | .var lane x =>
      match lane, premiseType with
      | .defLane, .none => (cLe x).defLe dIn
      | .posLane, .none => (cLe x).posLe dIn
      | .defLane, .some .defLane => cLe x dIn
      | .posLane, .some .posLane => cLe x dIn
    | .bvar _ => dIn
    | .null => dIn
    | .pair _ _ =>
      let ⟨dL, dR, eq, dLIn, dRIn⟩ := dIn
      let ihL := intp2_mono_std
        premiseType cLe (laneEq.map .elimPairLeft) dLIn
      let ihR := intp2_mono_std
        premiseType cLe (laneEq.map .elimPairRite) dRIn
      ⟨dL, dR, eq, ihL, ihR⟩
    | .un _ _ =>
      dIn.elim
        (fun dL =>
          let ihL := intp2_mono_std
            premiseType cLe (laneEq.map .elimUnLeft) dL
          Or.inl ihL)
        (fun dR =>
          let ihR := intp2_mono_std
            premiseType cLe (laneEq.map .elimUnRite) dR
          Or.inr ihR)
    | .ir _ _ =>
      let ⟨dLIn, dRIn⟩ := dIn
      let ihL := intp2_mono_std
        premiseType cLe (laneEq.map .elimIrLeft) dLIn
      let ihR := intp2_mono_std
        premiseType cLe (laneEq.map .elimIrRite) dRIn
      ⟨ihL, ihR⟩
    | .condSome _ =>
      let ⟨_dB, dBIn⟩ := dIn
      let ih := intp2_mono_std
        premiseType cLe (laneEq.map .elimCondSome) dBIn
      ⟨_, ih⟩
    | .condFull _ =>
      fun dB =>
        intp2_mono_std premiseType cLe (laneEq.map .elimCondFull) (dIn dB)
    | .compl _ => dIn -- Note: complement is not affected by context.
    | .arbUn _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      let laneEq := laneEq.map .elimArbUn
      ⟨dX, intp2_mono_std premiseType cLe laneEq dXIn⟩
    | .arbIr _ =>
      let laneEq := laneEq.map .elimArbIr
      fun dX => intp2_mono_std premiseType cLe laneEq (dIn dX)

def BasicExpr.triIntp2_mono_std_defMem
  {c0 c1: Valuation Pair}
  (cLe: ∀ x, (c0 x).defMem ≤ (c1 x).defMem)
  {expr: BasicExpr}
:
  (expr.triIntp2 bv b c0).defMem ⊆ (expr.triIntp2 bv b c1).defMem
:=
  SingleLaneExpr.intp2_mono_std
    (.some .defLane)
    cLe
    (expr.laneEqCtx .defLane)

def BasicExpr.triIntp2_mono_std_posMem
  {c0 c1: Valuation Pair}
  (cLe: ∀ x, (c1 x).posMem ≤ (c0 x).posMem)
  {expr: BasicExpr}
:
  (expr.triIntp2 bv b c1).posMem ⊆ (expr.triIntp2 bv b c0).posMem
:=
  SingleLaneExpr.intp2_mono_std
    (.some .posLane)
    cLe
    (expr.laneEqCtx .posLane)

def BasicExpr.triIntp2_mono_std
  {c0 c1: Valuation Pair}
  (cLe: c0 ≤ c1)
  {expr: BasicExpr}
:
  expr.triIntp2 bv b c0 ≤ expr.triIntp2 bv b c1
:= {
  defLe := triIntp2_mono_std_defMem (fun x => (cLe x).defLe),
  posLe := triIntp2_mono_std_posMem (fun x => (cLe x).posLe)
}

def DefList.triIntp2_mono_std
  {dl: DefList}
  {b: Valuation Pair}
  {c0 c1: Valuation Pair}
  (cLe: c0 ≤ c1)
:
  dl.triIntp2 b c0 ≤ dl.triIntp2 b c1
:=
  fun _ => BasicExpr.triIntp2_mono_std cLe


def BasicExpr.triIntp2_mono_apx
  {expr: BasicExpr}
  {bv: List Pair}
  {b0 b1 c0 c1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  expr.triIntp2 bv b0 c0 ⊑ expr.triIntp2 bv b1 c1
:=
  match expr with
  | .var x => {
      defLe := fun _d dIn => (cLe x).defLe dIn
      posLe := fun _d dIn => (cLe x).posLe dIn
    }
  | .bvar _ => ⟨fun _ => id, fun _ => id⟩
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
  | .un _ _ =>
      let ihL := triIntp2_mono_apx bLe cLe
      let ihR := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d dIn =>
          dIn.elim
            (fun dL => Or.inl (ihL.defLe dL))
            (fun dR => Or.inr (ihR.defLe dR))
        posLe := fun _d dIn =>
          dIn.elim
            (fun dL => Or.inl (ihL.posLe dL))
            (fun dR => Or.inr (ihR.posLe dR))
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
  | .condSome _ =>
      let ih := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d ⟨dB, dBIn⟩ => ⟨dB, ih.defLe dBIn⟩
        posLe := fun _d ⟨dB, dBIn⟩ => ⟨dB, ih.posLe dBIn⟩
      }
  | .condFull _ =>
      let ih := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d dIn dB => ih.defLe (dIn dB)
        posLe := fun _d dIn dB => ih.posLe (dIn dB)
      }
  | .compl _ =>
      let ih := triIntp2_mono_apx bLe bLe
      {
        defLe := fun d dIn =>
          let tmp: (d: Pair) → _ → _ := ih.posLe
          not_imp_not.mpr (tmp d) dIn
        posLe := fun d dIn =>
          let tmp: (d: Pair) → _ → _ := ih.defLe
          not_imp_not.mpr (tmp d) dIn
      }
  | .arbUn _ =>
      let ih _d := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d ⟨dX, dXIn⟩ => ⟨dX, (ih dX).defLe dXIn⟩
        posLe := fun _d ⟨dX, dXIn⟩ => ⟨dX, (ih dX).posLe dXIn⟩
      }
  | .arbIr _ =>
      let ih _d := triIntp2_mono_apx bLe cLe
      {
        defLe := fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1)
        posLe := fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0)
      }

def BasicExpr.triIntp2_mono_apx_defMem
  {expr: BasicExpr}
  {b0 b1 c0 c1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
:
  Set.Subset
    (expr.triIntp2 bv b0 c0).defMem
    (expr.triIntp2 bv b1 c1).defMem
:=
  let c0LeSelf := (Valuation.ordApx Pair).le_refl c0
  let isMonoB := triIntp2_mono_apx bLe c0LeSelf
  let isMonoC := triIntp2_mono_std_defMem cLeDef
  isMonoB.defLe.trans isMonoC

def BasicExpr.triIntp2_mono_apx_posMem
  {expr: BasicExpr}
  {b0 b1 c0 c1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
:
  Set.Subset
    (expr.triIntp2 bv b1 c1).posMem
    (expr.triIntp2 bv b0 c0).posMem
:=
  let c0LeSelf := (Valuation.ordApx Pair).le_refl c1
  let isMonoB := triIntp2_mono_apx bLe c0LeSelf
  let isMonoC := triIntp2_mono_std_posMem cLePos
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
