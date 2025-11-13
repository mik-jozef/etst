import Etst.WFC.Utils.Expr
import Etst.WFC.Utils.Valuation

namespace Etst


namespace SingleLaneExpr.interpretation_mono_std
  def CtxLe (c0 c1: Valuation D):
    Option SingleLaneVarType → Prop
  | .none => (x: Nat) → c0 x ≤ c1 x
  | .some .defLane => ∀ x: Nat, (c0 x).defMem ⊆ (c1 x).defMem
  | .some .posLane => ∀ x: Nat, (c0 x).posMem ⊆ (c1 x).posMem
  
  def LaneEq (expr: SingleLaneExpr sig kind):
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
  
end SingleLaneExpr.interpretation_mono_std


open SingleLaneExpr.interpretation_mono_std in
def SingleLaneExpr.interpretation_mono_std
  {c0 c1: Valuation salg.D}
  (premiseType: Option SingleLaneVarType)
  (cLe: CtxLe c0 c1 premiseType)
  (laneEq: LaneEq expr premiseType)
:
  Set.Subset
    (expr.interpretation salg bv b c0)
    (expr.interpretation salg bv b c1)
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
    | .op opr args =>
      let defMem0 param := (args param).interpretation salg bv b c0
      let defMem1 param := (args param).interpretation salg bv b c1
      let laneEq param := laneEq.map (fun eq => .elimOp eq param)
      let isLe param := interpretation_mono_std premiseType cLe (laneEq param)
      salg.isMonotonic opr defMem0 defMem1 isLe dIn
    | .compl _ => dIn -- Note: complement is not affected by context.
    | .arbUn _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      let laneEq := laneEq.map .elimArbUn
      ⟨dX, interpretation_mono_std premiseType cLe laneEq dXIn⟩
    | .arbIr _ =>
      let laneEq := laneEq.map .elimArbIr
      fun dX => interpretation_mono_std premiseType cLe laneEq (dIn dX)

def BasicExpr.interpretation_mono_std_defMem
  {c0 c1: Valuation salg.D}
  (cLe: ∀ x, (c0 x).defMem ≤ (c1 x).defMem)
  {expr: BasicExpr sig}
:
  (interpretation salg bv b c0 expr).defMem ⊆ (interpretation salg bv b c1 expr).defMem
:=
  SingleLaneExpr.interpretation_mono_std
    (.some .defLane)
    cLe
    (expr.posLaneEqCtx .defLane)

def BasicExpr.interpretation_mono_std_posMem
  {c0 c1: Valuation salg.D}
  (cLe: ∀ x, (c1 x).posMem ≤ (c0 x).posMem)
  {expr: BasicExpr sig}
:
  (interpretation salg bv b c1 expr).posMem ⊆ (interpretation salg bv b c0 expr).posMem
:=
  SingleLaneExpr.interpretation_mono_std
    (.some .posLane)
    cLe
    (expr.posLaneEqCtx .posLane)

def BasicExpr.interpretation_mono_std
  {c0 c1: Valuation salg.D}
  (cLe: c0 ≤ c1)
  {expr: BasicExpr sig}
:
  interpretation salg bv b c0 expr ≤ interpretation salg bv b c1 expr
:= {
  defLe := interpretation_mono_std_defMem (fun x => (cLe x).defLe),
  posLe := interpretation_mono_std_posMem (fun x => (cLe x).posLe)
}

def DefList.interpretation_mono_std
  {salg: Salgebra sig}
  {dl: DefList sig}
  {b: Valuation salg.D}
  {c0 c1: Valuation salg.D}
  (cLe: c0 ≤ c1)
:
  dl.interpretation salg b c0 ≤ dl.interpretation salg b c1
:=
  fun _ => BasicExpr.interpretation_mono_std cLe


def BasicExpr.interpretation_mono_apx
  {salg: Salgebra sig}
  {expr: BasicExpr sig}
  {bv: List salg.D}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  expr.interpretation salg bv b0 c0 ⊑ expr.interpretation salg bv b1 c1
:=
  match expr with
  | .var x => {
      defLe := fun _d dIn => (cLe x).defLe dIn
      posLe := fun _d dIn => (cLe x).posLe dIn
    }
  | .bvar _ => ⟨fun _ => id, fun _ => id⟩
  | .op opr args =>
      let ih _ := interpretation_mono_apx bLe cLe
      {
        defLe := fun _d dIn =>
          let defArgs0 arg :=
            (interpretation salg bv b0 c0 (args arg)).defMem
          let defArgs1 arg :=
            (interpretation salg bv b1 c1 (args arg)).defMem
          
          let defArgsLe := salg.isMonotonic
            opr defArgs0 defArgs1 (fun a => (ih a).defLe)
          
          defArgsLe dIn
        posLe := fun _d dIn =>
          let posArgs0 arg :=
            (interpretation salg bv b0 c0 (args arg)).posMem
          let posArgs1 arg :=
            (interpretation salg bv b1 c1 (args arg)).posMem
          
          let posArgsLe := salg.isMonotonic
            opr posArgs1 posArgs0 (fun a => (ih a).posLe)
          
          posArgsLe dIn
      }
  | .compl _ =>
      let ih := interpretation_mono_apx bLe bLe
      {
        defLe := fun d dIn =>
          let tmp: (d: salg.D) → _ → _ := ih.posLe
          not_imp_not.mpr (tmp d) dIn
        posLe := fun d dIn =>
          let tmp: (d: salg.D) → _ → _ := ih.defLe
          not_imp_not.mpr (tmp d) dIn
      }
  | .arbUn _ =>
      let ih _d := interpretation_mono_apx bLe cLe
      {
        defLe := fun _d ⟨dX, dXIn⟩ => ⟨dX, (ih dX).defLe dXIn⟩
        posLe := fun _d ⟨dX, dXIn⟩ => ⟨dX, (ih dX).posLe dXIn⟩
      }
  | .arbIr _ =>
      let ih _d := interpretation_mono_apx bLe cLe
      {
        defLe := fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1)
        posLe := fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0)
      }

def BasicExpr.interpretation_mono_apx_defMem
  {expr: BasicExpr sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
:
  Set.Subset
    (expr.interpretation salg bv b0 c0).defMem
    (expr.interpretation salg bv b1 c1).defMem
:=
  let c0LeSelf := (Valuation.ordApx salg.D).le_refl c0
  let isMonoB := interpretation_mono_apx bLe c0LeSelf
  let isMonoC := interpretation_mono_std_defMem cLeDef
  isMonoB.defLe.trans isMonoC

def BasicExpr.interpretation_mono_apx_posMem
  {expr: BasicExpr sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
:
  Set.Subset
    (expr.interpretation salg bv b1 c1).posMem
    (expr.interpretation salg bv b0 c0).posMem
:=
  let c0LeSelf := (Valuation.ordApx salg.D).le_refl c1
  let isMonoB := interpretation_mono_apx bLe c0LeSelf
  let isMonoC := interpretation_mono_std_posMem cLePos
  isMonoB.posLe.trans isMonoC

def DefList.interpretation_mono_apx
  {salg: Salgebra sig}
  {dl: DefList sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  dl.interpretation salg b0 c0 ⊑ dl.interpretation salg b1 c1
:=
  fun _ => BasicExpr.interpretation_mono_apx bLe cLe
