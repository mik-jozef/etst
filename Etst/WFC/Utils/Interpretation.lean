module
public import Etst.WFC.Utils.Expr.Basic
public import Etst.WFC.Utils.Valuation

public section
namespace Etst


-- An invariant for `intp_mono_std`, see below.
exposed def ExprKind.Lane.AgreesWith {kind}
  (kindLane: Lane kind)
  (even odd: Option Set3.Lane)
:
  Prop
:=
  match kind, kindLane, even, odd with
  | .basic, _, .none, .none => True
  | .basic, k, .none, .some o => k ≠ o
  | .basic, k, .some e, .none => k = e
  | .basic, k, .some e, .some o => k = e ∧ k ≠ o
  | .lane, (), _, _ => True

theorem ExprKind.Lane.AgreesWith.toggle {kind even odd}
  {lane: Lane kind}
  (laneAgrees: lane.AgreesWith even odd)
:
  lane.toggle.AgreesWith odd even
:=
  open Set3.Lane in
  match kind, even, odd with
  | .lane, _, _ => trivial
  | .basic, .none, .none => trivial
  | .basic, .none, .some _ => toggle_eq_iff.mpr laneAgrees
  | .basic, .some _, .none => toggle_ne_iff.mpr laneAgrees
  | .basic, .some _, .some _ => ⟨
      toggle_eq_iff.mpr laneAgrees.right,
      toggle_ne_iff.mpr laneAgrees.left
    ⟩

/-
  The interpretation function is monotonic in the context and
  antimonotonic in the background with respect to the standard
  ordering.
  
  For lane expressions, the parameters `even` and `odd` constrain
  which lanes may occur at even and odd complement depth, respectively.
  When one of them is `.none`, that parity is left unconstrained.
  Fewer constraints means more prerequisites for `bLe` and `cLe` to hold.
  
  `bLe` and `cLe` are guarantees that the input valuations are ordered
  on the lanes the expression may read given its lane constraints.
  
  `laneAgrees` is a guarantee that we only read the lanes for which
  we have a guarantee they are ordered.
-/
theorem Expr.intp_mono_std
  {b0 b1 c0 c1 even odd kind lane fv}
  (bLe: Valuation.LaneLe b1 b0 odd)
  (cLe: Valuation.LaneLe c0 c1 even)
  {expr: Expr kind}
  (laneEq: expr.LaneEq even odd)
  (laneAgrees: lane.AgreesWith even odd)
:
  expr.intp lane b0 c0 fv ⊆ expr.intp lane b1 c1 fv
:=
  fun _ pIn =>
    match expr with
    | .const tag x =>
      match kind with
      | .basic =>
        match lane, even, odd with
        | .defLane, .none, _ => (cLe x).defLe pIn
        | .posLane, .none, _ => (cLe x).posLe pIn
        | .defLane, .some .defLane, _ => cLe x pIn
        | .posLane, .some .posLane, _ => cLe x pIn
      | .lane =>
        match tag, even, laneEq with
        | .defLane, .none, .constLaneNone => (cLe x).defLe pIn
        | .posLane, .none, .constLaneNone => (cLe x).posLe pIn
        | .defLane, .some .defLane, .constLaneSome => cLe x pIn
        | .posLane, .some .posLane, .constLaneSome => cLe x pIn
    | .var _ => pIn
    | .null => pIn
    | .prod _ _ =>
      let ⟨pL, pR, eq, pLIn, pRIn⟩ := pIn
      let ihL := intp_mono_std bLe cLe laneEq.elimProdLeft laneAgrees pLIn
      let ihR := intp_mono_std bLe cLe laneEq.elimProdRite laneAgrees pRIn
      ⟨pL, pR, eq, ihL, ihR⟩
    | .ir _ _ =>
      let ⟨pLIn, pRIn⟩ := pIn
      let ihL := intp_mono_std bLe cLe laneEq.elimIrLeft laneAgrees pLIn
      let ihR := intp_mono_std bLe cLe laneEq.elimIrRite laneAgrees pRIn
      ⟨ihL, ihR⟩
    | .full _ =>
      fun pB => intp_mono_std bLe cLe laneEq.elimFull laneAgrees (pIn pB)
    | .compl _ =>
      let ih := intp_mono_std cLe bLe laneEq.elimCompl laneAgrees.toggle
      (Set.compl_subset_compl.mpr ih) pIn
    | .arbIr _ =>
      fun pX => intp_mono_std bLe cLe laneEq.elimArbIr laneAgrees (pIn pX)

theorem Expr.intp_mono_std_defMem
  {b0 b1} (bLePos: ∀ x, (b1 x).posMem ≤ (b0 x).posMem)
  {c0 c1} (cLeDef: ∀ x, (c0 x).defMem ≤ (c1 x).defMem)
  {expr: Expr .basic}
  {fv}
:
  Set.Subset
    (expr.intp .defLane b0 c0 fv)
    (expr.intp .defLane b1 c1 fv)
:=
  intp_mono_std
    (even := .some .defLane)
    (odd := .some .posLane)
    bLePos
    cLeDef
    (LaneEq.of_basic expr)
    ⟨rfl, Set3.Lane.noConfusion⟩

theorem Expr.intp_mono_std_posMem
  {b0 b1} (bLeDef: ∀ x, (b1 x).defMem ≤ (b0 x).defMem)
  {c0 c1} (cLePos: ∀ x, (c0 x).posMem ≤ (c1 x).posMem)
  {expr: Expr .basic}
  {fv}
:
  Set.Subset
    (expr.intp .posLane b0 c0 fv)
    (expr.intp .posLane b1 c1 fv)
:=
  intp_mono_std
    (even := .some .posLane)
    (odd := .some .defLane)
    bLeDef
    cLePos
    (LaneEq.of_basic expr)
    ⟨rfl, Set3.Lane.noConfusion⟩

theorem Expr.triIntp_mono_std
  {b0 b1} (bLe: b1 ≤ b0)
  {c0 c1} (cLe: c0 ≤ c1)
  {expr: Expr .basic}
  {fv}
:
  expr.triIntp b0 c0 fv ≤ expr.triIntp b1 c1 fv
:=
  {
    defLe :=
      intp_mono_std_defMem
        (fun x => (bLe x).posLe)
        (fun x => (cLe x).defLe)
    posLe :=
      intp_mono_std_posMem
        (fun x => (bLe x).defLe)
        (fun x => (cLe x).posLe)
  }

theorem DefList.intpDefs_mono_std
  {dl: DefList}
  {b0 b1} (bLe: b1 ≤ b0)
  {c0 c1} (cLe: c0 ≤ c1)
:
  dl.intpDefs b0 c0 ≤ dl.intpDefs b1 c1
:=
  fun _ => Expr.triIntp_mono_std bLe cLe


theorem Expr.triIntp_mono_apx
  {expr: Expr .basic}
  {b0 b1 c0 c1 fv}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  expr.triIntp b0 c0 fv ⊑ expr.triIntp b1 c1 fv
:=
  match expr with
  | .const _ x => {
      defLe _p pIn := (cLe x).defLe pIn
      posLe _p pIn := (cLe x).posLe pIn
    }
  | .var _ => ⟨fun _ => id, fun _ => id⟩
  | .null => ⟨fun _ => id, fun _ => id⟩
  | .prod _ _ =>
      let ihL := triIntp_mono_apx bLe cLe
      let ihR := triIntp_mono_apx bLe cLe
      {
        defLe := fun _p ⟨pL, pR, eq, pLIn, pRIn⟩ =>
          ⟨pL, pR, eq, ihL.defLe pLIn, ihR.defLe pRIn⟩
        posLe := fun _p ⟨pL, pR, eq, pLIn, pRIn⟩ =>
          ⟨pL, pR, eq, ihL.posLe pLIn, ihR.posLe pRIn⟩
      }
  | .ir _ _ =>
      let ihL := triIntp_mono_apx bLe cLe
      let ihR := triIntp_mono_apx bLe cLe
      {
        defLe := fun _p ⟨pLIn, pRIn⟩ =>
          ⟨ihL.defLe pLIn, ihR.defLe pRIn⟩
        posLe := fun _p ⟨pLIn, pRIn⟩ =>
          ⟨ihL.posLe pLIn, ihR.posLe pRIn⟩
      }
  | .full _ =>
      let ih := triIntp_mono_apx bLe cLe
      {
        defLe _p pIn pB := ih.defLe (pIn pB)
        posLe _p pIn pB := ih.posLe (pIn pB)
      }
  | .compl _ =>
      let ih := triIntp_mono_apx cLe bLe
      {
        defLe p pIn :=
          let tmp: (p: Pair) → _ → _ := ih.posLe
          not_imp_not.mpr (tmp p) pIn
        posLe p pIn :=
          let tmp: (p: Pair) → _ → _ := ih.defLe
          not_imp_not.mpr (tmp p) pIn
      }
  | .arbIr _ =>
      let ih _d := triIntp_mono_apx bLe cLe
      {
        defLe _p pIn pXPos1 := (ih pXPos1).defLe (pIn pXPos1)
        posLe _p pIn pXPos0 := (ih pXPos0).posLe (pIn pXPos0)
      }

theorem Expr.triIntp_mono_apx_defMem
  {expr: Expr .basic}
  {b0 b1} (bLe: b0 ⊑ b1)
  {c0 c1} (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
  {fv}
:
  Set.Subset
    (expr.triIntp b0 c0 fv).defMem
    (expr.triIntp b1 c1 fv).defMem
:=
  let c0LeSelf := (Valuation.ordApx Pair).le_refl c0
  let isMonoB := triIntp_mono_apx bLe c0LeSelf
  let isMonoC := intp_mono_std_defMem
    (fun _ => le_refl _)
    cLeDef
  isMonoB.defLe.trans isMonoC

theorem Expr.triIntp_mono_apx_posMem
  {expr: Expr .basic}
  {b0 b1} (bLe: b0 ⊑ b1)
  {c0 c1} (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
  {fv}
:
  Set.Subset
    (expr.triIntp b1 c1 fv).posMem
    (expr.triIntp b0 c0 fv).posMem
:=
  let c0LeSelf := (Valuation.ordApx Pair).le_refl c1
  let isMonoB := triIntp_mono_apx bLe c0LeSelf
  let isMonoC := intp_mono_std_posMem
    (fun _ => le_refl _)
    cLePos
  isMonoB.posLe.trans isMonoC

theorem DefList.intpDefs_mono_apx
  {dl: DefList}
  {b0 b1 c0 c1: Valuation Pair}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  dl.intpDefs b0 c0 ⊑ dl.intpDefs b1 c1
:=
  fun _ => Expr.triIntp_mono_apx bLe cLe


theorem Expr.triIntp_getLane_eq {b c fv lane}
  (expr: Expr .basic)
:
  (expr.triIntp b c fv).getLane lane = expr.intp lane b c fv
:=
  match lane with
  | .defLane => rfl
  | .posLane => rfl
