import Etst.WFC.Utils.Valuation

namespace Etst


def Expr.interpretation_mono_std_defMem
  {bv: List salg.D}
  {b c0 c1: Valuation salg.D}
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
  {expr: Expr sig}
:
  (expr.interpretation salg bv b c0).defMem
    ⊆
  (expr.interpretation salg bv b c1).defMem
:=
  fun _ dIn =>
    match expr with
    | Expr.var x => cLeDef x dIn
    | Expr.bvar _ => dIn
    | Expr.op opr args =>
      let defMem0 param :=
        ((args param).interpretation salg bv b c0).defMem
      
      let defMem1 param :=
        ((args param).interpretation salg bv b c1).defMem
      
      let isLe _ := interpretation_mono_std_defMem cLeDef

      salg.isMonotonic opr defMem0 defMem1 isLe dIn
    | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
    | Expr.arbUn _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      ⟨dX, interpretation_mono_std_defMem cLeDef dXIn⟩
    | Expr.arbIr _ =>
      fun dX =>
        interpretation_mono_std_defMem cLeDef (dIn dX)

def Expr.interpretation_mono_std_posMem
  {bv: List salg.D}
  {b c0 c1: Valuation salg.D}
  (cLePos: (x: Nat) → (c0 x).posMem ⊆ (c1 x).posMem)
  {expr: Expr sig}
:
  (expr.interpretation salg bv b c0).posMem
    ⊆
  (expr.interpretation salg bv b c1).posMem
:=
  fun _ dIn =>
    match expr with
    | Expr.var x => cLePos x dIn
    | Expr.bvar _ => dIn
    | Expr.op opr args =>
      let posMem0 param :=
        ((args param).interpretation salg bv b c0).posMem

      let posMem1 param :=
        ((args param).interpretation salg bv b c1).posMem

      let isLe _ := interpretation_mono_std_posMem cLePos

      salg.isMonotonic opr posMem0 posMem1 isLe dIn
    | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
    | Expr.arbUn _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      ⟨dX, interpretation_mono_std_posMem cLePos dXIn⟩
    | Expr.arbIr _ =>
      fun dX =>
        interpretation_mono_std_posMem cLePos (dIn dX)

def Expr.interpretation_mono_std
  {bv: List salg.D}
  {b: Valuation salg.D}
  {c0 c1: Valuation salg.D}
  (cLe: c0 ≤ c1)
:
  interpretation salg bv b c0 e ≤ interpretation salg bv b c1 e
:= {
  defLe := interpretation_mono_std_defMem fun x => (cLe x).defLe
  posLe := interpretation_mono_std_posMem fun x => (cLe x).posLe
}

def Expr.interpretation.isMonotonic.notPosMem
  {b c0 c1: Valuation salg.D}
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
  {expr: Expr sig}
:
  ¬ (expr.interpretation salg bv b c0).posMem d
    →
  ¬ (expr.interpretation salg bv b c1).posMem d
:=
  let le := Expr.interpretation_mono_std_posMem cLePos
  not_imp_not.mpr (@le d)


def DefList.interpretation_mono_std
  {salg: Salgebra sig}
  {dl: DefList sig}
  {b: Valuation salg.D}
  {c0 c1: Valuation salg.D}
  (cLe: c0 ≤ c1)
:
  dl.interpretation salg b c0 ≤ dl.interpretation salg b c1
:=
  fun _ => Expr.interpretation_mono_std cLe


def Expr.interpretation_mono_apx
  {salg: Salgebra sig}
  {e: Expr sig}
  {bv: List salg.D}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  interpretation salg bv b0 c0 e ⊑ interpretation salg bv b1 c1 e
:=
  match e with
  | Expr.var x => {
      defLe := fun _d dIn => (cLe x).defLe dIn
      posLe := fun _d dIn => (cLe x).posLe dIn
    }
  | Expr.bvar _ => ⟨fun _ => id, fun _ => id⟩
  | Expr.op opr args =>
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
  | Expr.cpl _ =>
      let ih := interpretation_mono_apx bLe bLe
      {
        defLe := fun d dIn =>
          let tmp: (d: salg.D) → _ → _ := ih.posLe
          not_imp_not.mpr (tmp d) dIn
        posLe := fun d dIn =>
          let tmp: (d: salg.D) → _ → _ := ih.defLe
          not_imp_not.mpr (tmp d) dIn
      }
  | Expr.arbUn _ =>
      let ih _d := interpretation_mono_apx bLe cLe
      {
        defLe := fun _d ⟨dX, dXIn⟩ => ⟨dX, (ih dX).defLe dXIn⟩
        posLe := fun _d ⟨dX, dXIn⟩ => ⟨dX, (ih dX).posLe dXIn⟩
      }
  | Expr.arbIr _ =>
      let ih _d := interpretation_mono_apx bLe cLe
      {
        defLe := fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1)
        posLe := fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0)
      }

def Expr.interpretation_mono_apx_defMem
  {e: Expr sig}
  {bv: List salg.D}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
:
  (interpretation salg bv b0 c0 e).defMem
    ⊆
  (interpretation salg bv b1 c1 e).defMem
:=
  let c0LeSelf := (Valuation.ordApx salg.D).le_refl c0
  let isMonoB := interpretation_mono_apx bLe c0LeSelf
  let isMonoC := interpretation_mono_std_defMem cLeDef
  isMonoB.defLe.trans isMonoC

def Expr.interpretation_mono_apx_posMem
  {e: Expr sig}
  {bv: List salg.D}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
:
  (interpretation salg bv b1 c1 e).posMem
    ⊆
  (interpretation salg bv b0 c0 e).posMem
:=
  let c0LeSelf := (Valuation.ordApx salg.D).le_refl c1
  let isMonoB := interpretation_mono_apx bLe c0LeSelf
  let isMonoC := interpretation_mono_std_posMem cLePos
  isMonoB.posLe.trans isMonoC

def Expr.interpretation_mono_apx_posMem_not
  {e: Expr sig}
  {bv: List salg.D}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
:
  ¬ (interpretation salg bv b0 c0 e).posMem d
    →
  ¬ (interpretation salg bv b1 c1 e).posMem d
:=
  let le := Expr.interpretation_mono_apx_posMem bLe cLePos
  not_imp_not.mpr (@le d)

def DefList.interpretation_mono_apx
  {salg: Salgebra sig}
  {dl: DefList sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  dl.interpretation salg b0 c0 ⊑ dl.interpretation salg b1 c1
:=
  fun _ => Expr.interpretation_mono_apx bLe cLe
