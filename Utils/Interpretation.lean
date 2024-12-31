/-
  Contains utility definitions and about the interpretation
  of expressions.
-/

import WFC.Ch3_Interpretation

def Expr.interpretation.opEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (opr: sig.Op)
  (args: sig.Params opr → Expr sig)
:
  (interpretation salg b c (op opr args)).defMem
    =
  salg.I opr (fun arg => (interpretation salg b c (args arg)).defMem)
:=
  rfl

def Expr.interpretation.opEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (opr: sig.Op)
  (args: sig.Params opr → Expr sig)
:
  (interpretation salg b c (op opr args)).posMem
    =
  salg.I opr (fun arg => (interpretation salg b c (args arg)).posMem)
:=
  rfl

def Expr.interpretation.cplEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (expr: Expr sig)
:
  (interpretation salg b c (cpl expr)).defMem
    =
  (interpretation salg b b expr).posMemᶜ
:=
  rfl

def Expr.interpretation.cplEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (expr: Expr sig)
:
  (interpretation salg b c (cpl expr)).posMem
    =
  (interpretation salg b b expr).defMemᶜ
:=
  rfl

def Expr.interpretation.arbUnEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (x: Nat)
  (body: Expr sig)
:
  let interpretationBody dX :=
    interpretation salg (b.update x dX) (c.update x dX) body
  
  (interpretation salg b c (arbUn x body)).defMem
    =
  (fun d => ∃ dX, d ∈ (interpretationBody dX).defMem)
:=
  rfl

def Expr.interpretation.arbUnEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (x: Nat)
  (body: Expr sig)
:
  let interpretationBody dX :=
    interpretation salg (b.update x dX) (c.update x dX) body
  
  (interpretation salg b c (arbUn x body)).posMem
    =
  (fun d => ∃ dX, d ∈ (interpretationBody dX).posMem)
:=
  rfl

def Expr.interpretation.arbIrEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (x: Nat)
  (body: Expr sig)
:
  let interpretationBody dX :=
    interpretation salg (b.update x dX) (c.update x dX) body
  
  (interpretation salg b c (arbIr x body)).defMem
    =
  (fun d => ∀ dX, d ∈ (interpretationBody dX).defMem)
:=
  rfl

def Expr.interpretation.arbIrEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (x: Nat)
  (body: Expr sig)
:
  let interpretationBody dX :=
    interpretation salg (b.update x dX) (c.update x dX) body
  
  (interpretation salg b c (arbIr x body)).posMem
    =
  (fun d => ∀ dX, d ∈ (interpretationBody dX).posMem)
:=
  rfl


def Expr.interpretation.isMonotonic.defMem
  {b c0 c1: Valuation salg.D}
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
  {expr: Expr sig}
:
  (expr.interpretation salg b c0).defMem
    ⊆
  (expr.interpretation salg b c1).defMem
:=
  fun _ dIn =>
    let cLeDefUpdated x dX :=
      Valuation.update.isMonotonic.standard.defMem cLeDef x dX
    match expr with
    | Expr.var x => cLeDef x dIn
    | Expr.op opr args =>
      let defMem param :=
        ((args param).interpretation salg b c0).defMem
      
      let defMemFloor param :=
        ((args param).interpretation salg b c1).defMem
      
      let isLe _ := isMonotonic.defMem cLeDef
      
      salg.isMonotonic opr defMem defMemFloor isLe dIn
    | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
    | Expr.arbUn x _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      let isDef :=
        isMonotonic.defMem (cLeDefUpdated x dX) dXIn
      ⟨dX, isDef⟩
    | Expr.arbIr x _ =>
      fun dX =>
        isMonotonic.defMem (cLeDefUpdated x dX) (dIn dX)

def Expr.interpretation.isMonotonic.posMem
  {b c0 c1: Valuation salg.D}
  (cLePos: (x: Nat) → (c0 x).posMem ⊆ (c1 x).posMem)
  {expr: Expr sig}
:
  (expr.interpretation salg b c0).posMem
    ⊆
  (expr.interpretation salg b c1).posMem
:=
  fun _ dIn =>
    let cLePosUpdated x dX :=
      Valuation.update.isMonotonic.standard.posMem cLePos x dX
    match expr with
    | Expr.var x => cLePos x dIn
    | Expr.op opr args =>
      let posMem param :=
        ((args param).interpretation salg b c0).posMem
      
      let posMemFloor param :=
        ((args param).interpretation salg b c1).posMem
      
      let isLe _ := isMonotonic.posMem cLePos
      
      salg.isMonotonic opr posMem posMemFloor isLe dIn
    | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
    | Expr.arbUn x _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      let isDef :=
        isMonotonic.posMem (cLePosUpdated x dX) dXIn
      ⟨dX, isDef⟩
    | Expr.arbIr x _ =>
      fun dX =>
        isMonotonic.posMem (cLePosUpdated x dX) (dIn dX)

def Expr.interpretation.isMonotonic.notPosMem
  {b c0 c1: Valuation salg.D}
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
  {expr: Expr sig}
:
  ¬ (expr.interpretation salg b c0).posMem d
    →
  ¬ (expr.interpretation salg b c1).posMem d
:=
  let le := Expr.interpretation.isMonotonic.posMem cLePos
  Function.contra (@le d)

def Expr.interpretation.isMonotonic.standard
  (salg: Salgebra sig)
  (e: Expr sig)
  (b: Valuation salg.D)
  {c0 c1: Valuation salg.D}
  (cLe: c0 ≤ c1)
:
  interpretation salg b c0 e ≤ interpretation salg b c1 e
:= {
  defLe := defMem fun x => (cLe x).defLe
  posLe := posMem fun x => (cLe x).posLe
}

def Expr.interpretation.isMonotonic.approximation
  (salg: Salgebra sig)
  (e: Expr sig)
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  interpretation salg b0 c0 e ⊑ interpretation salg b1 c1 e
:=
  match e with
  | Expr.var x => Set3.LeApx.intro
      (fun _d dIn => (cLe x).defLe dIn)
      (fun _d dIn => (cLe x).posLe dIn)
  | Expr.op opr args =>
      let ih (arg: sig.Params opr) :=
        interpretation.isMonotonic.approximation salg (args arg) bLe cLe
      
      Set3.LeApx.intro
        (fun _d dIn =>
          let defArgs0 arg :=
            (interpretation salg b0 c0 (args arg)).defMem
          let defArgs1 arg :=
            (interpretation salg b1 c1 (args arg)).defMem
          
          let defArgsLe := salg.isMonotonic
            opr defArgs0 defArgs1 (fun a => (ih a).defLe)
          
          defArgsLe dIn)
        (fun _d dIn =>
          let posArgs0 arg :=
            (interpretation salg b0 c0 (args arg)).posMem
          let posArgs1 arg :=
            (interpretation salg b1 c1 (args arg)).posMem
          
          let posArgsLe := salg.isMonotonic
            opr posArgs1 posArgs0 (fun a => (ih a).posLe)
          
          posArgsLe dIn)
  | Expr.cpl expr =>
      let ih :=
        interpretation.isMonotonic.approximation salg expr bLe bLe
      Set3.LeApx.intro
        (fun d dIn =>
          let tmp: (d: salg.D) → _ → _ := ih.posLe
          Function.contra (tmp d) dIn)
        (fun d dIn =>
          let tmp: (d: salg.D) → _ → _ := ih.defLe
          Function.contra (tmp d) dIn)
  | Expr.arbUn x body =>
      let ihBody d :=
        interpretation.isMonotonic.approximation salg body
          (Valuation.update.isMonotonic.approximation b0 b1 bLe x d)
          (Valuation.update.isMonotonic.approximation c0 c1 cLe x d)
      
      Set3.LeApx.intro
        (fun _d dIn =>
          let dX := dIn.unwrap
          ⟨
            dX.val,
            (ihBody dX.val).defLe dX.property⟩
          )
        (fun _d dIn =>
          let dX := dIn.unwrap
          ⟨
            dX.val,
            (ihBody dX.val).posLe dX.property⟩
          )
  | Expr.arbIr x body =>
      let ih d :=
        interpretation.isMonotonic.approximation salg body
          (Valuation.update.isMonotonic.approximation b0 b1 bLe x d)
          (Valuation.update.isMonotonic.approximation c0 c1 cLe x d)
      
      Set3.LeApx.intro
        (fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1))
        (fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0))


def Expr.interpretation.isMonotonic.apxDefMem
  {salg: Salgebra sig}
  {e: Expr sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
:
  (interpretation salg b0 c0 e).defMem
    ⊆
  (interpretation salg b1 c1 e).defMem
:=
  let c0LeSelf := (Valuation.ord.approximation salg.D).le_refl c0
  let isMonoB := isMonotonic.approximation salg e bLe c0LeSelf
  let isMonoC := isMonotonic.defMem cLeDef
  isMonoB.defLe.trans isMonoC

def Expr.interpretation.isMonotonic.apxPosMem
  {e: Expr sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
:
  (interpretation salg b1 c1 e).posMem
    ⊆
  (interpretation salg b0 c0 e).posMem
:=
  let c0LeSelf := (Valuation.ord.approximation salg.D).le_refl c1
  let isMonoB := isMonotonic.approximation salg e bLe c0LeSelf
  let isMonoC := isMonotonic.posMem cLePos
  isMonoB.posLe.trans isMonoC

def Expr.interpretation.isMonotonic.apxNotPosMem
  {e: Expr sig}
  {b0 b1 c0 c1: Valuation salg.D}
  (bLe: b0 ⊑ b1)
  (cLePos: (x: Nat) → (c1 x).posMem ⊆ (c0 x).posMem)
:
  ¬ (interpretation salg b0 c0 e).posMem d
    →
  ¬ (interpretation salg b1 c1 e).posMem d
:=
  let le := Expr.interpretation.isMonotonic.apxPosMem bLe cLePos
  Function.contra (@le d)
