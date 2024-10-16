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

def Expr.interpretation.unEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (left rite: Expr sig)
:
  (interpretation salg b c (un left rite)).defMem
    =
  Union.union
    (interpretation salg b c left).defMem
    (interpretation salg b c rite).defMem
:=
  rfl

def Expr.interpretation.unEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (left rite: Expr sig)
:
  (interpretation salg b c (un left rite)).posMem
    =
  Union.union
    (interpretation salg b c left).posMem
    (interpretation salg b c rite).posMem
:=
  rfl

def Expr.interpretation.irEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (left rite: Expr sig)
:
  (interpretation salg b c (ir left rite)).defMem
    =
  Inter.inter
    (interpretation salg b c left).defMem
    (interpretation salg b c rite).defMem
:=
  rfl

def Expr.interpretation.irEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (left rite: Expr sig)
:
  (interpretation salg b c (ir left rite)).posMem
    =
  Inter.inter
    (interpretation salg b c left).posMem
    (interpretation salg b c rite).posMem
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

def Expr.interpretation.ifThenEqDef
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (cond expr: Expr sig)
:
  (interpretation salg b c (ifThen cond expr)).defMem
    =
  (fun d =>
    And
      (∃ dC, dC ∈ (interpretation salg b c cond).defMem)
      (d ∈ (interpretation salg b c expr).defMem))
:=
  rfl

def Expr.interpretation.ifThenEqPos
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (cond expr: Expr sig)
:
  (interpretation salg b c (ifThen cond expr)).posMem
    =
  (fun d =>
    And
      (∃ dC, dC ∈ (interpretation salg b c cond).posMem)
      (d ∈ (interpretation salg b c expr).posMem))
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
  
  (interpretation salg b c (Expr.Un x body)).defMem
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
  
  (interpretation salg b c (Expr.Un x body)).posMem
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
  
  (interpretation salg b c (Expr.Ir x body)).defMem
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
  
  (interpretation salg b c (Expr.Ir x body)).posMem
    =
  (fun d => ∀ dX, d ∈ (interpretationBody dX).posMem)
:=
  rfl


def Expr.interpretation.isMonotonic.defMem
  {salg: Salgebra sig}
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
    | Expr.un _ _ =>
      dIn.elim
        (fun inL =>
          Or.inl (isMonotonic.defMem cLeDef inL))
        (fun inR =>
          Or.inr (isMonotonic.defMem cLeDef inR))
    | Expr.ir _ _ =>
      And.intro
        (isMonotonic.defMem cLeDef dIn.left)
        (isMonotonic.defMem cLeDef dIn.right)
    | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
    | Expr.ifThen _ _ =>
      let ⟨dC, dCIn⟩ := dIn.left.unwrap
      And.intro
        ⟨dC, isMonotonic.defMem cLeDef dCIn⟩
        (isMonotonic.defMem cLeDef dIn.right)
    | Expr.Un x _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      let isDef :=
        isMonotonic.defMem (cLeDefUpdated x dX) dXIn
      ⟨dX, isDef⟩
    | Expr.Ir x _ =>
      fun dX =>
        isMonotonic.defMem (cLeDefUpdated x dX) (dIn dX)

def Expr.interpretation.isMonotonic.posMem
  {salg: Salgebra sig}
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
    | Expr.un _ _ =>
      dIn.elim
        (fun inL =>
          Or.inl (isMonotonic.posMem cLePos inL))
        (fun inR =>
          Or.inr (isMonotonic.posMem cLePos inR))
    | Expr.ir _ _ =>
      And.intro
        (isMonotonic.posMem cLePos dIn.left)
        (isMonotonic.posMem cLePos dIn.right)
    | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
    | Expr.ifThen _ _ =>
      let ⟨dC, dCIn⟩ := dIn.left.unwrap
      And.intro
        ⟨dC, isMonotonic.posMem cLePos dCIn⟩
        (isMonotonic.posMem cLePos dIn.right)
    | Expr.Un x _ =>
      let ⟨dX, dXIn⟩ := dIn.unwrap
      let isDef :=
        isMonotonic.posMem (cLePosUpdated x dX) dXIn
      ⟨dX, isDef⟩
    | Expr.Ir x _ =>
      fun dX =>
        isMonotonic.posMem (cLePosUpdated x dX) (dIn dX)

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
  | Expr.un left rite =>
      let ihL :=
        interpretation.isMonotonic.approximation salg left bLe cLe
      let ihR :=
        interpretation.isMonotonic.approximation salg rite bLe cLe
      
      Set3.LeApx.intro
        (fun _d dIn => dIn.elim
          (fun inL => Or.inl (ihL.defLe inL))
          (fun inR => Or.inr (ihR.defLe inR)))
        (fun _d dIn => dIn.elim
          (fun inL => Or.inl (ihL.posLe inL))
          (fun inR => Or.inr (ihR.posLe inR)))
  | Expr.ir left rite =>
      let ihL :=
        interpretation.isMonotonic.approximation salg left bLe cLe
      let ihR :=
        interpretation.isMonotonic.approximation salg rite bLe cLe
      
      Set3.LeApx.intro
        (fun _d dIn =>
          And.intro (ihL.defLe dIn.left) (ihR.defLe dIn.right))
        (fun _d dIn =>
          And.intro (ihL.posLe dIn.left) (ihR.posLe dIn.right))
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
  | Expr.ifThen cond expr => Set3.LeApx.intro
      (fun _d dIn =>
        let dC := dIn.left.unwrap
        
        let hC :=
          interpretation.isMonotonic.approximation salg cond bLe cLe
        let hE :=
          interpretation.isMonotonic.approximation salg expr bLe cLe
        
        And.intro
          ⟨dC, hC.defLe dC.property⟩
          (hE.defLe dIn.right))
      (fun _d dIn =>
        let dC := dIn.left.unwrap
        
        let hC :=
          interpretation.isMonotonic.approximation salg cond bLe cLe
        let hE :=
          interpretation.isMonotonic.approximation salg expr bLe cLe
        
        And.intro
          ⟨dC, hC.posLe dC.property⟩
          (hE.posLe dIn.right))
  | Expr.Un x body =>
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
  | Expr.Ir x body =>
      let ih d :=
        interpretation.isMonotonic.approximation salg body
          (Valuation.update.isMonotonic.approximation b0 b1 bLe x d)
          (Valuation.update.isMonotonic.approximation c0 c1 cLe x d)
      
      Set3.LeApx.intro
        (fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1))
        (fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0))


def Expr.interpretation.isMonotonic.apxDefMem
  (salg: Salgebra sig)
  (e: Expr sig)
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
