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


def Expr.interpretation.isMonotonic.standard
  (salg: Salgebra sig)
  (e: Expr sig)
  (b: Valuation salg.D)
  {c0 c1: Valuation salg.D}
  (cLe: c0 ≤ c1)
:
  interpretation salg b c0 e ≤ interpretation salg b c1 e
:=
  match e with
  | Expr.var a => Set3.LeStd.intro
      (fun _x xIn => (cLe a).defLe xIn)
      (fun _x xIn => (cLe a).posLe xIn)
  | Expr.op opr args => Set3.LeStd.intro
      (fun _x xIn =>
        let argC0 (i: sig.Params opr) :=
          (interpretation salg b c0 (args i)).defMem
        let argC1 (i: sig.Params opr) :=
          (interpretation salg b c1 (args i)).defMem
        let argMono (i: sig.Params opr): argC0 i ≤ argC1 i :=
          (interpretation.isMonotonic.standard salg (args i) b cLe).defLe
        let isMono3 := salg.isMonotonic opr argC0 argC1 argMono
        isMono3 xIn)
      (fun _x xIn =>
        let argC0 (i: sig.Params opr) :=
          (interpretation salg b c0 (args i)).posMem
        let argC1 (i: sig.Params opr) :=
          (interpretation salg b c1 (args i)).posMem
        let argMono (i: sig.Params opr): argC0 i ≤ argC1 i :=
          (interpretation.isMonotonic.standard salg (args i) b cLe).posLe
        let isMono3 := salg.isMonotonic opr argC0 argC1 argMono
        isMono3 xIn)
  -- "Right" is one letter too long.
  | Expr.un left rite => Set3.LeStd.intro
      (fun x xIn =>
        let left.I0 := (interpretation salg b c0 left).defMem
        let left.I1 := (interpretation salg b c1 left).defMem
        
        let rite.I0 := (interpretation salg b c0 rite).defMem
        let rite.I1 := (interpretation salg b c1 rite).defMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (interpretation.isMonotonic.standard salg left b cLe).defLe
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (interpretation.isMonotonic.standard salg rite b cLe).defLe
        
        if hLeft: x ∈ left.I0 then
          let xInLeft1: x ∈ left.I1 := left.isMono hLeft
          Or.inl xInLeft1
        else if hRite: x ∈ rite.I0 then
          let xInRite1: x ∈ rite.I1 := rite.isMono hRite
          Or.inr xInRite1
        else
          False.elim (xIn.elim (fun xInL => hLeft xInL) (fun xInR => hRite xInR)))
      
      (fun x xIn =>
        let left.I0 := (interpretation salg b c0 left).posMem
        let left.I1 := (interpretation salg b c1 left).posMem
        
        let rite.I0 := (interpretation salg b c0 rite).posMem
        let rite.I1 := (interpretation salg b c1 rite).posMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (interpretation.isMonotonic.standard salg left b cLe).posLe
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (interpretation.isMonotonic.standard salg rite b cLe).posLe
        
        if hLeft: x ∈ left.I0 then
          let xInLeft1: x ∈ left.I1 := left.isMono hLeft
          Or.inl xInLeft1
        else if hRite: x ∈ rite.I0 then
          let xInRite1: x ∈ rite.I1 := rite.isMono hRite
          Or.inr xInRite1
        else
          False.elim (xIn.elim (fun xInL => hLeft xInL) (fun xInR => hRite xInR)))
  | Expr.ir left rite => Set3.LeStd.intro
      (fun x xIn =>
        let left.I0 := (interpretation salg b c0 left).defMem
        let left.I1 := (interpretation salg b c1 left).defMem
        
        let rite.I0 := (interpretation salg b c0 rite).defMem
        let rite.I1 := (interpretation salg b c1 rite).defMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (interpretation.isMonotonic.standard salg left b cLe).defLe
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (interpretation.isMonotonic.standard salg rite b cLe).defLe
        
        if hLeft: x ∈ left.I0 then
          if hRite: x ∈ rite.I0 then
            let xInLeft1: x ∈ left.I1 := left.isMono hLeft
            let xInRite1: x ∈ rite.I1 := rite.isMono hRite
            And.intro xInLeft1 xInRite1
          else
            False.elim (hRite xIn.right)
        else
          False.elim (hLeft xIn.left))
      
      (fun x xIn =>
        let left.I0 := (interpretation salg b c0 left).posMem
        let left.I1 := (interpretation salg b c1 left).posMem
        
        let rite.I0 := (interpretation salg b c0 rite).posMem
        let rite.I1 := (interpretation salg b c1 rite).posMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (interpretation.isMonotonic.standard salg left b cLe).posLe
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (interpretation.isMonotonic.standard salg rite b cLe).posLe
        
        if hLeft: x ∈ left.I0 then
          if hRite: x ∈ rite.I0 then
            let xInLeft1: x ∈ left.I1 := left.isMono hLeft
            let xInRite1: x ∈ rite.I1 := rite.isMono hRite
            And.intro xInLeft1 xInRite1
          else
            False.elim (hRite xIn.right)
        else
          False.elim (hLeft xIn.left))
  | Expr.cpl _ => Set3.LeStd.intro (fun _ xIn => xIn) (fun _ xIn => xIn)
  | Expr.ifThen cond expr => Set3.LeStd.intro
      (fun _d dIn =>
        let dC := dIn.left.unwrap
        
        let hC := interpretation.isMonotonic.standard salg cond b cLe
        let hE := interpretation.isMonotonic.standard salg expr b cLe
        
        And.intro
          ⟨dC, hC.defLe dC.property⟩
          (hE.defLe dIn.right))
      (fun _d dIn =>
        let dC := dIn.left.unwrap
        
        let hC := interpretation.isMonotonic.standard salg cond b cLe
        let hE := interpretation.isMonotonic.standard salg expr b cLe
        
        And.intro
          ⟨dC, hC.posLe dC.property⟩
          (hE.posLe dIn.right))
  | Expr.Un x body => Set3.LeStd.intro
      (fun d dIn =>
        let dX := dIn.unwrap
        
        let bUpdated := b.update x dX.val
        let c0Updated := c0.update x dX.val
        let c1Updated := c1.update x dX.val
        
        let body.I0 := interpretation salg bUpdated c0Updated body
        let body.I1 := interpretation salg bUpdated c1Updated body
        
        let cUpdatedLe :=
          Valuation.update.isMonotonic.standard cLe x dX.val
        
        let bodyLe: body.I0 ≤ body.I1 := interpretation.isMonotonic.standard
          salg body bUpdated cUpdatedLe
        
        let dInBody0: d ∈ body.I0.defMem := dX.property
        let dInBody1: d ∈ body.I1.defMem := bodyLe.defLe dInBody0
        
        ⟨dX.val, dInBody1⟩)
      
      (fun d dIn =>
        let dX := dIn.unwrap
        
        let bUpdated := b.update x dX.val
        let c0Updated := c0.update x dX.val
        let c1Updated := c1.update x dX.val
        
        let body.I0 := interpretation salg bUpdated c0Updated body
        let body.I1 := interpretation salg bUpdated c1Updated body
        
        let cUpdatedLe :=
          Valuation.update.isMonotonic.standard cLe x dX.val
        
        let bodyLe: body.I0 ≤ body.I1 := interpretation.isMonotonic.standard
          salg body bUpdated cUpdatedLe
        
        let dInBody0: d ∈ body.I0.posMem := dX.property
        let dInBody1: d ∈ body.I1.posMem := bodyLe.posLe dInBody0
        
        ⟨dX.val, dInBody1⟩)
  | Expr.Ir x body => Set3.LeStd.intro
      (fun _d dIn xDDef =>
        let dInXD := dIn xDDef
        
        let bUpdated := b.update x xDDef
        let c0Updated := c0.update x xDDef
        let c1Updated := c1.update x xDDef
        
        let body.I0 := interpretation salg bUpdated c0Updated body
        let body.I1 := interpretation salg bUpdated c1Updated body
        
        let cUpdatedLe :=
          Valuation.update.isMonotonic.standard cLe x xDDef
        
        let bodyLe: body.I0 ≤ body.I1 :=
          interpretation.isMonotonic.standard salg body bUpdated cUpdatedLe
        
        bodyLe.defLe dInXD)
      
      (fun _d dIn xDDef =>
        let dInXD := dIn xDDef
        
        let bUpdated := b.update x xDDef
        let c0Updated := c0.update x xDDef
        let c1Updated := c1.update x xDDef
        
        let body.I0 := interpretation salg bUpdated c0Updated body
        let body.I1 := interpretation salg bUpdated c1Updated body
        
        let cUpdatedLe :=
          Valuation.update.isMonotonic.standard cLe x xDDef
        
        let bodyLe: body.I0 ≤ body.I1 :=
          interpretation.isMonotonic.standard salg body bUpdated cUpdatedLe
        
        bodyLe.posLe dInXD)

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


def Expr.interpretation.contextHasDefMemPreservesDefMem
  {salg: Salgebra sig}
  {b c0 c1: Valuation salg.D}
  (cLeDef: (x: Nat) → (c0 x).defMem ⊆ (c1 x).defMem)
  {expr: Expr sig}
  {d: salg.D}
  (dIn: (expr.interpretation salg b c0).defMem d)
:
  (expr.interpretation salg b c1).defMem d
:=
  let cLeDefUpdated x dX :=
    Valuation.update.isMonotonic.standard.defMem cLeDef x dX
  match expr with
  | Expr.var x => cLeDef x dIn
  | Expr.op opr args =>
    let defMem param :=
      ((args param).interpretation salg b c0).defMem
    
    let defMemFloor param :=
      ((args param).interpretation salg b c1).defMem
    
    let isLe _ _ dIn := contextHasDefMemPreservesDefMem cLeDef dIn
    
    salg.isMonotonic opr defMem defMemFloor isLe dIn
  | Expr.un _ _ =>
    dIn.elim
      (fun inL =>
        Or.inl (contextHasDefMemPreservesDefMem cLeDef inL))
      (fun inR =>
        Or.inr (contextHasDefMemPreservesDefMem cLeDef inR))
  | Expr.ir _ _ =>
    And.intro
      (contextHasDefMemPreservesDefMem cLeDef dIn.left)
      (contextHasDefMemPreservesDefMem cLeDef dIn.right)
  | Expr.cpl _ => dIn -- Note: cpl is not affected by context.
  | Expr.ifThen _ _ =>
    let ⟨dC, dCIn⟩ := dIn.left.unwrap
    And.intro
      ⟨dC, contextHasDefMemPreservesDefMem cLeDef dCIn⟩
      (contextHasDefMemPreservesDefMem cLeDef dIn.right)
  | Expr.Un x _ =>
    let ⟨dX, dXIn⟩ := dIn.unwrap
    let isDef :=
      contextHasDefMemPreservesDefMem (cLeDefUpdated x dX) dXIn
    ⟨dX, isDef⟩
  | Expr.Ir x _ =>
    fun dX =>
      contextHasDefMemPreservesDefMem (cLeDefUpdated x dX) (dIn dX)