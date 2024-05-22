import Valuation
import ExprIsFreeVar

open Classical


def Args
  (s: Signature)
  (op: s.Op)
  (D: Type u)
:=
  s.Params op → Set D

/-
  Salgebras act not on elements themselves (like algebras
  do), but on sets of elements, monotonically.
  
  (Equivalently, a salgebra on T is an algebra on sets
  of T whose operations are monotonic.)
-/
structure Salgebra (s: Signature) where
  D: Type u
  I: (op: s.Op) → Args s op D → Set D
  isMonotonic
    (op: s.Op)
    (args0 args1: Args s op D)
    (le: ∀ arg: s.Params op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1


def Expr.interpretation
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
:
  (Expr sig) → Set3 salg.D

| Expr.var a => c a
| Expr.op opr exprs =>
    let defArgs := fun arg =>
      (interpretation salg b c (exprs arg)).defMem
    let posArgs := fun arg =>
      (interpretation salg b c (exprs arg)).posMem
    ⟨
      salg.I opr defArgs,
      salg.I opr posArgs,
      
      salg.isMonotonic
        opr
        defArgs
        posArgs
        fun arg => (interpretation salg b c (exprs arg)).defLePos
    ⟩
| Expr.un e0 e1 =>
    let iE0 := interpretation salg b c e0
    let iE1 := interpretation salg b c e1
    ⟨
      iE0.defMem ∪ iE1.defMem,
      iE0.posMem ∪ iE1.posMem,
      
      fun d dDef =>
        Or.elim (dDef: d ∈ iE0.defMem ∨ d ∈ iE1.defMem)
          (fun dIE0 => Or.inl (iE0.defLePos dIE0))
          (fun dIE1 => Or.inr (iE1.defLePos dIE1))
    ⟩
| Expr.ir e0 e1 =>
    let iE0 := interpretation salg b c e0
    let iE1 := interpretation salg b c e1
    ⟨
      iE0.defMem ∩ iE1.defMem,
      iE0.posMem ∩ iE1.posMem,
      
      fun _d dDef =>
        And.intro (iE0.defLePos dDef.left) (iE1.defLePos dDef.right)
    ⟩
| Expr.cpl e =>
    let ie := (interpretation salg b b e)
    ⟨
      ie.posMemᶜ,
      ie.defMemᶜ,
      
      fun d dInNPos =>
        show d ∉ ie.defMem from fun dInDef => dInNPos (ie.defLePos dInDef)
    ⟩
| Expr.ifThen cond expr =>
    let cond.I: Set3 salg.D := interpretation salg b c cond
    let expr.I: Set3 salg.D := interpretation salg b c expr
    
    ⟨
      fun d => (∃ dC, dC ∈ cond.I.defMem) ∧ d ∈ expr.I.defMem,
      fun d => (∃ dC, dC ∈ cond.I.posMem) ∧ d ∈ expr.I.posMem,
      
      fun _d dIn =>
        let dC := dIn.left.unwrap
        And.intro
          ⟨dC, cond.I.defLePos dC.property⟩
          (expr.I.defLePos dIn.right)
    ⟩
| Expr.Un x body =>
    let body.I (dX: salg.D): Set3 salg.D :=
      interpretation salg (b.update x dX) (c.update x dX) body
    
    ⟨
      fun d => ∃ dX, d ∈ (body.I dX).defMem,
      fun d => ∃ dX, d ∈ (body.I dX).posMem,
      
      fun _d dDef => dDef.elim fun dX iXDef =>
        ⟨dX, (body.I dX).defLePos iXDef⟩
    ⟩
| Expr.Ir x body =>
    let body.I (dX: salg.D): Set3 salg.D :=
      (interpretation salg (b.update x dX) (c.update x dX) body)
    
    ⟨
      fun d => ∀ dX, d ∈ (body.I dX).defMem,
      fun d => ∀ dX, d ∈ (body.I dX).posMem,
      
      fun _d dDefBody xDDef =>
        (body.I xDDef).defLePos (dDefBody xDDef)
    ⟩


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
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
           c0 c1 cLe x dX.val
        
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
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
          c0 c1 cLe x dX.val
        
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
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
          c0 c1 cLe x xDDef
        
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
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
          c0 c1 cLe x xDDef
        
        let bodyLe: body.I0 ≤ body.I1 :=
          interpretation.isMonotonic.standard salg body bUpdated cUpdatedLe
        
        bodyLe.posLe dInXD)

def Expr.interpretation.isMonotonic.approximation
  (salg: Salgebra sig)
  (e: Expr sig)
  (b0 b1 c0 c1: Valuation salg.D)
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
        interpretation.isMonotonic.approximation
          salg (args arg) b0 b1 c0 c1 bLe cLe
      
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
      let ihL := interpretation.isMonotonic.approximation
        salg left b0 b1 c0 c1 bLe cLe
      let ihR := interpretation.isMonotonic.approximation
        salg rite b0 b1 c0 c1 bLe cLe
      
      Set3.LeApx.intro
        (fun _d dIn => dIn.elim
          (fun inL => Or.inl (ihL.defLe inL))
          (fun inR => Or.inr (ihR.defLe inR)))
        (fun _d dIn => dIn.elim
          (fun inL => Or.inl (ihL.posLe inL))
          (fun inR => Or.inr (ihR.posLe inR)))
  | Expr.ir left rite =>
      let ihL := interpretation.isMonotonic.approximation
        salg left b0 b1 c0 c1 bLe cLe
      let ihR := interpretation.isMonotonic.approximation
        salg rite b0 b1 c0 c1 bLe cLe
      
      Set3.LeApx.intro
        (fun _d dIn =>
          And.intro (ihL.defLe dIn.left) (ihR.defLe dIn.right))
        (fun _d dIn =>
          And.intro (ihL.posLe dIn.left) (ihR.posLe dIn.right))
  | Expr.cpl expr =>
      let ih := interpretation.isMonotonic.approximation
        salg expr b0 b1 b0 b1 bLe bLe
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
        
        let hC := interpretation.isMonotonic.approximation
          salg cond b0 b1 c0 c1 bLe cLe
        let hE := interpretation.isMonotonic.approximation
          salg expr b0 b1 c0 c1 bLe cLe
        
        And.intro
          ⟨dC, hC.defLe dC.property⟩
          (hE.defLe dIn.right))
      (fun _d dIn =>
        let dC := dIn.left.unwrap
        
        let hC := interpretation.isMonotonic.approximation
          salg cond b0 b1 c0 c1 bLe cLe
        let hE := interpretation.isMonotonic.approximation
          salg expr b0 b1 c0 c1 bLe cLe
        
        And.intro
          ⟨dC, hC.posLe dC.property⟩
          (hE.posLe dIn.right))
  | Expr.Un x body =>
      let ihBody d :=
        interpretation.isMonotonic.approximation salg body
          (b0.update x d)
          (b1.update x d)
          (c0.update x d)
          (c1.update x d)
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
          (b0.update x d)
          (b1.update x d)
          (c0.update x d)
          (c1.update x d)
          (Valuation.update.isMonotonic.approximation b0 b1 bLe x d)
          (Valuation.update.isMonotonic.approximation c0 c1 cLe x d)
      
      Set3.LeApx.intro
        (fun _d dIn dXPos1 => (ih dXPos1).defLe (dIn dXPos1))
        (fun _d dIn dXPos0 => (ih dXPos0).posLe (dIn dXPos0))


def DefList.GetDef (sig: Signature) := Nat → Expr sig

/-
  The definition x depends on y if x = y or x contains
  y, possibly transitively.
-/
inductive DefList.DependsOn
  (getDef: GetDef sig): Nat → Nat → Prop
where
| Refl x: DependsOn getDef x x
| Uses
  (aUsesB: (getDef a).IsFreeVar Set.empty b)
  (bUsesC: DependsOn getDef b c)
  :
    DependsOn getDef a c

def DefList.DependsOn.push
  (dependsOn: DependsOn getDef a b)
  (isFree: (getDef b).IsFreeVar Set.empty c)
:
  DependsOn getDef a c
:=
  -- match dependsOn with
  -- | Refl _ => Uses isFree (Refl c)
  -- | Uses head tail =>
  --   let ih := push tail isFree
  --   ...
  let thePrincipleTM:
    (getDef b).IsFreeVar Set.empty c → DependsOn getDef a c
  :=
    dependsOn.rec
      (fun _ isFree => Uses isFree (Refl c))
      (fun isFree _ ih ihh =>
        Uses isFree (ih ihh))
  
  thePrincipleTM isFree

/-
  A definition list is finitely bounded iff every
  definition only depends on finitely many other
  definitions (transitively). This is to disallow
  definition lists like
  
  ```
    let def0 := def1
    let def1 := def3
    let def3 := def4
    ...
  ```
-/
def DefList.IsFinBounded (getDef: Nat → Expr sig): Prop :=
  ∀ name,
  ∃ upperBound,
  ∀ {dep}
    (_: DependsOn getDef name dep)
  ,
    dep < upperBound

structure DefList (sig: Signature) where
  getDef: DefList.GetDef sig

structure FinBoundedDL (sig: Signature) extends DefList sig where
  isFinBounded: DefList.IsFinBounded getDef

-- Interpretation on definition lists is defined pointwise.
def DefList.interpretation
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (dl: DefList sig)
:
  Valuation salg.D
:=
  fun x => Expr.interpretation salg b c (dl.getDef x)
