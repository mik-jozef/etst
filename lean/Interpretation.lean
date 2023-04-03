import Valuation

open Classical


-- Thanks to answerers of https://proofassistants.stackexchange.com/q/1740
structure Signature where
  Op: Type
  arity: Op → Type


inductive Expr (s: Signature) (Var: Type) where
  | var (v: Var)
  | varBound (v: Nat)
  | opApp (op: s.Op) (args: s.arity op → Expr s Var)
  | un (left rite: Expr s Var)
  | ir (left rite: Expr s Var)
  | cpl (expr: Expr s Var)
  | Un (x: Var) (domain body: Expr s Var)
  | Ir (x: Var) (domain body: Expr s Var)

namespace Expr
  instance: Coe Nat (Expr s Var) where
    coe := fun n => Expr.varBound n
  
  instance (n: Nat): OfNat (Expr s Var) n where
    ofNat := Expr.varBound n
  
  def any: Expr s Var := Expr.un 0 (Expr.cpl 0)
  
  def isPos: Expr s Var → Prop
    | var _ => True
    | varBound _ => True
    | opApp op args => ∀ arg: s.arity op, (args arg).isPos
    | un left rite => left.isPos ∧ rite.isPos
    | ir left rite => left.isPos ∧ rite.isPos
    | cpl expr => (∃ x, expr = Expr.var x) ∨ (∃ x, expr = Expr.varBound x)
    | Un _ domain body => domain.isPos ∧ body.isPos
    | Ir _ domain body => domain = any ∧ body.isPos
end Expr

/- TODO delete?
inductive PosExpr (s: Signature) (Var: Type) where
  | var (v: Var)
  | varBound (v: Nat)
  | opApp (op: s.Op) (args: s.arity op → PosExpr s Var)
  | un (left: PosExpr s Var) (rite: PosExpr s Var)
  | ir (left: PosExpr s Var) (rite: PosExpr s Var)
  | ifThen (cond ifYes: PosExpr s Var)
  | Un (x xc: Var) (body: PosExpr s Var)
  | Ir (x xc: Var) (body: PosExpr s Var)

namespace PosExpr
  def ComplementsMap := Nat → Option Nat
  
  def replace (cm: ComplementsMap) (x xc: Nat): ComplementsMap :=
    fun xx => if xx = x then none else if xx = xc then x
  
  def toExpr (cm: ComplementsMap): PosExpr s Var → Expr s Var
  | PosExpr.var x => Expr.var x
  | PosExpr.varBound x => Expr.varBound x
  | PosExpr.opApp op args => Expr.opApp op (fun arg => (args arg).toExpr cm)
  | PosExpr.un a b => Expr.un (a.toExpr cm) (b.toExpr cm)
  | PosExpr.ir a b => Expr.un (a.toExpr cm) (b.toExpr cm)
  | PosExpr.ifThen a b => Expr.un (a.toExpr cm) (b.toExpr cm)
  | PosExpr.Un x xc body => Expr.Un x (body.toExpr (cm.replace xc x))
  | PosExpr.Ir x xc body => sorry

end PosExpr-/


structure DefList (s: Signature) (Var: Type) where
  isFinite: Type.isFinite Var
  getDef: Var → Expr s Var

/- TODO delete?
structure PosDefList (s: Signature) (Var: Type) where
  isFinite: Type.isFinite Var
  getDef: Var → PosExpr s Var-/


/-
  For our purposes, algebras act on sets of elements,
  monotonically.
  
  The other document refers to algebras as 'structures'
  because of these differences. I've not yet decided
  which name I want to keep.
-/
structure Algebra (s: Signature) where
  D: Type
  I: (op: s.Op) → (s.arity op → Set D) → Set D
  isMonotonic
    (op: s.Op)
    (args0 args1: s.arity op → Set D)
    (le: ∀ arg: s.arity op, args0 arg ≤ args1 arg)
  :
    I op args0 ≤ I op args1


def I (alg: Algebra s) (b c: Valuation Var alg.D): (Expr s Var) → Set3 alg.D
| Expr.var a => c (Sum.inl a)
| Expr.varBound a => c (Sum.inr a)
| Expr.opApp op exprs =>
    let defArgs := fun arg => (I alg b c (exprs arg)).defMem
    let posArgs := fun arg => (I alg b c (exprs arg)).posMem
    ⟨
      alg.I op defArgs,
      alg.I op posArgs,
      
      alg.isMonotonic
        op
        defArgs
        posArgs
        fun arg => (I alg b c (exprs arg)).defLePos
    ⟩
| Expr.un e0 e1 =>
    let iE0 := I alg b c e0
    let iE1 := I alg b c e1
    ⟨
      iE0.defMem ∪ iE1.defMem,
      iE0.posMem ∪ iE1.posMem,
      
      fun d dDef =>
        Or.elim (dDef: d ∈ iE0.defMem ∨ d ∈ iE1.defMem)
          (fun dIE0 => Or.inl (iE0.defLePos d dIE0))
          (fun dIE1 => Or.inr (iE1.defLePos d dIE1))
    ⟩
| Expr.ir e0 e1 =>
    let iE0 := I alg b c e0
    let iE1 := I alg b c e1
    ⟨
      iE0.defMem ∩ iE1.defMem,
      iE0.posMem ∩ iE1.posMem,
      
      fun d dDef =>
        And.intro (iE0.defLePos d dDef.left) (iE1.defLePos d dDef.right)
    ⟩
| Expr.cpl e =>
    let ie := (I alg b b e)
    ⟨
      ~ ie.posMem,
      ~ ie.defMem,
      
      fun d dInNPos =>
        show d ∉ ie.defMem from fun dInDef => dInNPos (ie.defLePos d dInDef)
    ⟩
| Expr.Un x xDom body =>
    let xDom.I: Set3 alg.D := I alg b c xDom
    
    let body.I (iX: alg.D): Set3 alg.D :=
      I alg (b.update (Sum.inl x) iX) (c.update (Sum.inl x) iX) body
    
    ⟨
      fun d => ∃ iX: ↑xDom.I.defMem, d ∈ (body.I iX).defMem,
      fun d => ∃ iX: ↑xDom.I.posMem, d ∈ (body.I iX).posMem,
      
      fun d dDef => dDef.elim fun iX iXDef => ⟨
        ⟨iX, xDom.I.defLePos iX iX.property⟩,
        (body.I iX).defLePos d iXDef
      ⟩
    ⟩
| Expr.Ir x xDom body =>
    -- Notice we're only using the background valuation.
    let xDom.I: Set3 alg.D := I alg b b xDom
    
    let iBody (iX: alg.D): Set3 alg.D :=
      (I alg (b.update (Sum.inl x) iX) (c.update (Sum.inl x) iX) body)
    
    ⟨
      fun d => ∀ iX: ↑xDom.I.posMem, d ∈ (iBody iX).defMem,
      fun d => ∀ iX: ↑xDom.I.defMem, d ∈ (iBody iX).posMem,
      
      fun d dDefBody xDDef =>
        let dPos := ⟨xDDef, xDom.I.defLePos xDDef xDDef.property⟩
        (iBody xDDef.val).defLePos d (dDefBody dPos)
    ⟩

/- TODO delete?
def PosI (alg: Algebra s) (c: Valuation Var alg.D): (PosExpr s Var) → Set3 alg.D
| PosExpr.var x => sorry
| PosExpr.varBound x => sorry
| PosExpr.opApp op args => sorry
| PosExpr.un a b => sorry
| PosExpr.ir a b => sorry
| PosExpr.ifThen a b => sorry
| PosExpr.Un x xc body => sorry
| PosExpr.Ir x xc body => sorry-/

def I.isMonotonic.standard
  (alg: Algebra s)
  (e: Expr s Var)
  (b c0 c1: Valuation Var alg.D)
  (cLe: c0 ≤ c1)
:
  I alg b c0 e ≤ I alg b c1 e
:=
  match e with
  | Expr.var a => And.intro
      (fun x xIn => (cLe (Sum.inl a)).left x xIn)
      (fun x xIn => (cLe (Sum.inl a)).right x xIn)
  | Expr.varBound a => And.intro
      (fun x xIn => (cLe (Sum.inr a)).left x xIn)
      (fun x xIn => (cLe (Sum.inr a)).right x xIn)
  | Expr.opApp op args => And.intro
      (fun x xIn =>
        let argC0 (i: s.arity op) := (I alg b c0 (args i)).defMem
        let argC1 (i: s.arity op) := (I alg b c1 (args i)).defMem
        let argMono (i: s.arity op): argC0 i ≤ argC1 i :=
          (I.isMonotonic.standard alg (args i) b c0 c1 cLe).left
        let isMono3 := alg.isMonotonic op argC0 argC1 argMono
        isMono3 x xIn)
      (fun x xIn =>
        let argC0 (i: s.arity op) := (I alg b c0 (args i)).posMem
        let argC1 (i: s.arity op) := (I alg b c1 (args i)).posMem
        let argMono (i: s.arity op): argC0 i ≤ argC1 i :=
          (I.isMonotonic.standard alg (args i) b c0 c1 cLe).right
        let isMono3 := alg.isMonotonic op argC0 argC1 argMono
        isMono3 x xIn)
  -- "Right" is one letter too long.
  | Expr.un left rite => And.intro
      (fun x xIn =>
        let left.I0 := (I alg b c0 left).defMem
        let left.I1 := (I alg b c1 left).defMem
        
        let rite.I0 := (I alg b c0 rite).defMem
        let rite.I1 := (I alg b c1 rite).defMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (I.isMonotonic.standard alg left b c0 c1 cLe).left
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (I.isMonotonic.standard alg rite b c0 c1 cLe).left
        
        if hLeft: x ∈ left.I0 then
          let xInLeft1: x ∈ left.I1 := left.isMono x hLeft
          Or.inl xInLeft1
        else if hRite: x ∈ rite.I0 then
          let xInRite1: x ∈ rite.I1 := rite.isMono x hRite
          Or.inr xInRite1
        else
          False.elim (xIn.elim (fun xInL => hLeft xInL) (fun xInR => hRite xInR)))
      
      (fun x xIn =>
        let left.I0 := (I alg b c0 left).posMem
        let left.I1 := (I alg b c1 left).posMem
        
        let rite.I0 := (I alg b c0 rite).posMem
        let rite.I1 := (I alg b c1 rite).posMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (I.isMonotonic.standard alg left b c0 c1 cLe).right
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (I.isMonotonic.standard alg rite b c0 c1 cLe).right
        
        if hLeft: x ∈ left.I0 then
          let xInLeft1: x ∈ left.I1 := left.isMono x hLeft
          Or.inl xInLeft1
        else if hRite: x ∈ rite.I0 then
          let xInRite1: x ∈ rite.I1 := rite.isMono x hRite
          Or.inr xInRite1
        else
          False.elim (xIn.elim (fun xInL => hLeft xInL) (fun xInR => hRite xInR)))
  | Expr.ir left rite => And.intro
      (fun x xIn =>
        let left.I0 := (I alg b c0 left).defMem
        let left.I1 := (I alg b c1 left).defMem
        
        let rite.I0 := (I alg b c0 rite).defMem
        let rite.I1 := (I alg b c1 rite).defMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (I.isMonotonic.standard alg left b c0 c1 cLe).left
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (I.isMonotonic.standard alg rite b c0 c1 cLe).left
        
        if hLeft: x ∈ left.I0 then
          if hRite: x ∈ rite.I0 then
            let xInLeft1: x ∈ left.I1 := left.isMono x hLeft
            let xInRite1: x ∈ rite.I1 := rite.isMono x hRite
            And.intro xInLeft1 xInRite1
          else
            False.elim (hRite xIn.right)
        else
          False.elim (hLeft xIn.left))
      
      (fun x xIn =>
        let left.I0 := (I alg b c0 left).posMem
        let left.I1 := (I alg b c1 left).posMem
        
        let rite.I0 := (I alg b c0 rite).posMem
        let rite.I1 := (I alg b c1 rite).posMem
        
        let left.isMono: left.I0 ≤ left.I1 :=
          (I.isMonotonic.standard alg left b c0 c1 cLe).right
        
        let rite.isMono: rite.I0 ≤ rite.I1 :=
          (I.isMonotonic.standard alg rite b c0 c1 cLe).right
        
        if hLeft: x ∈ left.I0 then
          if hRite: x ∈ rite.I0 then
            let xInLeft1: x ∈ left.I1 := left.isMono x hLeft
            let xInRite1: x ∈ rite.I1 := rite.isMono x hRite
            And.intro xInLeft1 xInRite1
          else
            False.elim (hRite xIn.right)
        else
          False.elim (hLeft xIn.left))
  | Expr.cpl _ => And.intro (fun _ xIn => xIn) (fun _ xIn => xIn)
  | Expr.Un x xDom body => And.intro
      (fun d dIn =>
        let dX := choiceEx dIn
        
        let bUpdated := b.update (Sum.inl x) dX.val
        let c0Updated := c0.update (Sum.inl x) dX.val
        let c1Updated := c1.update (Sum.inl x) dX.val
        
        let dom.I0 := I alg b c0 xDom
        let dom.I1 := I alg b c1 xDom
        
        let body.I0 := I alg bUpdated c0Updated body
        let body.I1 := I alg bUpdated c1Updated body
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
           c0 c1 cLe (Sum.inl x) dX.val
        
        let dom.le: dom.I0 ≤ dom.I1 := I.isMonotonic.standard
          alg xDom b c0 c1 cLe
        
        let body.le: body.I0 ≤ body.I1 := I.isMonotonic.standard
          alg body bUpdated c0Updated c1Updated cUpdatedLe
        
        let dXInDom0: dX.val.val ∈ dom.I0.defMem := dX.val.property
        let dXInDom1: dX.val.val ∈ dom.I1.defMem := dom.le.left dX.val dXInDom0
        
        let dInBody0: d ∈ body.I0.defMem := dX.property
        let dInBody1: d ∈ body.I1.defMem := body.le.left d dInBody0
        
        ⟨⟨dX.val, dXInDom1⟩, dInBody1⟩)
      
      (fun d dIn =>
        let dX := choiceEx dIn
        
        let bUpdated := b.update (Sum.inl x) dX.val
        let c0Updated := c0.update (Sum.inl x) dX.val
        let c1Updated := c1.update (Sum.inl x) dX.val
        
        let dom.I0 := I alg b c0 xDom
        let dom.I1 := I alg b c1 xDom
        
        let body.I0 := I alg bUpdated c0Updated body
        let body.I1 := I alg bUpdated c1Updated body
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
          c0 c1 cLe (Sum.inl x) dX.val
        
        let dom.le: dom.I0 ≤ dom.I1 := I.isMonotonic.standard
          alg xDom b c0 c1 cLe
        
        let body.le: body.I0 ≤ body.I1 := I.isMonotonic.standard
          alg body bUpdated c0Updated c1Updated cUpdatedLe
        
        let dXInDom0: dX.val.val ∈ dom.I0.posMem := dX.val.property
        let dXInDom1: dX.val.val ∈ dom.I1.posMem := dom.le.right dX.val dXInDom0
        
        let dInBody0: d ∈ body.I0.posMem := dX.property
        let dInBody1: d ∈ body.I1.posMem := body.le.right d dInBody0
        
        ⟨⟨dX.val, dXInDom1⟩, dInBody1⟩)
  | Expr.Ir x _xDom body => And.intro
      (fun _d dIn xDDef =>
        let dInXD := dIn xDDef
        
        let bUpdated := b.update (Sum.inl x) xDDef
        let c0Updated := c0.update (Sum.inl x) xDDef
        let c1Updated := c1.update (Sum.inl x) xDDef
        
        let body.I0 := I alg bUpdated c0Updated body
        let body.I1 := I alg bUpdated c1Updated body
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
          c0 c1 cLe (Sum.inl x) xDDef
        
        let body.le: body.I0 ≤ body.I1 :=
          I.isMonotonic.standard alg body bUpdated c0Updated c1Updated cUpdatedLe
        
        body.le.left _ dInXD)
      
      (fun _d dIn xDDef =>
        let dInXD := dIn xDDef
        
        let bUpdated := b.update (Sum.inl x) xDDef
        let c0Updated := c0.update (Sum.inl x) xDDef
        let c1Updated := c1.update (Sum.inl x) xDDef
        
        let body.I0 := I alg bUpdated c0Updated body
        let body.I1 := I alg bUpdated c1Updated body
        
        let cUpdatedLe := Valuation.update.isMonotonic.standard
          c0 c1 cLe (Sum.inl x) xDDef
        
        let body.le: body.I0 ≤ body.I1 :=
          I.isMonotonic.standard alg body bUpdated c0Updated c1Updated cUpdatedLe
        
        body.le.right _ dInXD)

def I.isMonotonic.approximation
  (alg: Algebra s)
  (e: Expr s Var)
  (b0 b1 c0 c1: Valuation Var alg.D)
  (bLe: b0 ⊑ b1)
  (cLe: c0 ⊑ c1)
:
  I alg b0 c0 e ⊑ I alg b1 c1 e
:=
  match e with
  | Expr.var x => And.intro
      (fun d dIn => (cLe (Sum.inl x)).left d dIn)
      (fun d dIn => (cLe (Sum.inl x)).right d dIn)
  | Expr.varBound x => And.intro
      (fun d dIn => (cLe (Sum.inr x)).left d dIn)
      (fun d dIn => (cLe (Sum.inr x)).right d dIn)
  | Expr.opApp op args =>
      let ih (arg: s.arity op) :=
        I.isMonotonic.approximation alg (args arg) b0 b1 c0 c1 bLe cLe
      
      And.intro
        (fun d dIn =>
          let defArgs0 arg := (I alg b0 c0 (args arg)).defMem
          let defArgs1 arg := (I alg b1 c1 (args arg)).defMem
          
          let defArgsLe :=
            alg.isMonotonic op defArgs0 defArgs1 (fun a => (ih a).left)
          
          defArgsLe d dIn)
        (fun d dIn =>
          let posArgs0 arg := (I alg b0 c0 (args arg)).posMem
          let posArgs1 arg := (I alg b1 c1 (args arg)).posMem
          
          let posArgsLe :=
            alg.isMonotonic op posArgs1 posArgs0 (fun a => (ih a).right)
          
          posArgsLe d dIn)
  | Expr.un left rite =>
      let ihL := I.isMonotonic.approximation alg left b0 b1 c0 c1 bLe cLe
      let ihR := I.isMonotonic.approximation alg rite b0 b1 c0 c1 bLe cLe
      
      And.intro
        (fun d dIn => dIn.elim
          (fun inL => Or.inl (ihL.left d inL))
          (fun inR => Or.inr (ihR.left d inR)))
        (fun d dIn => dIn.elim
          (fun inL => Or.inl (ihL.right d inL))
          (fun inR => Or.inr (ihR.right d inR)))
  | Expr.ir left rite =>
      let ihL := I.isMonotonic.approximation alg left b0 b1 c0 c1 bLe cLe
      let ihR := I.isMonotonic.approximation alg rite b0 b1 c0 c1 bLe cLe
      
      And.intro
        (fun d dIn => And.intro (ihL.left d dIn.left) (ihR.left d dIn.right))
        (fun d dIn => And.intro (ihL.right d dIn.left) (ihR.right d dIn.right))
  | Expr.cpl expr =>
      let ih := I.isMonotonic.approximation alg expr b0 b1 b0 b1 bLe bLe
      And.intro
        (fun d dIn => contra (ih.right d) dIn)
        (fun d dIn => contra (ih.left d) dIn)
  | Expr.Un x xDom body =>
      let ihXDom :=
        I.isMonotonic.approximation alg xDom b0 b1 c0 c1 bLe cLe
      
      let ihBody d :=
        I.isMonotonic.approximation alg body
          (b0.update (Sum.inl x) d)
          (b1.update (Sum.inl x) d)
          (c0.update (Sum.inl x) d)
          (c1.update (Sum.inl x) d)
          (Valuation.update.isMonotonic.approximation b0 b1 bLe (Sum.inl x) d)
          (Valuation.update.isMonotonic.approximation c0 c1 cLe (Sum.inl x) d)
      
      And.intro
        (fun d dIn =>
          let dX := choiceEx dIn
          ⟨
            ⟨dX.val, ihXDom.left _ dX.val.property⟩,
            (ihBody dX.val).left d dX.property⟩
          )
        (fun d dIn =>
          let dX := choiceEx dIn
          ⟨
            ⟨dX.val, ihXDom.right _ dX.val.property⟩,
            (ihBody dX.val).right d dX.property⟩
          )
  | Expr.Ir x xDom body =>
      let ihXDom :=
        I.isMonotonic.approximation alg xDom b0 b1 b0 b1 bLe bLe
      
      let ih d :=
        I.isMonotonic.approximation alg body
          (b0.update (Sum.inl x) d)
          (b1.update (Sum.inl x) d)
          (c0.update (Sum.inl x) d)
          (c1.update (Sum.inl x) d)
          (Valuation.update.isMonotonic.approximation b0 b1 bLe (Sum.inl x) d)
          (Valuation.update.isMonotonic.approximation c0 c1 cLe (Sum.inl x) d)
      
      And.intro
        (fun d dIn dXPos1 =>
          let dXPos0: { d: alg.D // d ∈ (I alg b0 b0 xDom).posMem } :=
            ⟨dXPos1, ihXDom.right dXPos1 dXPos1.property⟩
          (ih dXPos1).left d (dIn dXPos0))
        (fun d dIn dXPos0 =>
          let dXPos1: { d: alg.D // d ∈ (I alg b1 b1 xDom).defMem } :=
            ⟨dXPos0, ihXDom.left dXPos0 dXPos0.property⟩
          (ih dXPos1).right d (dIn dXPos1))


-- Interpretation on definition lists is defined pointwise.
def DefList.I
  (alg: Algebra s)
  (b c: Valuation Var alg.D)
  (dl: DefList s Var)
:
  Valuation Var alg.D
:=
  fun x =>
    match x with
    | Sum.inl x => _root_.I alg b c (dl.getDef x)
    | Sum.inr _ =>
        /-
          These are only used by the interpretation of expressions,
          because there are no global bound variables. I could
          theoretically split Valuation into two types (one with bound
          vars and one without, I guess that would result in duplicated
          work.)
        -/
        Set3.empty
