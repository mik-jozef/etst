import Utils.Valuation
import Utils.ExprIsFreeVar


def Args
  (s: Signature)
  (op: s.Op)
  (D: Type u)
:=
  s.Params op → Set D

/-
  Salgebras act not on elements themselves (like algebras do), but
  on sets of elements, monotonically.
  
  (Equivalently, a salgebra on T is an algebra on sets of T whose
  operations are monotonic.)
  
  A salgebra on a signature `sig` provides an interpretation of
  each operation in the signature.
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


/-
  The interpretation of an expression is defined using two valuations
  we will call "background" and "context". Context is the "main"
  valuation that is normally used to interpret the variables in the
  expression. Background is used to interpret complements and their
  subexpressions. In particular,
  
      (Expr.cpl expr).interpretation b c
  
  is defined in terms of
  
      expr.interpretation b b \,.
  
  When background and context are the same valuation, this
  definition reduces to the usual one with a single valuation.
  
  The three-valuedness is handled in an intuitive fashion -- the
  definite members of an expression are defined in terms of the
  definite members of its subexpressions, and the same applies to
  the possible members.
  
  An interesting exception is the complement, where `d` is a
  definite member of the complement of `expr` iff `d` is not
  a *possible* member of `expr`, and vice versa.
-/
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


def DefList.GetDef (sig: Signature) := Nat → Expr sig

/-
  A definition list is a map from natural numbers to expressions.
  It is used to allow recursive definitions -- the free variables
  in a definition refer to other definitions of the definition list.
-/
structure DefList (sig: Signature) where
  getDef: DefList.GetDef sig

/-
  The definition x depends on y if x = y or x contains y, possibly
  transitively.
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
  {getDef: GetDef sig}
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
  A definition list is finitely bounded iff every definition only
  depends on finitely many other definitions (transitively). This
  excludes definition lists like
  
  ```
    let def0 := def1
    let def1 := def3
    let def3 := def4
    ...
  ```
-/
def DefList.IsFinBounded (getDef: GetDef sig): Prop :=
  ∀ name,
  ∃ upperBound,
  ∀ {dep}
    (_: DependsOn getDef name dep)
  ,
    dep < upperBound

-- A finitely bounded definition list.
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
