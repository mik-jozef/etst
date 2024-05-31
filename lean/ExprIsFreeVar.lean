import Utils.BasicUtils


-- Thanks to answerers of https://proofassistants.stackexchange.com/q/1740
structure Signature where
  Op: Type u
  Params: Op → Type v


inductive Expr (sig: Signature) where
| var (x: Nat)
| op (op: sig.Op) (args: sig.Params op → Expr sig)
| un (left rite: Expr sig)
| ir (left rite: Expr sig)
| cpl (expr: Expr sig)
| ifThen (cond expr: Expr sig)
| Un (x: Nat) (body: Expr sig)
| Ir (x: Nat) (body: Expr sig)

namespace Expr
  instance: Coe Nat (Expr s) where
    coe := fun n => Expr.var n
  
  instance (n: Nat): OfNat (Expr s) n where
    ofNat := Expr.var n
  
  def any: Expr s := Expr.un 0 (Expr.cpl 0)
end Expr

def Expr.IsFreeVar
  (expr: Expr sig)
  (boundVars: Set Nat)
:
  Set Nat
:=
  fun x =>
    match expr with
      | var v => x = v ∧ v ∉ boundVars
      | op _ args => ∃ param, (args param).IsFreeVar boundVars x
      | un left rite =>
          Or
            (left.IsFreeVar boundVars x)
            (rite.IsFreeVar boundVars x)
      | ir left rite =>
          Or
            (left.IsFreeVar boundVars x)
            (rite.IsFreeVar boundVars x)
      | cpl expr => expr.IsFreeVar boundVars x
      | ifThen cond expr =>
          Or
            (cond.IsFreeVar boundVars x)
            (expr.IsFreeVar boundVars x)
      | Un bv body => body.IsFreeVar (fun v => v ∈ boundVars ∨ v = bv) x
      | Ir bv body => body.IsFreeVar (fun v => v ∈ boundVars ∨ v = bv) x


def Expr.IsFreeVar.boundNotFree
  (expr: Expr sig)
  {boundVars: Set Nat}
  (isBound: x ∈ boundVars)
:
  ¬expr.IsFreeVar boundVars x
:=
  let boundVarsUpdated xUn: Set Nat :=
    fun x => x ∈ boundVars ∨ x = xUn
  
  fun isFreeVar =>
    match expr with
    | var _ =>
      isFreeVar.right (isFreeVar.left ▸ isBound)
    | op _ _ =>
      let arg := isFreeVar.unwrap
      (boundNotFree _ isBound) arg.property
    | un _ _ =>
      isFreeVar.elim
        (boundNotFree _ isBound)
        (boundNotFree _ isBound)
    | ir _ _ =>
      isFreeVar.elim
        (boundNotFree _ isBound)
        (boundNotFree _ isBound)
    | cpl expr =>
      boundNotFree expr isBound isFreeVar
    | ifThen _ _ =>
      isFreeVar.elim
        (boundNotFree _ isBound)
        (boundNotFree _ isBound)
    | Un xUn body =>
      let xIn: x ∈ boundVarsUpdated xUn := Or.inl isBound
      
      boundNotFree body xIn isFreeVar
    | Ir xUn body =>
      let xIn: x ∈ boundVarsUpdated xUn := Or.inl isBound
      
      boundNotFree body xIn isFreeVar

def Expr.IsFreeVar.getBoundVars
  {expr: Expr sig}
  (_: expr.IsFreeVar boundVars x)
:
  Set Nat
:=
  boundVars

def Expr.IsFreeVar.nopeFreeInUn
  (isFreeVar: x ∈ (Expr.Un x body).IsFreeVar boundVars)
:
  P
:=
  let isFreeVarBody: x ∈ body.IsFreeVar _ := isFreeVar
  let inB: x ∈ isFreeVarBody.getBoundVars := Or.inr rfl
  
  (boundNotFree body inB isFreeVar).elim

def Expr.IsFreeVar.toOtherBounds
  {expr: Expr sig}
  (isFreeVar: expr.IsFreeVar boundVars x)
  (boundVarsOther: Set Nat)
:
  expr.IsFreeVar boundVarsOther x ∨ x ∈ boundVarsOther
:=
  if h: x ∈ boundVarsOther then
    Or.inr h
  else
    let elimInB {P: Prop} (p: P ∨ x ∈ boundVarsOther): P :=
      p.elim id (fun inB => False.elim (h inB))
    
    match expr with
    | var _ =>
      isFreeVar.left ▸
      Or.inl (And.intro rfl h)
    
    | op _ _ =>
      let fv := isFreeVar.unwrap
      Or.inl ⟨fv, elimInB (toOtherBounds fv.property boundVarsOther)⟩
    
    | un _ _ =>
      Or.inl
        (isFreeVar.elim
          (fun inL =>
            Or.inl (elimInB (toOtherBounds inL boundVarsOther)))
          (fun inR =>
            Or.inr (elimInB (toOtherBounds inR boundVarsOther))))
    
    | ir _ _ =>
      Or.inl
        (isFreeVar.elim
          (fun ifvL =>
            Or.inl (elimInB (toOtherBounds ifvL boundVarsOther)))
          (fun ifvR =>
            Or.inr (elimInB (toOtherBounds ifvR boundVarsOther))))
    
    | cpl expr =>
      Or.inl
        (elimInB (@toOtherBounds _ _ _ expr isFreeVar boundVarsOther))
    
    | ifThen _ _ =>
      Or.inl
        (isFreeVar.elim
          (fun ifvL =>
            Or.inl (elimInB (toOtherBounds ifvL boundVarsOther)))
          (fun ifvR =>
            Or.inr (elimInB (toOtherBounds ifvR boundVarsOther))))
    
    | Un xUn body =>
      let ifvBody:
        body.IsFreeVar (fun v => v ∈ boundVars ∨ v = xUn) x
      :=
        isFreeVar
      
      let ivfOr :=
        (toOtherBounds
          ifvBody
          (fun x => boundVarsOther x ∨ x = xUn))
      
      ivfOr.elim
        (fun ifvOther => Or.inl ifvOther)
        (fun inB =>
          inB.elim
            (fun inOther => Or.inr (elimInB (Or.inl inOther)))
            (fun eq => nopeFreeInUn (eq ▸ isFreeVar)))
    
    | Ir xUn body =>
      let ifvBody:
        body.IsFreeVar (fun v => v ∈ boundVars ∨ v = xUn) x
      :=
        isFreeVar
      
      let ivfOr :=
        (toOtherBounds
          ifvBody
          (fun x => boundVarsOther x ∨ x = xUn))
      
      ivfOr.elim
        (fun ifvOther => Or.inl ifvOther)
        (fun inB =>
          inB.elim
            (fun inOther => Or.inr (elimInB (Or.inl inOther)))
            (fun eq => nopeFreeInUn (eq ▸ isFreeVar)))

def Expr.IsFreeVar.toBoundsNin
  {expr: Expr sig}
  (isFreeVar: expr.IsFreeVar boundVars x)
  (ninOther: x ∉ boundVarsOther)
:
  expr.IsFreeVar boundVarsOther x
:=
  (toOtherBounds isFreeVar boundVarsOther).elim
    id
    (fun inOther => False.elim (ninOther inOther))

def Expr.IsFreeVar.incrementBounds
  {expr: Expr sig}
  (isFreeVar: expr.IsFreeVar boundVars x)
  (addedBoundVar: Nat)
:
  expr.IsFreeVar (boundVars ∪ {addedBoundVar}) x ∨ x = addedBoundVar
:=
  (toOtherBounds isFreeVar (boundVars ∪ {addedBoundVar})).elim
    (fun isFree => Or.inl isFree)
    (fun inB =>
      inB.elim
        (fun inL => False.elim (boundNotFree expr inL isFreeVar))
        (fun inR => Or.inr inR))


def Expr.IsFreeVar.var
  (ninBound: v ∉ boundVars)
:
  v ∈ (@Expr.var sig v).IsFreeVar boundVars
:=
  And.intro rfl ninBound

def Expr.IsFreeVar.varEmptyBound
  (v: Nat)
:
  v ∈ (@Expr.var sig v).IsFreeVar Set.empty
:=
  var False.elim

def Expr.IsFreeVar.op
  {sig: Signature}
  (op: sig.Op)
  (args: sig.Params op → Expr sig)
  {param: sig.Params op}
  (isFreeVar: x ∈ (args param).IsFreeVar boundVars)
:
  x ∈ (Expr.op op args).IsFreeVar boundVars
:= ⟨
  param,
  isFreeVar
⟩

def Expr.IsFreeVar.unLeft
  (isFreeVar: x ∈ left.IsFreeVar boundVars)
  (rite: Expr sig)
:
  x ∈ (Expr.un left rite).IsFreeVar boundVars
:=
  Or.inl isFreeVar

def Expr.IsFreeVar.unRite
  (left: Expr sig)
  (isFreeVar: x ∈ rite.IsFreeVar boundVars)
:
  x ∈ (Expr.un left rite).IsFreeVar boundVars
:=
  Or.inr isFreeVar

def Expr.IsFreeVar.irRite
  (left: Expr sig)
  (isFreeVar: x ∈ rite.IsFreeVar boundVars)
:
  x ∈ (Expr.ir left rite).IsFreeVar boundVars
:=
  Or.inr isFreeVar

def Expr.IsFreeVar.irLeft
  (isFreeVar: x ∈ left.IsFreeVar boundVars)
  (rite: Expr sig)
:
  x ∈ (Expr.ir left rite).IsFreeVar boundVars
:=
  Or.inl isFreeVar

def Expr.IsFreeVar.ifThenCond
  {cond: Expr sig}
  (isFreeVar: x ∈ cond.IsFreeVar boundVars)
  (body: Expr sig)
:
  x ∈ (Expr.ifThen cond body).IsFreeVar boundVars
:=
  Or.inl isFreeVar

def Expr.IsFreeVar.ifThenBody
  (cond: Expr sig)
  (isFreeVar: x ∈ body.IsFreeVar boundVars)
:
  x ∈ (Expr.ifThen cond body).IsFreeVar boundVars
:=
  Or.inr isFreeVar

def Expr.IsFreeVar.arbUn
  (x: Nat)
  {body: Expr sig}
  (isFreeVar: xf ∈ body.IsFreeVar boundVars)
:
  xf ∈ IsFreeVar (Un x body) boundVars ∨ xf = x
:=
  if eq: xf = x then
    Or.inr eq
  else
    (toOtherBounds isFreeVar (fun xO => boundVars xO ∨ xO = x)).elim
      (fun ifv => Or.inl ifv)
      (fun inBO =>
        inBO.elim
          (fun inB =>
            False.elim (boundNotFree body inB isFreeVar))
          Or.inr)


inductive PosExpr (sig: Signature) where
| var (v: Nat)
| opApp (op: sig.Op) (args: sig.Params op → PosExpr sig)
| un (left: PosExpr sig) (rite: PosExpr sig)
| ir (left: PosExpr sig) (rite: PosExpr sig)
| ifThen (cond expr: PosExpr sig)
  -- Complementing a bound variable is OK.
| Un (x xc: Nat) (body: PosExpr sig)
| Ir (x xc: Nat) (body: PosExpr sig)

def PosExpr.toExpr
  (complements: Nat → Option Nat := fun _ => none)
:
  PosExpr sig → Expr sig

| PosExpr.var v =>
  match complements v with
  | none => Expr.var v
  | some v' => Expr.cpl (Expr.var v')

| PosExpr.opApp op args =>
    Expr.op op (fun p => (args p).toExpr complements)

| PosExpr.un left rite =>
    Expr.un (left.toExpr complements) (rite.toExpr complements)

| PosExpr.ir left rite =>
    Expr.ir (left.toExpr complements) (rite.toExpr complements)

| PosExpr.ifThen cond expr =>
    Expr.ifThen (cond.toExpr complements) (expr.toExpr complements)

| PosExpr.Un x xc body =>
    Expr.Un x (body.toExpr (fun v => if v = xc then x else complements v))

| PosExpr.Ir x xc body =>
    Expr.Ir x (body.toExpr (fun v => if v = xc then x else complements v))
