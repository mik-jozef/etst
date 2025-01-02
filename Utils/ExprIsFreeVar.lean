/-
  Helpers for working with free variables in expressions.
-/

import WFC.Ch1_Expr


def Expr.IsFreeVar.boundNotFree
  (expr: Expr Var sig)
  {boundVars: Set Var}
  (isBound: x ∈ boundVars)
:
  ¬expr.IsFreeVar boundVars x
:=
  let boundVarsUpdated xUn: Set Var :=
    fun x => x ∈ boundVars ∨ x = xUn
  
  fun isFreeVar =>
    match expr with
    | var _ =>
      isFreeVar.right (isFreeVar.left ▸ isBound)
    | op _ _ =>
      let arg := isFreeVar.unwrap
      (boundNotFree _ isBound) arg.property
    | cpl expr =>
      boundNotFree expr isBound isFreeVar
    | arbUn xUn body =>
      let xIn: x ∈ boundVarsUpdated xUn := Or.inl isBound
      
      boundNotFree body xIn isFreeVar
    | arbIr xUn body =>
      let xIn: x ∈ boundVarsUpdated xUn := Or.inl isBound
      
      boundNotFree body xIn isFreeVar

def Expr.IsFreeVar.getBoundVars
  {expr: Expr Var sig}
  (_: expr.IsFreeVar boundVars x)
:
  Set Var
:=
  boundVars

def Expr.IsFreeVar.nopeFreeInUn
  (isFreeVar: x ∈ (arbUn x body).IsFreeVar boundVars)
:
  P
:=
  let isFreeVarBody: x ∈ body.IsFreeVar _ := isFreeVar
  let inB: x ∈ isFreeVarBody.getBoundVars := Or.inr rfl
  
  (boundNotFree body inB isFreeVar).elim

def Expr.IsFreeVar.toOtherBounds
  {expr: Expr Var sig}
  (isFreeVar: expr.IsFreeVar boundVars x)
  (boundVarsOther: Set Var)
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
    
    | cpl expr =>
      Or.inl
        (elimInB
          (toOtherBounds
            (expr := expr)
            isFreeVar
            boundVarsOther))
    
    | arbUn xUn body =>
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
    
    | arbIr xUn body =>
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
  {expr: Expr Var sig}
  (isFreeVar: expr.IsFreeVar boundVars x)
  (ninOther: x ∉ boundVarsOther)
:
  expr.IsFreeVar boundVarsOther x
:=
  (toOtherBounds isFreeVar boundVarsOther).elim
    id
    (fun inOther => False.elim (ninOther inOther))

def Expr.IsFreeVar.incrementBounds
  {expr: Expr Var sig}
  (isFreeVar: expr.IsFreeVar boundVars x)
  (addedBoundVar: Var)
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
  {v: Var}
  (ninBound: v ∉ boundVars)
:
  v ∈ (@Expr.var Var sig v).IsFreeVar boundVars
:=
  And.intro rfl ninBound

def Expr.IsFreeVar.varEmptyBound
  (v: Var)
:
  v ∈ (@Expr.var Var sig v).IsFreeVar Set.empty
:=
  var False.elim

def Expr.IsFreeVar.op
  {sig: Signature}
  (op: sig.Op)
  (args: sig.Params op → Expr Var sig)
  {param: sig.Params op}
  (isFreeVar: x ∈ (args param).IsFreeVar boundVars)
:
  x ∈ (Expr.op op args).IsFreeVar boundVars
:= ⟨
  param,
  isFreeVar
⟩

def Expr.IsFreeVar.arbUn
  (x: Var)
  {body: Expr Var sig}
  (isFreeVar: xf ∈ body.IsFreeVar boundVars)
:
  xf ∈ IsFreeVar (arbUn x body) boundVars ∨ xf = x
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
