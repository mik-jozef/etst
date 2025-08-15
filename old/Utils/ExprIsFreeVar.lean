/-
  Helpers for working with free variables in expressions.
-/

import old.WFC.Ch1_Expr


def Expr.IsFreeVar.arbUnUnfold
  (isFreeVar: x ∈ (arbUn xB body).IsFreeVar boundVars)
:
  x ∈ body.IsFreeVar (fun v => v ∈ boundVars ∨ v = xB)
:=
  isFreeVar

def Expr.IsFreeVar.arbIrUnfold
  (isFreeVar: x ∈ (arbIr xB body).IsFreeVar boundVars)
:
  x ∈ body.IsFreeVar (fun v => v ∈ boundVars ∨ v = xB)
:=
  isFreeVar

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
    | cpl expr =>
      boundNotFree expr isBound isFreeVar
    | arbUn xUn body =>
      let xIn: x ∈ boundVarsUpdated xUn := Or.inl isBound
      
      boundNotFree body xIn isFreeVar
    | arbIr xUn body =>
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
  (isFreeVar: x ∈ (arbUn x body).IsFreeVar boundVars)
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
    
    | cpl expr =>
      Or.inl
        (elimInB (@toOtherBounds _ _ _ expr isFreeVar boundVarsOther))
    
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

def Expr.IsFreeVar.arbUn
  (x: Nat)
  {body: Expr sig}
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

def Expr.IsFreeVar.toIsFreeEmptyList
  (isFree: IsFreeVar expr Set.empty x)
:
  IsFreeVar expr (fun x => x ∈ []) x
:=
  list_mem_empty_eq_set_empty ▸ isFree
