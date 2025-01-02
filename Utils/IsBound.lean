/-
  Contains utility files related to bound variables.
-/

import WFC.Ch2_Valuation


inductive IsBoundTo:
  (boundVars: List (ValVar Var D)) → Var → D → Prop
|
  InHead
    {rest: List (ValVar Var D)}
    {x: Var}
    {d: D}
  :
    IsBoundTo (⟨d, x⟩ :: rest) x d
|
  InTail
    (tail: IsBoundTo rest x d)
    (neq: x ≠ xH)
    dH
  :
    IsBoundTo (⟨dH, xH⟩ :: rest) x d

def IsBoundTo.inBoundVars:
  IsBoundTo boundVars x d →
  ⟨d, x⟩ ∈ boundVars
|
  InHead => List.mem_cons_self _ _
| InTail tail _ _ => List.mem_cons_of_mem _ (inBoundVars tail)

def IsBoundTo.exOfInBoundVars
  (inBoundVars: ⟨d, x⟩ ∈ boundVars)
:
  ∃ dB, IsBoundTo boundVars x dB
:=
  match inBoundVars with
  | List.Mem.head _ => ⟨d, InHead⟩
  | List.Mem.tail ⟨headD, headX⟩ inTail =>
    let ⟨dB, isBoundTo⟩ := IsBoundTo.exOfInBoundVars inTail
    if h: x = headX then
      ⟨headD, h ▸ IsBoundTo.InHead⟩
    else
      ⟨dB, IsBoundTo.InTail isBoundTo h headD⟩

def IsBoundTo.listHeadEq
  (isBoundTo: IsBoundTo (⟨dd, xx⟩ :: boundVars) x d)
  (xEq: x = xx)
:
  d = dd
:=
  match isBoundTo with
  | InHead => rfl

def IsBoundTo.listHeadNeq
  (isBoundTo: IsBoundTo (⟨dd, xx⟩ :: boundVars) x d)
  (xNeq: x ≠ xx)
:
  IsBoundTo boundVars x d
:=
  match isBoundTo with
  | InHead => (xNeq rfl).elim
  | InTail tail _ _ => tail

def IsBoundTo.isUnique
  (isBoundTo0: IsBoundTo boundVars x d0)
  (isBoundTo1: IsBoundTo boundVars x d1)
:
  d0 = d1
:=
  -- Lean throws an error if these match expressions are merged.
  match isBoundTo0 with
  | InHead =>
    match isBoundTo1 with
    | InHead => rfl
  | InTail isBoundTail0 neq _ =>
    match isBoundTo1 with
    | InHead => absurd rfl neq
    | InTail isBoundTail1 _ _ =>
      isBoundTail0.isUnique isBoundTail1

def IsBound
  (boundVars: List (ValVar Var Pair))
  (x: Var)
:
  Prop
:=
  ∃ d, IsBoundTo boundVars x d

def IsBound.Not.notBoundHeadNotEq
  (notBound: ¬ IsBound (⟨dB, xB⟩ :: boundVars) x)
:
  x ≠ xB
:=
  fun xEq =>
    notBound ⟨dB, xEq ▸ IsBoundTo.InHead⟩

def IsBound.Not.notBoundTail
  (notBound: ¬ IsBound (⟨dB, xB⟩ :: boundVars) x)
:
  ¬ IsBound boundVars x
:=
  fun ⟨d, isBoundTo⟩ =>
    if h: x = xB then
      notBound ⟨dB, h ▸ IsBoundTo.InHead⟩
    else
      let isBound := IsBoundTo.InTail isBoundTo h dB
      notBound ⟨d, isBound⟩


def IsVarFree
  (boundVars: List (ValVar Var D))
  (x: Var)
:
  Prop
:=
  ∀ d, ⟨d, x⟩ ∉ boundVars

def IsVarFree.Not.exBoundOfNot
  {boundVars: List (ValVar Var D)}
  (notFree: ¬ IsVarFree boundVars x)
:
  ∃ d, ⟨d, x⟩ ∈ boundVars
:=
  notFree.toEx fun _ => Not.dne

def IsVarFree.Not.exBoundTo
  {boundVars: List (ValVar Var D)}
  (notFree: ¬ IsVarFree boundVars x)
:
  ∃ d, IsBoundTo boundVars x d
:=
  let ⟨_, inBoundVars⟩ := IsVarFree.Not.exBoundOfNot notFree
  
  IsBoundTo.exOfInBoundVars inBoundVars

def IsVarFree.nopeIsBoundTo
  (isFree: IsVarFree boundVars x)
  (isBoundTo: IsBoundTo boundVars x d)
:
  P
:=
  False.elim (isFree d isBoundTo.inBoundVars)

def IsVarFree.nopeIsBound
  (isFree: IsVarFree boundVars x)
  (isBound: IsBound boundVars x)
:
  P
:=
  isFree.nopeIsBoundTo isBound.unwrap.property

def IsVarFree.ofTail
  (isFree: IsVarFree boundVars x)
  (neqHead: xH ≠ x)
  dH
:
  IsVarFree (⟨dH, xH⟩ :: boundVars) x
:=
  fun _ isBound =>
    match List.mem_cons.mp isBound with
    | Or.inl eq => ValVar.noConfusion eq fun _ => Ne.symm neqHead
    | Or.inr inBoundTail => isFree _ inBoundTail
