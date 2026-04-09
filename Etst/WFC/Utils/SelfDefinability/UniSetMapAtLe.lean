import Etst.WFC.Utils.MembershipPs.OutIntro3
import Etst.WFC.Utils.SelfDefinability.UniSetMapHelpers

namespace Etst.uniSetMapDl
open SingleLaneExpr


def IsInappExtIh
  (dl: DefList)
  (outSet: Nat → Set Pair)
  (externalCause: Cause Pair)
:
  Prop
:=
  externalCause.IsInapplicable outSet fun x d =>
    {n fv expr dInt: _} →
    x = uniSetMapDl.consts.uniSetMap →
    d = .pair (uniSetMapIndex dl n fv expr) dInt →
    ((dl.prefix n).triIntp fv expr).defMem dInt

def intOfExtCycle
  (dl: DefList)
  (n: Nat)
  (extCycle: Nat → Set Pair)
  (x: Nat)
  (d: Pair)
:
  Prop
:=
  Or
    (extCycle
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndexDef dl n x) d))
    (¬ x < n)

def allInternalInapp {dl n fv d expr}
  {extCycle: Nat → Set Pair}
  (extIsEmpty:
    ∀ {x d},
      extCycle x d →
      (cause: Cause Pair) →
      cause.IsWeakCause (uniSetMapDl.getDef x) d →
      uniSetMapDl.IsCauseInapplicable extCycle cause)
  (everyCauseInapp:
    ∀ {x d},
      extCycle x d →
      (cause: Cause Pair) →
      cause.IsWeakCause (uniSetMapDl.getDef x) d →
      IsInappExtIh dl extCycle cause)
  (inExtCycle:
    extCycle
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) d))
  (cause : Cause Pair)
  (isCause: cause.IsWeakCauseFv fv expr d)
:
  (dl.prefix n).IsCauseInapplicableExtended
    (intOfExtCycle dl n extCycle)
    cause
:=
  match expr with
  | .const x =>
    if h: x < n then
      let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseConst
      match isExtInapp with
      | .blockedCins (d:=dd) (x:=xx) (Or.inl ⟨xEq, dEq⟩) inCycle =>
        let out := DefList.Out.intro extCycle extIsEmpty inCycle
        let insGetNth :=
          uniSetMapDl.getNthDl (lane:=.posLane) (fv:=[]) h
        False.elim (out.isSound (xEq ▸ dEq ▸ insGetNth))
      | .blockedCins (d:=dd) (x:=xx) (Or.inr ⟨xEq, dEq⟩) inCycle =>
        let inCycle:
          extCycle
            uniSetMapDl.consts.uniSetMap
            (.pair (uniSetMapIndexDef dl n x) d)
        :=
          xEq ▸ dEq ▸ inCycle
        let intCycle x d :=
          extCycle
            uniSetMapDl.consts.uniSetMap
            (.pair (uniSetMapIndex dl n fv (.const x)) d)
        .blockedCinsCycle isCause.constElim (Or.inl inCycle)
    else
      .blockedCinsCycle isCause.constElim (Or.inr h)
  | .var _ => sorry
  | .null => sorry
  | .pair _ _ => sorry
  | .ir _ _ => sorry
  | .full _ => sorry
  | .compl _ =>
    let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseCompl
    match isExtInapp with
    | .blockedBout (d:=dd) (x:=xx) ⟨xEq, dEq⟩ isDefFn =>
      let isDef := not_not_intro (isDefFn xEq dEq)
      let isInapp := isCause.isInapplicableOfIsNonmember isDef
      match isInapp with
      | .blockedCins inCins notPos =>
        .blockedCinsOut inCins (DefList.Out.isComplete notPos)
      | .blockedBout inBout isDef =>
        .blockedBout inBout (DefList.Ins.isComplete isDef)
  | .arbIr _ => sorry

/-
  Has to use the weird equality trick :( else we get:
  
  ```
    fail to show termination for
    [...]
    Not considering parameter ins of Etst.externalInsElimHelper:
      its type Etst.DefList.Ins is an inductive family and
      indices are not variables
  ```
-/
mutual
def externalInsElimHelper {dl n fv index cst expr p}
  (ins: uniSetMapDl.Ins cst index)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
:
(expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  match ins with
  | .intro _ _ cause isCause cinsSat boutSat =>
    let ins := isCause cause.leastValsApxAreSat
    let ⟨dlEnc, ins⟩ := inArbUnElim (cstEq ▸ indexEq ▸ ins)
    let ⟨fvEnc, ins⟩ := inArbUnElim ins
    let ⟨exprEnc, ins⟩ := inArbUnElim ins
    let ⟨insEnc, insList⟩ := inPairElim ins
    let ⟨dlEncEq, fvEncEq, exprEncEq⟩ :=
      let ⟨insDl, ins⟩ := inPairElim insEnc
      let ⟨insFv, insExpr⟩ := inPairElim ins
      And.intro
        (inVarElim insDl rfl)
        (And.intro
          (inVarElim insFv rfl)
          (inVarElim insExpr rfl))
    
    match expr with
    | .const x =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      let inCins := isAtElimConst insList cinsSat
      let ih := externalInsElimHelper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .var x =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      isAtElimVar insList cinsSat
    | .null => sorry
    | .pair _ _ => sorry
    | .ir _ _ => sorry
    | .full _ => sorry
    | .compl _ =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      let inBout := boutSat (isAtElimCompl insList).dne
      externalOutElimHelper inBout rfl rfl
    | .arbIr _ =>
      let insList := dlEncEq ▸ fvEncEq ▸ exprEncEq ▸ insList
      inArbIr fun dX =>
        let insBody := cinsSat (isAtElimArbIr insList dX)
        externalInsElimHelper insBody rfl rfl

def externalOutElimHelper {dl n fv index cst expr p}
  (out: uniSetMapDl.Out cst index)
  (cstEq: cst = uniSetMapDl.consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  match out with
  | .intro extCycle extIsEmpty inExtCycle =>
    let everyCauseInapp {x d}
      (inCycle: extCycle x d)
      {cause}
      (isCause: cause.IsWeakCause (uniSetMapDl.getDef x) d)
    :
      IsInappExtIh dl extCycle cause
    :=
      match extIsEmpty inCycle cause isCause with
      | .blockedCins _ inCins inCycle =>
        .blockedCins inCins inCycle
      | .blockedBout _ inBout ins =>
        .blockedBout inBout fun xEq dEq =>
          externalInsElimHelper ins xEq dEq
    
    fun isPos =>
      let isCause: Cause.IsWeakCauseFv _ fv expr p :=
        Cause.IsWeakCauseFv.ofValPos isPos
      let isInapplicable :=
        allInternalInapp
          extIsEmpty
          everyCauseInapp
          (cstEq ▸ indexEq ▸ inExtCycle)
          _
          isCause
      match isInapplicable with
      | .blockedCinsCycle inCins inCycle =>
        let out :=
          DefList.Out.intro3
            (intOfExtCycle dl n extCycle)
            (fun
            | Or.inl inCycle =>
              allInternalInapp extIsEmpty everyCauseInapp inCycle
            | Or.inr xNotLt =>
              fun cause isCause =>
                let isCause :=
                  DefList.prefix_none_at xNotLt ▸ isCause
                isCause.noneElim)
            inCycle
        out.nopePos inCins
      | .blockedCinsOut inCins out => out.isSound inCins
      | .blockedBout inBout ins => ins.nopeNotDef inBout
end


def externalInsElim {dl n fv expr p}
  (ins:
    uniSetMapDl.Ins
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  externalInsElimHelper ins rfl rfl

def externalOutElim {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      uniSetMapDl.consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  externalOutElimHelper out rfl rfl

def uniSetMapAt_le
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  uniSetMapAt dl n fv expr ⊑ expr.triIntp fv (dl.prefix n).wfm
:= {
  defLe _ := externalInsElim ∘ DefList.Ins.isComplete
  posLe _ :=
    Function.mtr (externalOutElim ∘ DefList.Out.isComplete)
}
