import Etst.WFC.Utils.MembershipPs.OutIntro3
import Etst.WFC.Utils.SelfDefinability.UniSetMapHelpers

namespace Etst.uniSetMapDl
open SingleLaneExpr


def CinsIh
  (dl: DefList)
  (n: Nat)
  (intCause: Cause Pair)
:
  Prop
:=
  {x d: _} →
  intCause.cins x d →
  (vals.uniSetMap).defMem (.pair (uniSetMapIndexDef dl n x) d)

def BoutIh
  (dl: DefList)
  (n: Nat)
  (intCause: Cause Pair)
:
  Prop
:=
  {x d: _} →
  intCause.bout x d →
  ¬ (vals.uniSetMap).posMem (.pair (uniSetMapIndexDef dl n x) d)


def IntCauseIsInappIh
  (dl: DefList)
  (n: Nat)
  (intCycle: Nat → Set Pair)
  (intCause: Cause Pair)
:
  Prop
:=
  intCause.IsInapplicable
    intCycle
    (fun xInt dInt =>
      vals.uniSetMap.defMem
        (.pair (uniSetMapIndexDef dl n xInt) dInt))

def AllIntCausesInappIh
  (dl: DefList)
  (n: Nat)
  (intCycle: Nat → Set Pair)
  (fv: List Pair)
  (expr: BasicExpr)
  (p: Pair)
:=
  ∀ {intCause: Cause Pair},
    intCause.IsWeakCauseFv fv expr p →
    IntCauseIsInappIh dl n intCycle intCause

def extOfIntCycle
  (dl: DefList)
  (n: Nat)
  (intCycle: Nat → Set Pair)
  (xExt: Nat)
  (pExt: Pair)
:
  Prop
:=
  And
    (xExt = consts.uniSetMap)
    (∃ fv expr pInt,
      And
      (AllIntCausesInappIh dl n intCycle fv expr pInt)
      (pExt = .pair (uniSetMapIndex dl n fv expr) pInt))

mutual
def internalCauseElim {dl n fv expr p}
  {intCause: Cause Pair}
  (intIsCause: intCause.IsStrongCauseFv fv expr p)
  (cinsIns: ∀ {x d}, intCause.cins x d → ((dl.prefix n).wfm x).defMem d)
  (cinsIh: CinsIh dl n intCause)
  (boutIh: BoutIh dl n intCause)
:
  (vals.uniSetMap).defMem (.pair (uniSetMapIndex dl n fv expr) p)
  
:=
  match expr with
  | .const x =>
    let inDefExt := cinsIh intIsCause.constElim
    let inInt := cinsIns intIsCause.constElim
    let inIntDef := InWfm.in_def_no_fv (lane := .defLane) inInt
    let xLt: x < n :=
      -- Indentation note: if you ever make your own linter, then not
      -- indenting the `ninNone ...` is good actually, because even
      -- whitespace sensitive parsing would still be unambiguous.
      byContradiction fun nLt =>
      ninNone (dl.prefix_none_at nLt ▸ inIntDef)
    let insGetNth := getNthDl xLt
    let isAt := isAtConst (lane := .defLane) inDefExt insGetNth
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .var x => sorry
  | .null => sorry
  | .pair _ _ => sorry
  | .ir _ _ => sorry
  | .full _ => sorry
  | .compl _ => sorry
  | .arbIr _ => sorry

def allCausesInappElim {dl n fv intCycle expr p}
  (allInapp: AllIntCausesInappIh dl n intCycle fv expr p)
  (intCauseInappIh:
    {x p: _} →
    intCycle x p →
    {intCause: _} →
    intCause.IsWeakCauseFv [] ((dl.prefix n).getDef x) p →
    IntCauseIsInappIh dl n intCycle intCause)
  {extCause: Cause Pair}
  (isCause:
    extCause.IsWeakCause
      (uniSetMapDl.getDef consts.uniSetMap)
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  uniSetMapDl.IsCauseInapplicableExtended
    (extOfIntCycle dl n intCycle)
    extCause
:=
  match expr with
  | .const x =>
    byContradiction fun isApplicable =>
    let isAt := isAtOfInsDef (isCause (extCause.maximalValsApxAreSat))
    let isAtDef :=
      isAtConstElim
        (lane := .defLane)
        isAt
        (fun inCins =>
          byContradiction fun notDef =>
          let out :=
            DefList.Out.isComplete
              (Function.comp
                notDef
                (getNthLaneSwap
                  (laneA := .posLane)
                  (laneB := .defLane)))
          isApplicable (.blockedCinsOut inCins out))
    match allInapp Cause.IsWeakCauseFv.const with
    | .blockedCins ⟨xEq, dEq⟩ inCycle =>
      let allInapp intCause :=
        intCauseInappIh (xEq ▸ dEq ▸ inCycle) (intCause := intCause)
      let isInExtCycle := ⟨rfl, ⟨_, _, _, allInapp _, rfl⟩⟩
      isApplicable (.blockedCinsCycle isAtDef isInExtCycle)
  | .var x => sorry
  | .null => sorry
  | .pair _ _ => sorry
  | .ir _ _ => sorry
  | .full _ => sorry
  | .compl _ => sorry
  | .arbIr _ => sorry
end

mutual
def internalInsElim {dl n x p}
  (ins: (DefList.prefix dl n).Ins x p)
:
  (vals.uniSetMap).defMem (.pair (uniSetMapIndexDef dl n x) p)
:=
  match ins with
  | .intro _ _ _ isCause cinsIns boutOut =>
    internalCauseElim
      isCause
      (DefList.Ins.isSound ∘ cinsIns)
      (fun inCins => internalInsElim (cinsIns inCins))
      (fun inBout => internalOutElim (boutOut inBout))

def internalOutElim {dl n x p}
  (out: (DefList.prefix dl n).Out x p)
:
  ¬ (vals.uniSetMap).posMem (.pair (uniSetMapIndexDef dl n x) p)
:=
  match out with
  | .intro intCycle intCycleIsEmpty inIntCycle =>
    let intCauseInapp {x p}
      (inIntCycle: intCycle x p)
      {intCause: Cause Pair}
      (isCause:
        intCause.IsWeakCauseFv
          []
          ((dl.prefix n).getDef x)
          p)
    :
      IntCauseIsInappIh dl n intCycle intCause
    :=
      match intCycleIsEmpty inIntCycle _ isCause with
      | .blockedCins _ inCins inCycle =>
        .blockedCins inCins inCycle
      | .blockedBout _ inBout ins =>
        .blockedBout inBout (internalInsElim ins)
    let out :=
      DefList.Out.intro3
        (extOfIntCycle dl n intCycle)
        (fun inExtCycle _ isExtCause =>
          let ⟨xEq, ⟨_, _, _, ⟨allInapp, dEq⟩⟩⟩ := inExtCycle
          allCausesInappElim
            allInapp
            intCauseInapp
            (xEq ▸ dEq ▸ isExtCause))
        ⟨rfl, ⟨_, _, _, ⟨intCauseInapp inIntCycle, rfl⟩⟩⟩
    out.isSound
end


def uniSetMapAt_ge
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  expr.triIntp fv (dl.prefix n).wfm ⊑ uniSetMapAt dl n fv expr
:= {
  defLe _ isDef :=
    internalCauseElim
      (Cause.IsStrongCauseFv.ofValDef isDef)
      id
      (internalInsElim ∘ DefList.Ins.isComplete)
      (internalOutElim ∘ DefList.Out.isComplete)
  posLe _ isPos :=
    -- Function.mtr (internalOutElim ∘ DefList.Out.isComplete)
    -- allCausesInappElim sorry
    byContradiction fun notPos => sorry
}
