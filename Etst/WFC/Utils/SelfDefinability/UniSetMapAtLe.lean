import Etst.WFC.Utils.MembershipPs.OutIntro3
import Etst.WFC.Utils.SelfDefinability.UniSetMapHelpers

namespace Etst.uniSetMapDl
open SingleLaneExpr


def IsInappExtIh
  (dl: DefList)
  (extCycle: Nat → Set Pair)
  (externalCause: Cause Pair)
:
  Prop
:=
  externalCause.IsInapplicable extCycle fun xExt dExt =>
    {n fv expr dInt: _} →
    xExt = consts.uniSetMap →
    dExt = .pair (uniSetMapIndex dl n fv expr) dInt →
    ((dl.prefix n).triIntp fv expr).defMem dInt

def intOfExtCycle
  (dl: DefList)
  (n: Nat)
  (extCycle: Nat → Set Pair)
  (xInt: Nat)
  (dInt: Pair)
:
  Prop
:=
  Or
    (extCycle
      consts.uniSetMap
      (.pair (uniSetMapIndexDef dl n xInt) dInt))
    (¬ xInt < n)

def allInternalInapp {dl n fv expr d}
  {extCycle: Nat → Set Pair}
  (extIsEmpty:
    ∀ {x d},
      extCycle x d →
      (extCause: Cause Pair) →
      extCause.IsWeakCause (uniSetMapDl.getDef x) d →
      uniSetMapDl.IsCauseInapplicable extCycle extCause)
  (everyCauseInapp:
    ∀ {x d},
      extCycle x d →
      (extCause: Cause Pair) →
      extCause.IsWeakCause (uniSetMapDl.getDef x) d →
      IsInappExtIh dl extCycle extCause)
  (inExtCycle:
    extCycle
      consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) d))
  (intCause : Cause Pair)
  (intIsCause: intCause.IsWeakCauseFv fv expr d)
:
  (dl.prefix n).IsCauseInapplicableExtended
    (intOfExtCycle dl n extCycle)
    intCause
:=
  match expr with
  | .const x =>
    if h: x < n then
      let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseConst
      match isExtInapp with
      | .blockedCins (Or.inl ⟨xEq, dEq⟩) inCycle =>
        let out := DefList.Out.intro extCycle extIsEmpty inCycle
        let insGetNth :=
          uniSetMapDl.getNthDl (lane:=.posLane) h
        False.elim (out.isSound (xEq ▸ dEq ▸ insGetNth))
      | .blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
        let inCycle:
          extCycle
            consts.uniSetMap
            (.pair (uniSetMapIndexDef dl n x) d)
        :=
          xEq ▸ dEq ▸ inCycle
        .blockedCinsCycle intIsCause.constElim (Or.inl inCycle)
    else
      .blockedCinsCycle intIsCause.constElim (Or.inr h)
  | .var x =>
    let inVar := intIsCause intCause.maximalValsApxAreSat
    let xLt: x < fv.length :=
      byContradiction fun nlt => inVarNope inVar nlt
    let dEq := inVarElim inVar (List.getElem?_eq_getElem xLt)
    match extIsEmpty inExtCycle (causeVar fv x d) isWeakCauseVar with
    | .blockedCins _ inCins inCycle =>
      let ⟨xEq, dEqGetNth⟩ := inCins
      let out := DefList.Out.intro extCycle extIsEmpty inCycle
      let insGetNth:
        (uniSetMapDl.wfm consts.getNth).posMem (getNthEnc fv x d)
      :=
        dEq ▸ uniSetMapDl.getNth (list:=fv) (i:=x) (lane:=.posLane) xLt
      False.elim (out.isSound (xEq ▸ dEqGetNth ▸ insGetNth))
    | .blockedBout _ inBout _ => inBout.elim
  | .null =>
    let dEq := inNullElim (intIsCause intCause.maximalValsApxAreSat)
    nomatch extIsEmpty inExtCycle causeNull (dEq ▸ isWeakCauseNull)
  | .pair left rite =>
    match d with
    | .null =>
      inPairElimNope (intIsCause intCause.maximalValsApxAreSat)
    | .pair pL pR =>
      let leftIsCause _ _ isSat :=
        (inPairElim (intIsCause isSat)).left
      let riteIsCause _ _ isSat :=
        (inPairElim (intIsCause isSat)).right
      match extIsEmpty
        inExtCycle
        (causePair dl n fv left rite pL pR)
        isWeakCausePair
      with
      | .blockedCins _ (Or.inl ⟨xEq, dEq⟩) inCycle =>
        let inCycle := xEq ▸ dEq ▸ inCycle
        allInternalInapp
          extIsEmpty everyCauseInapp inCycle intCause leftIsCause
      | .blockedCins _ (Or.inr ⟨xEq, dEq⟩) inCycle =>
        let inCycle := xEq ▸ dEq ▸ inCycle
        allInternalInapp
          extIsEmpty everyCauseInapp inCycle intCause riteIsCause
      | .blockedBout _ inBout _ => inBout.elim
  | .ir left rite =>
    let leftIsCause _ _ isSat :=
      (inIrElim (intIsCause isSat)).left
    let riteIsCause _ _ isSat :=
      (inIrElim (intIsCause isSat)).right
    match extIsEmpty
      inExtCycle
      (causeIr dl n fv left rite d)
      isWeakCauseIr
    with
    | .blockedCins _ (Or.inl ⟨xEq, dEq⟩) inCycle =>
      let inCycle := xEq ▸ dEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause leftIsCause
    | .blockedCins _ (Or.inr ⟨xEq, dEq⟩) inCycle =>
      let inCycle := xEq ▸ dEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause riteIsCause
    | .blockedBout _ inBout _ => inBout.elim
  | .full body =>
    let bodyIsCause dB _ _ isSat :=
      inFullElim (intIsCause isSat) dB
    match extIsEmpty
      inExtCycle
      (causeFull dl n fv body)
      isWeakCauseFull
    with
    | .blockedCins _ inCins inCycle =>
      let ⟨dB, xEq, dEq⟩ := inCins
      let inCycle := xEq ▸ dEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause (bodyIsCause dB)
    | .blockedBout _ inBout _ => inBout.elim
  -- | .compl _ =>
  --   let isExtInapp := everyCauseInapp inExtCycle _ isWeakCauseCompl
  --   match isExtInapp with
  --   | .blockedBout ⟨xEq, dEq⟩ isDefFn =>
  --     let isDef := not_not_intro (isDefFn xEq dEq)
  --     let isInapp := intIsCause.isInapplicableOfIsNonmember isDef
  --     match isInapp with
  --     | .blockedCins inCins notPos =>
  --       .blockedCinsOut inCins (DefList.Out.isComplete notPos)
  --     | .blockedBout inBout isDef =>
  --       .blockedBout inBout (DefList.Ins.isComplete isDef)
  | .compl (.const x) =>
    sorry
  | .compl (.var x) =>
    sorry
  | .compl (.null) =>
    sorry
  | .compl (.pair left rite) =>
    sorry
  | .compl (.ir left rite) =>
    let extIsCauseL :=
      isWeakCauseUnL (left:=left.compl) (rite:=rite.compl)
    let inExtCycleL :=
      match everyCauseInapp inExtCycle _ extIsCauseL with
      | .blockedCins ⟨xEq, dEq⟩ inCycle =>
        xEq ▸ dEq ▸ inCycle
    
    let extIsCauseR :=
      isWeakCauseUnR (left:=left.compl) (rite:=rite.compl)
    let inExtCycleR :=
      match everyCauseInapp inExtCycle _ extIsCauseR with
      | .blockedCins ⟨xEq, dEq⟩ inCycle =>
        xEq ▸ dEq ▸ inCycle
    
    let intWfm := (dl.prefix n).wfm
    let isInappOfInappUn
      {cause: Cause Pair}
      (isInapp:
        (dl.prefix n).IsCauseInapplicableExtended
          (intOfExtCycle dl n extCycle)
          (cause.union (Cause.ofValPos intWfm Valuation.empty)))
    :
      (dl.prefix n).IsCauseInapplicableExtended
        (intOfExtCycle dl n extCycle)
        cause
    :=
      match isInapp with
      | .blockedCinsCycle (Or.inl inCins) inCycle =>
        .blockedCinsCycle inCins inCycle
      | .blockedCinsOut (Or.inl inCins) isOut =>
        .blockedCinsOut inCins isOut
      | .blockedBout (Or.inl inBout) isIns =>
        .blockedBout inBout isIns
      | .blockedBout (Or.inr inBout) isIns =>
        isIns.nopeNotDef inBout
    
    match intIsCause.complIrElim intWfm Valuation.empty with
    | Or.inl isCauseL =>
      have := complBinLtL left rite
      isInappOfInappUn
        (allInternalInapp
          extIsEmpty
          everyCauseInapp
          inExtCycleL
          _
          isCauseL)
    | Or.inr isCauseR =>
      have := complBinLtR left rite
      isInappOfInappUn
        (allInternalInapp
          extIsEmpty
          everyCauseInapp
          inExtCycleR
          _
          isCauseR)
  | .compl (.full body) =>
    sorry
  | .compl (.compl body) =>
    sorry
  | .compl (.arbIr body) =>
    sorry
  | .arbIr body =>
    let bodyIsCause dX _ _ isSat :=
      inArbIrElim (intIsCause isSat) dX
    match extIsEmpty
      inExtCycle
      (causeArbIr dl n fv body d)
      isWeakCauseArbIr
    with
    | .blockedCins _ inCins inCycle =>
      let ⟨dX, xEq, dEq⟩ := inCins
      let inCycle := xEq ▸ dEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause (bodyIsCause dX)
    | .blockedBout _ inBout _ => inBout.elim

termination_by sizeOf expr

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
  (cstEq: cst = consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
:
(expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  match ins with
  | .intro _ _ cause isCause cinsSat boutSat =>
    let ins := isCause cause.leastValsApxAreSat
    -- TODO Lean, why can't I call `isAtOfInsDef` once before the match?
    let IsAt :=
      InUniSetMapAt dl n fv cause.leastBackgroundApx cause.leastContextApx
    match expr with
    | .const _x =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let inCins := isAtConstElim insList (DefList.Ins.isSound ∘ cinsSat)
      let ih := externalInsElimHelper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .var _x =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      isAtVarElim insList cinsSat
    | .null =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      isAtNullElim insList
    | .pair _left _rite =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨_pL, _pR, eqP, inLeft, inRite⟩ := isAtPairElim insList
      let ihL := externalInsElimHelper (cinsSat inLeft) rfl rfl
      let ihR := externalInsElimHelper (cinsSat inRite) rfl rfl
      eqP ▸ inPair ihL ihR
    | .ir _left _rite =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨inLeft, inRite⟩ := isAtIrElim insList
      let ihL := externalInsElimHelper (cinsSat inLeft) rfl rfl
      let ihR := externalInsElimHelper (cinsSat inRite) rfl rfl
      And.intro ihL ihR
    | .full _body =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      fun dB =>
        externalInsElimHelper (cinsSat (isAtFullElim insList dB)) rfl rfl
    | .compl _ =>
      -- let insList: IsAt _ .defLane p :=
      --   isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      -- let inBout := boutSat (isAtComplElim insList).dne
      -- externalOutElimHelper inBout rfl rfl
      sorry
    | .arbIr _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      inArbIr fun dX =>
        let insBody := cinsSat (isAtArbIrElim insList dX)
        externalInsElimHelper insBody rfl rfl

def externalOutElimHelper {dl n fv index cst expr p}
  (out: uniSetMapDl.Out cst index)
  (cstEq: cst = consts.uniSetMap)
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
              fun _ isCause =>
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
      consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  externalInsElimHelper ins rfl rfl

def externalOutElim {dl n fv expr p}
  (out:
    uniSetMapDl.Out
      consts.uniSetMap
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
