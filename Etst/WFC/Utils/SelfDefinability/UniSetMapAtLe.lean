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
    And
      (({n fv expr dInt: _} →
        xExt = consts.uniSetMap →
        dExt = .pair (uniSetMapIndex dl n fv expr) dInt →
        ((dl.prefix n).triIntp fv expr).defMem dInt))
      (xExt = consts.getNth → vals.getNth.defMem dExt)

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

def anyCycleNope
  {dl n fv}
  {extCycle: Nat → Set Pair}
  (extIsEmpty:
    ∀ {x d},
      extCycle x d →
      (extCause: Cause Pair) →
      extCause.IsWeakCause (uniSetMapDl.getDef x) d →
      uniSetMapDl.IsCauseInapplicable extCycle extCause)
  {p}
  (inCycleAny:
    extCycle
      consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv .any) p))
  {P: Prop}
:
  P
:=
  match
    extIsEmpty
      inCycleAny
      (causeArbUn dl n fv (.var 0) p p)
      isWeakCauseArbUn
  with
  | .blockedCins _ inCins inCycleVar =>
    let ⟨xEq, dEq⟩ := inCins
    match
      extIsEmpty
        (xEq ▸ dEq ▸ inCycleVar)
        (causeVar (p :: fv) 0 p)
        isWeakCauseVar
    with
    | .blockedCins _ inCins inCycleGetNth =>
      let ⟨xEq, dEqGetNth⟩ := inCins
      let out := DefList.Out.intro extCycle extIsEmpty inCycleGetNth
      let insGetNth :=
        uniSetMapDl.getNth
          (lane := .posLane)
          (Nat.zero_lt_succ _)
      False.elim (out.isSound (xEq ▸ dEqGetNth ▸ insGetNth))

def isInappOfInappUn
  {dl: DefList}
  {cycle: Nat → Set Pair}
  {cause: Cause Pair}
  (isInapp:
    dl.IsCauseInapplicableExtended
      cycle
      (cause.union (Cause.ofValPos dl.wfm Valuation.empty)))
:
  dl.IsCauseInapplicableExtended cycle cause
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
        let inCycle := xEq ▸ dEq ▸ inCycle
        .blockedCinsCycle intIsCause.constElim (Or.inl inCycle)
    else
      .blockedCinsCycle intIsCause.constElim (Or.inr h)
  | .compl (.const x) =>
    let inBout := intIsCause.complConstElim
    match everyCauseInapp inExtCycle _ isWeakCauseComplConst with
    | .blockedBout (Or.inl ⟨enc, neq, xEq, dEq⟩) inDef =>
      let inGetNth := dEq ▸ (inDef.right xEq)
      let encEq :=
        dl.prefixList_at_eq n x ▸
        getNthElimD (lane := .defLane) inGetNth
      False.elim (neq encEq.symm)
    | .blockedBout (Or.inr ⟨xEq, dEq⟩) inDef =>
      let inConst := InWfm.of_in_def_no_fv (inDef.left xEq dEq)
      .blockedBout inBout (DefList.Ins.isComplete inConst)
  | .var x =>
    let inVar := intIsCause intCause.maximalValsApxAreSat
    let xLt: x < fv.length :=
      byContradiction fun nlt => (inVarNope inVar) nlt
    let dEq := inVarElim inVar (List.getElem?_eq_getElem xLt)
    match extIsEmpty inExtCycle (causeVar fv x d) isWeakCauseVar with
    | .blockedCins _ inCins inCycle =>
      let ⟨xEq, dEqGetNth⟩ := inCins
      let out := DefList.Out.intro extCycle extIsEmpty inCycle
      let insGetNth:
        vals.getNth.posMem (getNthEnc fv x d)
      :=
        dEq ▸ uniSetMapDl.getNth (list:=fv) (lane:=.posLane) xLt
      False.elim (out.isSound (xEq ▸ dEqGetNth ▸ insGetNth))
  | .compl (.var x) =>
    let inBout := intIsCause intCause.maximalValsApxAreSat
    match
      extIsEmpty inExtCycle (causeComplVar fv x d) isWeakCauseComplVar
    with
    | .blockedBout _ ⟨xEq, dEq⟩ insGetNth =>
      let inGetNth: (usmWfm consts.getNth).getLane _ _ :=
        xEq ▸ dEq ▸ insGetNth.isSound
      let inVar:
        (var x).intp2 fv (dl.prefix n).wfm (dl.prefix n).wfm d
      :=
        inVar (getNthElim (lane := .defLane) inGetNth)
      False.elim (inBout inVar)
  | .null =>
    let dEq := inNullElim (intIsCause intCause.maximalValsApxAreSat)
    nomatch extIsEmpty inExtCycle Cause.empty (dEq ▸ isWeakCauseNull)
  | .compl .null =>
    match d with
    | .null =>
      let inNullCompl := intIsCause intCause.maximalValsApxAreSat
      False.elim (inComplElim inNullCompl inNull)
    | .pair pL pR =>
      let isExtCause := isWeakCausePair (left := .any) (rite := .any)
      match everyCauseInapp inExtCycle _ isExtCause with
      | .blockedCins (Or.inl ⟨xEq, dEq⟩) inCycle =>
        anyCycleNope extIsEmpty (xEq ▸ dEq ▸ inCycle)
      | .blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
        anyCycleNope extIsEmpty (xEq ▸ dEq ▸ inCycle)
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
        (causeTwoExprs dl n fv left rite pL pR)
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
  | .compl (.pair left rite) =>
    let inner :=
      .un (.pair left.compl .any) (.pair .any rite.compl)
    match d with
    | .null =>
      let inCycleNull :=
        let extIsCause := isWeakCauseUnL .null inner
        match everyCauseInapp inExtCycle _ extIsCause with
        | .blockedCins ⟨xEq, dEq⟩ inCycle =>
          xEq ▸ dEq ▸ inCycle
      
      nomatch extIsEmpty inCycleNull Cause.empty isWeakCauseNull
    | .pair pL pR =>
      let inExtCycleInner :=
        let extIsCause := isWeakCauseUnR .null inner
        match everyCauseInapp inExtCycle _ extIsCause with
        | .blockedCins ⟨xEq, dEq⟩ inCycle =>
          xEq ▸ dEq ▸ inCycle
      
      let inExtCycleL :=
        let inExtCyclePairL :=
          let exprLeft := .pair left.compl .any
          let exprRite := .pair .any rite.compl
          let extIsCause := isWeakCauseUnL exprLeft exprRite
          match everyCauseInapp inExtCycleInner _ extIsCause with
          | .blockedCins ⟨xEq, dEq⟩ inCycle =>
            xEq ▸ dEq ▸ inCycle
        let extIsCause :=
          isWeakCausePair (left := left.compl) (rite := .any)
        match everyCauseInapp inExtCyclePairL _ extIsCause with
        | .blockedCins (Or.inl ⟨xEq, dEq⟩) inCycle =>
          xEq ▸ dEq ▸ inCycle
        | .blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
          anyCycleNope extIsEmpty (xEq ▸ dEq ▸ inCycle)
      
      let inExtCycleR :=
        let inExtCyclePairR :=
          let exprLeft := .pair left.compl .any
          let exprRite := .pair .any rite.compl
          let extIsCause := isWeakCauseUnR exprLeft exprRite
          match everyCauseInapp inExtCycleInner _ extIsCause with
          | .blockedCins ⟨xEq, dEq⟩ inCycle =>
            xEq ▸ dEq ▸ inCycle
        let extIsCause :=
          isWeakCausePair (left := .any) (rite := rite.compl)
        match everyCauseInapp inExtCyclePairR _ extIsCause with
        | .blockedCins (Or.inl ⟨xEq, dEq⟩) inCycle =>
          anyCycleNope extIsEmpty (xEq ▸ dEq ▸ inCycle)
        | .blockedCins (Or.inr ⟨xEq, dEq⟩) inCycle =>
          xEq ▸ dEq ▸ inCycle
      
      match intIsCause.complPairElim (dl.prefix n).wfm .empty with
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
  | .ir left rite =>
    let leftIsCause _ _ isSat :=
      (inIrElim (intIsCause isSat)).left
    let riteIsCause _ _ isSat :=
      (inIrElim (intIsCause isSat)).right
    match extIsEmpty
      inExtCycle
      (causeTwoExprs dl n fv left rite d d)
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
  | .compl (.ir left rite) =>
    let inExtCycleL :=
      let extIsCauseL := isWeakCauseUnL left.compl rite.compl
      match everyCauseInapp inExtCycle _ extIsCauseL with
      | .blockedCins ⟨xEq, dEq⟩ inCycle =>
        xEq ▸ dEq ▸ inCycle
    
    let inExtCycleR :=
      let extIsCauseR := isWeakCauseUnR left.compl rite.compl
      match everyCauseInapp inExtCycle _ extIsCauseR with
      | .blockedCins ⟨xEq, dEq⟩ inCycle =>
        xEq ▸ dEq ▸ inCycle
    
    match intIsCause.complIrElim (dl.prefix n).wfm .empty with
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
  | .full body =>
    match extIsEmpty
      inExtCycle
      (causeFull dl n fv body)
      isWeakCauseFull
    with
    | .blockedCins _ inCins inCycle =>
      let ⟨dB, xEq, dEq⟩ := inCins
      let inCycle := xEq ▸ dEq ▸ inCycle
      let bodyIsCause _ _ isSat := inFullElim (intIsCause isSat) dB
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause bodyIsCause
    | .blockedBout _ inBout _ => inBout.elim
  | .compl (.full body) =>
    match intIsCause.complFullElim (dl.prefix n).wfm .empty with
    | ⟨dB, isCauseBody⟩ =>
      let inExtCycleBody :=
        let extIsCause := isWeakCauseSome (.compl body) dB
        match everyCauseInapp inExtCycle _ extIsCause with
        | .blockedCins ⟨xEq, dEq⟩ inCycle =>
          xEq ▸ dEq ▸ inCycle
      
      have := complUnaryLt body
      isInappOfInappUn
        (allInternalInapp
          extIsEmpty
          everyCauseInapp
          inExtCycleBody
          _
          isCauseBody)
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
  | .compl (.arbIr body) =>
    match intIsCause.complArbIrElim (dl.prefix n).wfm .empty with
    | ⟨dX, isCauseBody⟩ =>
      let inExtCycleBody :=
        let extIsCause := isWeakCauseArbUn (body:=.compl body)
        match everyCauseInapp inExtCycle _ extIsCause with
        | .blockedCins ⟨xEq, dEq⟩ inCycle =>
          xEq ▸ dEq ▸ inCycle
      have := complUnaryLt body
      isInappOfInappUn
        (allInternalInapp
          extIsEmpty
          everyCauseInapp
          inExtCycleBody
          _
          isCauseBody)
  | .compl (.compl body) =>
    let inExtCycleBody:
      extCycle
        consts.uniSetMap
        (.pair (uniSetMapIndex dl n fv body) d)
    :=
      inExtCycle

    allInternalInapp
      extIsEmpty
      everyCauseInapp
      inExtCycleBody
      intCause
      intIsCause.complComplElim


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
    | .const _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let inCins := isAtConstElim insList (DefList.Ins.isSound ∘ cinsSat)
      let ih := externalInsElimHelper (cinsSat inCins) rfl rfl
      InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .compl (.const _) =>
      sorry
    | .var _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ins := (cinsSat (isAtVarElim insList)).isSound
      inVar (b:=.empty) (c:=.empty) (getNthElim (lane := .defLane) ins)
    | .compl (.var _) =>
      sorry
    | .null =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      isAtNullElim insList
    | .compl .null =>
      sorry
    | .pair _ _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨_pL, _pR, eqP, inLeft, inRite⟩ := isAtPairElim insList
      let ihL := externalInsElimHelper (cinsSat inLeft) rfl rfl
      let ihR := externalInsElimHelper (cinsSat inRite) rfl rfl
      eqP ▸ inPair ihL ihR
    | .compl (.ir _ _) =>
      sorry
    | .ir _ _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨inLeft, inRite⟩ := isAtIrElim insList
      let ihL := externalInsElimHelper (cinsSat inLeft) rfl rfl
      let ihR := externalInsElimHelper (cinsSat inRite) rfl rfl
      And.intro ihL ihR
    | .compl (.pair _left _rite) =>
      sorry
    | .full _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      fun dB =>
        externalInsElimHelper (cinsSat (isAtFullElim insList dB)) rfl rfl
    | .compl (.full _) =>
      sorry
    | .arbIr _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      inArbIr fun dX =>
        let insBody := cinsSat (isAtArbIrElim insList dX)
        externalInsElimHelper insBody rfl rfl
    | .compl (.arbIr _) =>
      sorry
    | .compl (.compl _) =>
      sorry

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
        .blockedBout inBout ⟨
          (fun xEq dEq => externalInsElimHelper ins xEq dEq),
          (fun xEq => show (usmWfm consts.getNth).defMem _ from
            xEq ▸ DefList.Ins.isSound ins)
        ⟩
    
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
