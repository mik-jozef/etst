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
  externalCause.IsInapplicable extCycle fun xExt pExt =>
    And
      (({n fv expr pInt: _} →
        xExt = consts.uniSetMap →
        pExt = .pair (uniSetMapIndex dl n fv expr) pInt →
        ((dl.prefix n).triIntp fv expr).defMem pInt))
      (xExt = consts.getNth → vals.getNth.defMem pExt)

def intOfExtCycle
  (dl: DefList)
  (n: Nat)
  (extCycle: Nat → Set Pair)
  (xInt: Nat)
  (pInt: Pair)
:
  Prop
:=
  Or
    (extCycle
      consts.uniSetMap
      (.pair (uniSetMapIndexDef dl n xInt) pInt))
    (¬ xInt < n)

def anyCycleNope
  {dl n fv}
  {extCycle: Nat → Set Pair}
  (extIsEmpty:
    ∀ {x p},
      extCycle x p →
      (extCause: Cause Pair) →
      extCause.IsWeakCause (uniSetMapDl.getDef x) p →
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
    let ⟨xEq, pEq⟩ := inCins
    match
      extIsEmpty
        (xEq ▸ pEq ▸ inCycleVar)
        (causeVar (p :: fv) 0 p)
        isWeakCauseVar
    with
    | .blockedCins _ inCins inCycleGetNth =>
      let ⟨xEq, pEqGetNth⟩ := inCins
      let out := DefList.Out.intro extCycle extIsEmpty inCycleGetNth
      let insGetNth :=
        uniSetMapDl.getNth
          (lane := .posLane)
          (Nat.zero_lt_succ _)
      False.elim (out.isSound (xEq ▸ pEqGetNth ▸ insGetNth))

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


def allInternalInapp {dl n fv expr p}
  {extCycle: Nat → Set Pair}
  (extIsEmpty:
    ∀ {x p},
      extCycle x p →
      (extCause: Cause Pair) →
      extCause.IsWeakCause (uniSetMapDl.getDef x) p →
      uniSetMapDl.IsCauseInapplicable extCycle extCause)
  (everyCauseInapp:
    ∀ {x p},
      extCycle x p →
      (extCause: Cause Pair) →
      extCause.IsWeakCause (uniSetMapDl.getDef x) p →
      IsInappExtIh dl extCycle extCause)
  (inExtCycle:
    extCycle
      consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
  (intCause : Cause Pair)
  (intIsCause: intCause.IsWeakCauseFv fv expr p)
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
      | .blockedCins (Or.inl ⟨xEq, pEq⟩) inCycle =>
        let out := DefList.Out.intro extCycle extIsEmpty inCycle
        let insGetNth :=
          uniSetMapDl.getNthDl (lane:=.posLane) h
        False.elim (out.isSound (xEq ▸ pEq ▸ insGetNth))
      | .blockedCins (Or.inr ⟨xEq, pEq⟩) inCycle =>
        let inCycle := xEq ▸ pEq ▸ inCycle
        .blockedCinsCycle intIsCause.constElim (Or.inl inCycle)
    else
      .blockedCinsCycle intIsCause.constElim (Or.inr h)
  | .compl (.const x) =>
    let inBout := intIsCause.complConstElim
    match everyCauseInapp inExtCycle _ isWeakCauseComplConst with
    | .blockedBout (Or.inl ⟨enc, neq, xEq, pEq⟩) inDef =>
      let inGetNth := pEq ▸ (inDef.right xEq)
      let encEq :=
        dl.prefixList_at_eq n x ▸
        getNthElimD (lane := .defLane) inGetNth
      False.elim (neq encEq.symm)
    | .blockedBout (Or.inr ⟨xEq, pEq⟩) inDef =>
      let inConst := DefList.InWfm.of_in_def_no_fv (inDef.left xEq pEq)
      .blockedBout inBout (DefList.Ins.isComplete inConst)
  | .var x =>
    let inVar := intIsCause intCause.maximalValsApxAreSat
    let xLt: x < fv.length :=
      byContradiction fun nlt => (inVarNope inVar) nlt
    let pEq := inVarElim inVar (List.getElem?_eq_getElem xLt)
    match extIsEmpty inExtCycle (causeVar fv x p) isWeakCauseVar with
    | .blockedCins _ inCins inCycle =>
      let ⟨xEq, pEqGetNth⟩ := inCins
      let out := DefList.Out.intro extCycle extIsEmpty inCycle
      let insGetNth:
        vals.getNth.posMem (getNthEnc fv x p)
      :=
        pEq ▸ uniSetMapDl.getNth (list:=fv) (lane:=.posLane) xLt
      False.elim (out.isSound (xEq ▸ pEqGetNth ▸ insGetNth))
  | .compl (.var x) =>
    let inBout := intIsCause intCause.maximalValsApxAreSat
    match
      extIsEmpty inExtCycle (causeComplVar fv x p) isWeakCauseComplVar
    with
    | .blockedBout _ ⟨xEq, pEq⟩ insGetNth =>
      let inGetNth: (usmWfm consts.getNth).getLane _ _ :=
        xEq ▸ pEq ▸ insGetNth.isSound
      let inVar:
        (var x).intp2 fv (dl.prefix n).wfm (dl.prefix n).wfm p
      :=
        inVar (getNthElim (lane := .defLane) inGetNth)
      False.elim (inBout inVar)
  | .null =>
    let pEq := inNullElim (intIsCause intCause.maximalValsApxAreSat)
    nomatch extIsEmpty inExtCycle Cause.empty (pEq ▸ isWeakCauseNull)
  | .compl .null =>
    match p with
    | .null =>
      let inNullCompl := intIsCause intCause.maximalValsApxAreSat
      False.elim (inComplElim inNullCompl inNull)
    | .pair pL pR =>
      let isExtCause := isWeakCausePair (left := .any) (rite := .any)
      match everyCauseInapp inExtCycle _ isExtCause with
      | .blockedCins (Or.inl ⟨xEq, pEq⟩) inCycle =>
        anyCycleNope extIsEmpty (xEq ▸ pEq ▸ inCycle)
      | .blockedCins (Or.inr ⟨xEq, pEq⟩) inCycle =>
        anyCycleNope extIsEmpty (xEq ▸ pEq ▸ inCycle)
  | .pair left rite =>
    match p with
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
      | .blockedCins _ (Or.inl ⟨xEq, pEq⟩) inCycle =>
        let inCycle := xEq ▸ pEq ▸ inCycle
        allInternalInapp
          extIsEmpty everyCauseInapp inCycle intCause leftIsCause
      | .blockedCins _ (Or.inr ⟨xEq, pEq⟩) inCycle =>
        let inCycle := xEq ▸ pEq ▸ inCycle
        allInternalInapp
          extIsEmpty everyCauseInapp inCycle intCause riteIsCause
  | .compl (.pair left rite) =>
    let inner :=
      .un (.pair left.compl .any) (.pair .any rite.compl)
    match p with
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
          | .blockedCins ⟨xEq, pEq⟩ inCycle =>
            xEq ▸ pEq ▸ inCycle
        let extIsCause :=
          isWeakCausePair (left := left.compl) (rite := .any)
        match everyCauseInapp inExtCyclePairL _ extIsCause with
        | .blockedCins (Or.inl ⟨xEq, pEq⟩) inCycle =>
          xEq ▸ pEq ▸ inCycle
        | .blockedCins (Or.inr ⟨xEq, pEq⟩) inCycle =>
          anyCycleNope extIsEmpty (xEq ▸ pEq ▸ inCycle)
      
      let inExtCycleR :=
        let inExtCyclePairR :=
          let exprLeft := .pair left.compl .any
          let exprRite := .pair .any rite.compl
          let extIsCause := isWeakCauseUnR exprLeft exprRite
          match everyCauseInapp inExtCycleInner _ extIsCause with
          | .blockedCins ⟨xEq, pEq⟩ inCycle =>
            xEq ▸ pEq ▸ inCycle
        let extIsCause :=
          isWeakCausePair (left := .any) (rite := rite.compl)
        match everyCauseInapp inExtCyclePairR _ extIsCause with
        | .blockedCins (Or.inl ⟨xEq, pEq⟩) inCycle =>
          anyCycleNope extIsEmpty (xEq ▸ pEq ▸ inCycle)
        | .blockedCins (Or.inr ⟨xEq, pEq⟩) inCycle =>
          xEq ▸ pEq ▸ inCycle
      
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
      (causeTwoExprs dl n fv left rite p p)
      isWeakCauseIr
    with
    | .blockedCins _ (Or.inl ⟨xEq, pEq⟩) inCycle =>
      let inCycle := xEq ▸ pEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause leftIsCause
    | .blockedCins _ (Or.inr ⟨xEq, pEq⟩) inCycle =>
      let inCycle := xEq ▸ pEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause riteIsCause
  | .compl (.ir left rite) =>
    let inExtCycleL :=
      let extIsCauseL := isWeakCauseUnL left.compl rite.compl
      match everyCauseInapp inExtCycle _ extIsCauseL with
      | .blockedCins ⟨xEq, pEq⟩ inCycle =>
        xEq ▸ pEq ▸ inCycle
    
    let inExtCycleR :=
      let extIsCauseR := isWeakCauseUnR left.compl rite.compl
      match everyCauseInapp inExtCycle _ extIsCauseR with
      | .blockedCins ⟨xEq, pEq⟩ inCycle =>
        xEq ▸ pEq ▸ inCycle
    
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
      let ⟨pB, xEq, pEq⟩ := inCins
      let inCycle := xEq ▸ pEq ▸ inCycle
      let bodyIsCause _ _ isSat := inFullElim (intIsCause isSat) pB
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause bodyIsCause
    | .blockedBout _ inBout _ => inBout.elim
  | .compl (.full body) =>
    match intIsCause.complFullElim (dl.prefix n).wfm .empty with
    | ⟨pB, isCauseBody⟩ =>
      let inExtCycleBody :=
        let extIsCause := isWeakCauseSome (.compl body) pB
        match everyCauseInapp inExtCycle _ extIsCause with
        | .blockedCins ⟨xEq, pEq⟩ inCycle =>
          xEq ▸ pEq ▸ inCycle
      
      have := complUnaryLt body
      isInappOfInappUn
        (allInternalInapp
          extIsEmpty
          everyCauseInapp
          inExtCycleBody
          _
          isCauseBody)
  | .arbIr body =>
    let bodyIsCause pX _ _ isSat :=
      inArbIrElim (intIsCause isSat) pX
    match extIsEmpty
      inExtCycle
      (causeArbIr dl n fv body p)
      isWeakCauseArbIr
    with
    | .blockedCins _ inCins inCycle =>
      let ⟨pX, xEq, pEq⟩ := inCins
      let inCycle := xEq ▸ pEq ▸ inCycle
      allInternalInapp
        extIsEmpty everyCauseInapp inCycle intCause (bodyIsCause pX)
    | .blockedBout _ inBout _ => inBout.elim
  | .compl (.arbIr body) =>
    match intIsCause.complArbIrElim (dl.prefix n).wfm .empty with
    | ⟨pX, isCauseBody⟩ =>
      let inExtCycleBody :=
        let extIsCause := isWeakCauseArbUn (body:=.compl body)
        match everyCauseInapp inExtCycle _ extIsCause with
        | .blockedCins ⟨xEq, pEq⟩ inCycle =>
          xEq ▸ pEq ▸ inCycle
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
        (.pair (uniSetMapIndex dl n fv body) p)
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
mutual
def externalInsElimHelper {dl n fv index cst expr p}
  (ins: uniSetMapDl.Ins cst index)
  (cstEq: cst = consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  (isNnf: expr.IsNnf)
:
(expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  match ins with
  | .intro _ _ cause isCause cinsSat boutSat =>
    let InCins expr fv p :=
      cause.cins
        consts.uniSetMap
        ((uniSetMapIndex dl n fv expr).pair p)
    let inCinsCcElim {expr fv p} (inCins: InCins expr.compl.compl fv p):
      InCins expr fv p
    :=
      inCins
    let inCinsNnf {expr fv p} (inCins: InCins expr fv p):
      InCins expr.toNnf fv p
    := by
      unfold InCins
      exact uniSetMapIndex_nnf_eq ▸ inCins
    
    let ins := isCause cause.leastValsApxAreSat
    -- TODO Lean, why can't I call `isAtOfInsDef` once before the match?
    let IsAt :=
      InUniSetMapAt dl n fv cause.leastBackgroundApx cause.leastContextApx
    match expr, isNnf with
    | .const x, _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let inCins := isAtConstElim insList (DefList.Ins.isSound ∘ cinsSat)
      let insDef := cinsSat (inCinsNnf inCins)
      let ih: (BasicExpr.triIntp _ _ _).defMem _ :=
        BasicExpr.triIntp_toNnf_eq _ _ _ ▸
        externalInsElimHelper insDef rfl rfl (Expr.toNnf_isNnf _)
      DefList.InWfm.of_in_def_no_fv (lane := .defLane) ih
    | .compl (.const x), _ =>
      let insList := isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      fun inConst =>
      match isAtComplConstElim insList with
      | Or.inl inBoutGetNth =>
        if h: x < n then
          False.elim
            ((boutSat inBoutGetNth.dne).isSound
              (getNthDl (lane := .posLane) h))
        else
          let inNone :=
            DefList.prefix_none_at h ▸
            DefList.InWfm.in_def_no_fv (lane := .posLane) inConst
          ninNone inNone
      | Or.inr inBout =>
        let df := (dl.prefix n).getDef x
        let out:
          uniSetMapDl.Out
            consts.uniSetMap
            ((uniSetMapIndex dl n [] df.toNnf).pair p)
        :=
          boutSat (uniSetMapIndex_nnf_eq ▸ inBout.dne)
        externalOutElimHelper
          out
          rfl
          rfl
          df.toNnf_isNnf
          ((BasicExpr.triIntp_toNnf_eq _ _ _).symm ▸
          DefList.InWfm.in_def_no_fv (lane := .posLane) inConst)
    | .var _, _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ins := (cinsSat (isAtVarElim insList)).isSound
      inVar (b:=.empty) (c:=.empty) (getNthElim (lane := .defLane) ins)
    | .compl (.var x), _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      inCompl fun inVar =>
        let xLt: x < fv.length :=
          byContradiction fun nlt => (inVarNope inVar) nlt
        let pEq: fv[x] = p := inVarElimLt inVar xLt
        let out := boutSat (isAtComplVarElim insList).dne
        out.isSound (pEq ▸ uniSetMapDl.getNth (lane:=.posLane) xLt)
    | .null, _ =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      isAtNullElim insList
    | .pair _ _, .pair nnfL nnfR =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨_pL, _pR, eqP, inLeft, inRite⟩ := isAtPairElim insList
      let ihL := externalInsElimHelper (cinsSat inLeft) rfl rfl nnfL
      let ihR := externalInsElimHelper (cinsSat inRite) rfl rfl nnfR
      eqP ▸ inPair ihL ihR
    | .un left rite, .un nnfL nnfR =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      match isAtComplIrElim insList with
      | Or.inl inLeftCc =>
        let inLeft := inCinsCcElim inLeftCc
        inUnL (externalInsElimHelper (cinsSat inLeft) rfl rfl nnfL)
      | Or.inr inRiteCc =>
        let inRite := inCinsCcElim inRiteCc
        inUnR (externalInsElimHelper (cinsSat inRite) rfl rfl nnfR)
    | .ir _ _, .ir nnfL nnfR =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨inLeft, inRite⟩ := isAtIrElim insList
      let ihL := externalInsElimHelper (cinsSat inLeft) rfl rfl nnfL
      let ihR := externalInsElimHelper (cinsSat inRite) rfl rfl nnfR
      inIr ihL ihR
    | .full _, .full nnfB =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      fun pB =>
        externalInsElimHelper
          (cinsSat (isAtFullElim insList pB))
          rfl
          rfl
          nnfB
    | .some body, .some nnfB =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨pB, inBodyCc⟩ := isAtComplFullElim insList
      let inBody := inCinsCcElim inBodyCc
      inSome _ (externalInsElimHelper (cinsSat inBody) rfl rfl nnfB)
    | .arbIr _, .arbIr nnfB =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      inArbIr fun pX =>
        let insBody := cinsSat (isAtArbIrElim insList pX)
        externalInsElimHelper insBody rfl rfl nnfB
    | .arbUn body, .arbUn nnfB =>
      let insList: IsAt _ .defLane p :=
        isAtOfInsDef (cstEq ▸ indexEq ▸ ins)
      let ⟨pX, inBodyCc⟩ := isAtComplArbIrElim insList
      let inBody := inCinsCcElim inBodyCc
      inArbUn pX (externalInsElimHelper (cinsSat inBody) rfl rfl nnfB)

def externalOutElimHelper {dl n fv index cst expr p}
  (out: uniSetMapDl.Out cst index)
  (cstEq: cst = consts.uniSetMap)
  (indexEq: index = .pair (uniSetMapIndex dl n fv expr) p)
  -- Note: allInternalInapp could be optimized with this to remove
  -- some of the branches. But since it already works... ¯\_(ツ)_/¯
  (_isNnf: expr.IsNnf)
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  match out with
  | .intro extCycle extIsEmpty inExtCycle =>
    let everyCauseInapp {x p}
      (inCycle: extCycle x p)
      {cause}
      (isCause: cause.IsWeakCause (uniSetMapDl.getDef x) p)
    :
      IsInappExtIh dl extCycle cause
    :=
      match extIsEmpty inCycle cause isCause with
      | .blockedCins _ inCins inCycle =>
        .blockedCins inCins inCycle
      | .blockedBout _ inBout ins =>
        .blockedBout inBout ⟨
          (fun {_ _ expr _} xEq dEq =>
            show (expr.triIntp _ _).defMem _ from
            (expr.triIntp_toNnf_eq _ _).symm ▸
            externalInsElimHelper
              ins
              xEq
              (uniSetMapIndex_nnf_eq ▸ dEq)
              expr.toNnf_isNnf),
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
end


def externalInsElim {dl n fv expr p}
  (insExt:
    uniSetMapDl.Ins
      consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  (expr.triIntp fv (dl.prefix n).wfm).defMem p
:=
  expr.triIntp_toNnf_eq fv _ ▸
  externalInsElimHelper
    (uniSetMapIndex_nnf_eq ▸ insExt)
    rfl
    rfl
    expr.toNnf_isNnf

def externalOutElim {dl n fv expr p}
  (outExt:
    uniSetMapDl.Out
      consts.uniSetMap
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem p
:=
  expr.triIntp_toNnf_eq fv _ ▸
  externalOutElimHelper
      (uniSetMapIndex_nnf_eq ▸ outExt)
      rfl
      rfl
      expr.toNnf_isNnf

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
