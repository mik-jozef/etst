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
  vals.uniSetMap.defMem (.pair (uniSetMapIndexDef dl n x) d)

def BoutIh
  (dl: DefList)
  (n: Nat)
  (intCause: Cause Pair)
:
  Prop
:=
  {x d: _} →
  intCause.bout x d →
  ¬ vals.uniSetMap.posMem (.pair (uniSetMapIndexDef dl n x) d)
  

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

/-
  Taking out the largest branch because we're getting timeouts
  at whnf.
-/
def internalCauseElimComplPair {dl n fv left rite p}
  {intCause: Cause Pair}
  (intIsCause:
    intCause.IsStrongCauseFv fv
      (.compl (.pair left rite)) p)
  (ih:
    ∀ pL pR: Pair,
    p = .pair pL pR →
    Or
      (vals.uniSetMap.defMem
        (.pair (uniSetMapIndex dl n fv left.compl) pL))
      (vals.uniSetMap.defMem
        (.pair (uniSetMapIndex dl n fv rite.compl) pR)))
:
  vals.uniSetMap.defMem
    (.pair (uniSetMapIndex dl n fv (.compl (.pair left rite))) p)
  
:=
  let isAt:
    InUniSetMapAt dl n fv usmWfm usmWfm
      (.un .null (.un (.pair left.compl .any) (.pair .any rite.compl)))
      .defLane
      p
  :=
    match p with
    | .null =>
      let atNull:
        (usmWfm consts.uniSetMap).getLane
          .defLane
          ((uniSetMapIndex dl n fv .null).pair .null)
      :=
        InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAtNull)
      isAtUn (Or.inl atNull)
    | .pair pL pR =>
      match ih pL pR rfl with
      | Or.inl ihL =>
        isAtUn
          (Or.inr
            (InWfm.of_in_def_no_fv
              (isInMap
                (isAtUn
                  (Or.inl
                    (InWfm.of_in_def_no_fv
                      (isInMap
                        (isAtPair
                          ihL
                          (InWfm.of_in_def_no_fv
                            (isInMap isAtAny))))))))))
      | Or.inr ihR =>
        isAtUn
          (Or.inr
            (InWfm.of_in_def_no_fv
              (isInMap
                (isAtUn
                  (Or.inr
                    (InWfm.of_in_def_no_fv
                      (isInMap
                        (isAtPair
                          (InWfm.of_in_def_no_fv
                            (isInMap isAtAny))
                          ihR))))))))
  InWfm.of_in_def_no_fv (lane := .defLane) (isInMap (isAt))

def internalCauseElim {dl n fv expr p}
  {intCause: Cause Pair}
  (intIsCause: intCause.IsStrongCauseFv fv expr p)
  (cinsIh: CinsIh dl n intCause)
  (boutIh: BoutIh dl n intCause)
:
  vals.uniSetMap.defMem (.pair (uniSetMapIndex dl n fv expr) p)
:=
  match expr with
  | .const x =>
    let inDefExt := cinsIh intIsCause.constElim
    let xLt: x < n :=
      -- Indentation note: if you ever make your own linter, then not
      -- indenting the function body is good actually, because even
      -- whitespace sensitive parsing would still be unambiguous.
      byContradiction fun nLt =>
      False.elim (notAtDefGeN nLt inDefExt.toPos)
    let insGetNth := getNthDl xLt
    let isAt := isAtConst (lane := .defLane) inDefExt insGetNth
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.const x) =>
    let isAt :=
      isAtComplConst
        (lane := .defLane)
        (fun exprNeq inGetNth => exprNeq (getNthEq inGetNth))
        (boutIh intIsCause.complConstElim)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .var x =>
    let inVar := intIsCause intCause.leastValsApxAreSat
    let xLt: x < fv.length :=
      byContradiction fun nlt => (inVarNope inVar) nlt
    let pEq: fv[x] = p := inVarElimLt inVar xLt
    let isAt := isAtVar (pEq ▸ getNth xLt)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.var x) =>
    let isAt :=
      isAtComplVar
        (fun inGetNth =>
          inComplElim
            (intIsCause intCause.leastValsApxAreSat)
            (inVar (getNthElim inGetNth)))
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
    | .null =>
      let pEq := inNullElim (intIsCause intCause.leastValsApxAreSat)
      pEq ▸ InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAtNull)
  | .compl .null =>
    match p with
    | .null =>
      let inCompl := intIsCause intCause.leastValsApxAreSat
      False.elim (inComplElim inCompl inNull)
    | .pair pL pR =>
      let isAt: InUniSetMapAt dl n fv _ _ (.pair .any .any) _ _ :=
        isAtPair
          (InWfm.of_in_def_no_fv (isInMap isAtAny))
          (InWfm.of_in_def_no_fv (isInMap isAtAny))
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .pair left rite =>
    match p with
    | .null =>
      let isPair := intIsCause intCause.leastValsApxAreSat
      False.elim (inPairElimNope isPair)
    | .pair pL pR =>
      let isCauseL _ _ isSat := (inPairElim (intIsCause isSat)).left
      let isCauseR _ _ isSat := (inPairElim (intIsCause isSat)).right
      let isAt :=
        isAtPair
          (lane := .defLane)
          (internalCauseElim isCauseL cinsIh boutIh)
          (internalCauseElim isCauseR cinsIh boutIh)
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.pair left rite) =>
    internalCauseElimComplPair
      intIsCause
      (fun _ _ eq =>
        match p with
        | .pair _ _ =>
        match intIsCause.complPairElim with
        | Or.inl intIsCauseL =>
          have := complBinLtL left rite
          let eqL := Pair.noConfusion eq fun a b => a
          Or.inl (eqL ▸ internalCauseElim intIsCauseL cinsIh boutIh)
        | Or.inr intIsCauseR =>
          have := complBinLtR left rite
          let eqR := Pair.noConfusion eq fun a b => b
          Or.inr (eqR ▸ internalCauseElim intIsCauseR cinsIh boutIh))
  | .ir left rite =>
    let isCauseL _ _ isSat := (inIrElim (intIsCause isSat)).left
    let isCauseR _ _ isSat := (inIrElim (intIsCause isSat)).right
    let isAt :=
      isAtIr
        (lane := .defLane)
        (internalCauseElim isCauseL cinsIh boutIh)
        (internalCauseElim isCauseR cinsIh boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.ir left rite) =>
    match intIsCause.complIrElim with
    | Or.inl intIsCauseL =>
      have := complBinLtL left rite
      let ih := internalCauseElim intIsCauseL cinsIh boutIh
      let isAt :=
        isAtUn
          (lane := .defLane)
          (Or.inl (internalCauseElim intIsCauseL cinsIh boutIh))
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
    | Or.inr intIsCauseR =>
      have := complBinLtR left rite
      let ih := internalCauseElim intIsCauseR cinsIh boutIh
      let isAt :=
        isAtUn
          (lane := .defLane)
          (Or.inr (internalCauseElim intIsCauseR cinsIh boutIh))
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .full body =>
    let isAt :=
      isAtFull
        (lane := .defLane)
        (fun dB =>
          internalCauseElim
            (fun _ _ isSat => inFullElim (intIsCause isSat) dB)
            cinsIh
            boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.full body) =>
    have := complUnaryLt body
    let ⟨dB, intIsCauseBody⟩ := intIsCause.complFullElim
    let isAt :=
      isAtSome
        (lane := .defLane)
        dB
        (internalCauseElim intIsCauseBody cinsIh boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .arbIr body =>
    let isAt :=
      isAtArbIr
        (lane := .defLane)
        (fun dX =>
          internalCauseElim
            (fun _ _ isSat => inArbIrElim (intIsCause isSat) dX)
            cinsIh
            boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.arbIr body) =>
    have := complUnaryLt body
    let ⟨dX, intIsCauseBody⟩ := intIsCause.complArbIrElim
    let isAt:
      InUniSetMapAt dl n fv uniSetMapDl.wfm uniSetMapDl.wfm body.arbIr.compl Set3.Lane.defLane p
    :=
      isAtArbUn
        (lane := .defLane)
        dX
        (internalCauseElim intIsCauseBody cinsIh boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.compl body) =>
    show
      vals.uniSetMap.defMem ((uniSetMapIndex dl n fv body).pair p)
    from
      internalCauseElim
        intIsCause.complComplElim
        cinsIh
        boutIh
termination_by sizeOf expr

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
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let isAtDef :=
      isAtConstElim
        isAt
        (fun inCins =>
          DefList.Ins.isSound
            (getNthClassical.resolve_right fun out =>
              isApplicable (.blockedCinsOut inCins out)))
    match allInapp Cause.IsWeakCauseFv.const with
    | .blockedCins ⟨xEq, dEq⟩ inCycle =>
      let allInapp intCause :=
        intCauseInappIh (xEq ▸ dEq ▸ inCycle) (intCause := intCause)
      let isInExtCycle := ⟨rfl, ⟨_, _, _, allInapp _, rfl⟩⟩
      isApplicable (.blockedCinsCycle isAtDef isInExtCycle)
  | .compl (.const x) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    
    match allInapp Cause.IsWeakCauseFv.complConst with
    | .blockedBout ⟨xEq, dEq⟩ ins =>
    let ins := xEq ▸ dEq ▸ ins
    
    match isAtComplConstElim isAt with
    | Or.inl inBoutGetNth =>
      if h: x < n then
        let insNth :=
          DefList.Ins.isComplete (getNthDl (lane:=.defLane) h)
        .blockedBout inBoutGetNth.dne insNth
      else
        False.elim (notAtDefGeN h ins.toPos)
    | Or.inr inBout =>
      .blockedBout inBout.dne (DefList.Ins.isComplete ins)
  | .var x =>
    byContradiction fun isApplicable =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let inGetNth := isAtVarElim isAt
    let insGetNth :=
      getNthClassical.resolve_right fun out =>
        isApplicable (.blockedCinsOut inGetNth out)
    let inVar _ _ _ :=
      inVar (getNthElim (lane := .defLane) insGetNth.isSound)
    nomatch allInapp (intCause := Cause.empty) inVar
  | .compl (.var x) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    match getNthClassical with
    | Or.inl ins =>
      .blockedBout (isAtComplVarElim isAt).dne ins
    | Or.inr out =>
      let inComplVar _ _ _ :=
        inCompl fun inVar =>
          let xLt: x < fv.length :=
            byContradiction fun nlt => inVarNope inVar nlt
          let pEq: fv[x] = p := inVarElimLt inVar xLt
          out.isSound (pEq ▸ getNth (lane := .posLane) xLt)
      nomatch allInapp (intCause := Cause.empty) inComplVar
  | .null =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let pEq _ _ _ := isAtNullElim isAt
    nomatch allInapp (intCause := Cause.empty) pEq
  | .compl .null =>
    match p with
    | .null =>
      let isAtAny:
        InUniSetMapAt dl n fv
          extCause.maximalBackgroundApx
          extCause.maximalContextApx
          (.pair .any .any)
          .defLane
          .null
      :=
        isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
      nomatch isAtPairElim isAtAny
    | .pair pL pR =>
      let inComplNull _ _ _ :=
        inCompl fun inNull => inNullElimNope inNull
      nomatch allInapp (intCause := Cause.empty) inComplNull
  | .pair left rite =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨pL, pR, pEq, inCinsLeft, inCinsRite⟩ := isAtPairElim isAt
    if hL: AllIntCausesInappIh dl n intCycle fv left pL then
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hL, rfl⟩⟩
      .blockedCinsCycle inCinsLeft isInExtCycle
    else if hR: AllIntCausesInappIh dl n intCycle fv rite pR then
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hR, rfl⟩⟩
      .blockedCinsCycle inCinsRite isInExtCycle
    else
      let ⟨causeL, isCauseL, isAppL⟩ :=
        hL.toEx fun _ => Classical.not_imp.mp
      let ⟨causeR, isCauseR, isAppR⟩ :=
        hR.toEx fun _ => Classical.not_imp.mp
      let isInappUnion :=
        allInapp
          (pEq ▸ Cause.IsWeakCauseFv.pair isCauseL isCauseR)
      False.elim
        (Cause.IsInapplicable.Not.union isAppL isAppR isInappUnion)
  | .compl (.pair left rite) =>
    let isAt:
      InUniSetMapAt dl n fv
        extCause.maximalBackgroundApx
        extCause.maximalContextApx
        (.un .null (.un (.pair left.compl .any) (.pair .any rite.compl)))
        .posLane
        p
    :=
      isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    match isAtComplIrElim isAt with
    | Or.inl inCinsComplComplNull =>
      let allInappNull:
        AllIntCausesInappIh dl n intCycle fv .null p
      :=
        fun isCauseNull =>
          allInapp fun _ _ isSat =>
            let pEq := inNullElim (isCauseNull isSat)
            pEq ▸ inCompl fun inPair => inPairElimNope inPair
      let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappNull, rfl⟩⟩
      .blockedCinsCycle inCinsComplComplNull isInExtCycle
    | Or.inr inCinsInner =>
      let inner := .un (.pair left.compl .any) (.pair .any rite.compl)
      let allInappInner:
        AllIntCausesInappIh dl n intCycle fv inner p
      :=
        fun isCauseInner =>
          allInapp fun b c isSat inPair =>
            let innerLeft := BasicExpr.toPosLane (.pair left.compl .any)
            let innerRite := BasicExpr.toPosLane (.pair .any rite.compl)
            have isInner: (un innerLeft innerRite).intp2 fv b c p :=
              -- (why tf is by exact needed here?)
              by exact isCauseInner isSat
            match inUnElim (isInner) with
            | .inl inLeft =>
              let ⟨pL, pR, pEq, inComplLeft, _⟩ := inPairElimEx inLeft
              inComplElim inComplLeft (inPairElim (pEq ▸ inPair)).left
            | .inr inRite =>
              let ⟨pL, pR, pEq, _, inComplRite⟩ := inPairElimEx inRite
              inComplElim inComplRite (inPairElim (pEq ▸ inPair)).right
      let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappInner, rfl⟩⟩
      .blockedCinsCycle inCinsInner isInExtCycle
  | .ir left rite =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨inCinsLeft, inCinsRite⟩ := isAtIrElim isAt
    if hL: AllIntCausesInappIh dl n intCycle fv left p then
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hL, rfl⟩⟩
      .blockedCinsCycle inCinsLeft isInExtCycle
    else if hR: AllIntCausesInappIh dl n intCycle fv rite p then
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hR, rfl⟩⟩
      .blockedCinsCycle inCinsRite isInExtCycle
    else
      let ⟨causeL, isCauseL, isAppL⟩ :=
        hL.toEx fun _ => Classical.not_imp.mp
      let ⟨causeR, isCauseR, isAppR⟩ :=
        hR.toEx fun _ => Classical.not_imp.mp
      let isInappUnion :=
        allInapp (Cause.IsWeakCauseFv.ir isCauseL isCauseR)
      False.elim
        (Cause.IsInapplicable.Not.union isAppL isAppR isInappUnion)
  | .compl (.ir left rite) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    match isAtComplIrElim isAt with
    | Or.inl inCinsL =>
      let allInappL:
        AllIntCausesInappIh dl n intCycle fv left.compl p
      :=
        fun isCauseL =>
          let isCauseComplIr _ _ isSat inIr :=
            isCauseL isSat inIr.left
          allInapp isCauseComplIr
      let isInExtCycleL := ⟨rfl, ⟨_, _, _, allInappL, rfl⟩⟩
      .blockedCinsCycle inCinsL isInExtCycleL
    | Or.inr inCinsR =>
      let allInappR: AllIntCausesInappIh dl n intCycle fv rite.compl p :=
        fun isCauseR =>
          let isCauseComplIr _ _ isSat inIr :=
            isCauseR isSat inIr.right
          allInapp isCauseComplIr
      let isInExtCycleR := ⟨rfl, ⟨_, _, _, allInappR, rfl⟩⟩
      .blockedCinsCycle inCinsR isInExtCycleR
  | .full body =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    if h: ∃ dB, AllIntCausesInappIh dl n intCycle fv body dB then
      let ⟨dB, hBody⟩ := h
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hBody, rfl⟩⟩
      .blockedCinsCycle (isAtFullElim isAt dB) isInExtCycle
    else
      let allApplicable :=
        h.toAll fun dB notAllInapp =>
          (notAllInapp.toEx fun _ => Classical.not_imp.mp).unwrap
      let causes := fun dB => (allApplicable dB).val
      let fullIsCause _ _ isSat dB :=
          (allApplicable dB).property.left (isSat.arbUnElim dB)
      False.elim
        (Cause.IsInapplicable.Not.arbUn
          (fun dB => (allApplicable dB).property.right)
          (allInapp fullIsCause))
  | .compl (.full body) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨dB, inCinsBody⟩ := isAtComplFullElim isAt
    let allInappBody:
      AllIntCausesInappIh dl n intCycle fv body.compl dB
    :=
      fun isCauseBody =>
        allInapp fun b c isSat inFull =>
          inComplElim (isCauseBody isSat) (inFullElim inFull dB)
    let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappBody, rfl⟩⟩
    .blockedCinsCycle inCinsBody isInExtCycle
  | .arbIr body =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    if h: ∃ dX, AllIntCausesInappIh dl n intCycle (dX :: fv) body p then
      let ⟨dX, hBody⟩ := h
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hBody, rfl⟩⟩
      .blockedCinsCycle (isAtArbIrElim isAt dX) isInExtCycle
    else
      let allApplicable :=
        h.toAll fun dX notAllInapp =>
          (notAllInapp.toEx fun _ => Classical.not_imp.mp).unwrap
      let causes dX := (allApplicable dX).val
      let arbIrIsCause _ _ isSat dX :=
        (allApplicable dX).property.left (isSat.arbUnElim dX)
      False.elim
        (Cause.IsInapplicable.Not.arbUn
          (fun dX => (allApplicable dX).property.right)
          (allInapp arbIrIsCause))
  | .compl (.arbIr body) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨dX, inCinsBody⟩ := isAtComplArbIrElim isAt
    let allInappBody:
      AllIntCausesInappIh dl n intCycle (dX :: fv) body.compl p
    :=
      fun isCauseBody =>
        allInapp fun b c isSat inArbIr =>
          inComplElim (isCauseBody isSat) (inArbIrElim inArbIr dX)
    let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappBody, rfl⟩⟩
    .blockedCinsCycle inCinsBody isInExtCycle
  | .compl (.compl body) =>
    allCausesInappElim
      (fun isCause => allInapp isCause.complCompl)
      intCauseInappIh
      isCause


mutual
def internalInsElim {dl n x p}
  (ins: (DefList.prefix dl n).Ins x p)
:
  vals.uniSetMap.defMem (.pair (uniSetMapIndexDef dl n x) p)
:=
  match ins with
  | .intro _ _ _ isCause cinsIns boutOut =>
    internalCauseElim
      isCause
      (fun inCins => internalInsElim (cinsIns inCins))
      (fun inBout => internalOutElim (boutOut inBout))

def internalOutElim {dl n x p}
  (out: (DefList.prefix dl n).Out x p)
:
  ¬ vals.uniSetMap.posMem (.pair (uniSetMapIndexDef dl n x) p)
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
      (internalInsElim ∘ DefList.Ins.isComplete)
      (internalOutElim ∘ DefList.Out.isComplete)
  posLe x (isPos: (uniSetMapAt dl n fv expr).posMem x) :=
    byContradiction fun
      (notPos: ¬ (expr.triIntp fv (dl.prefix n).wfm).posMem x)
    =>
      let intCycle: Nat → Set Pair := (dl.prefix n).Out
      let allInapp: AllIntCausesInappIh dl n intCycle fv expr x :=
        fun isCause =>
          match isCause.isInapplicableOfIsNonmember notPos with
          | .blockedCins inCins inCycle =>
            .blockedCins inCins (DefList.Out.isComplete inCycle)
          | .blockedBout inBout isDef =>
            let ins := internalInsElim (DefList.Ins.isComplete isDef)
            .blockedBout inBout ins
      let intCauseInapp
        {x p: _}
        (inIntCycle: intCycle x p)
        {intCause: Cause Pair}
        (isCause: intCause.IsWeakCauseFv [] ((dl.prefix n).getDef x) p)
      :
        IntCauseIsInappIh dl n intCycle intCause
      :=
        match inIntCycle with
        | .intro cycle isEmpty inCycle =>
          match isEmpty inCycle _ isCause with
          | .blockedCins _ inCins inInnerCycle =>
            .blockedCins inCins (.intro cycle isEmpty inInnerCycle)
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
          ⟨rfl, ⟨_, _, _, ⟨allInapp, rfl⟩⟩⟩
      out.nopePos isPos
}
