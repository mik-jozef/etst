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
  {x p: _} →
  intCause.cins x p →
  vals.uniSetMap.defMem (.pair (uniSetMapIndexDef dl n x) p)

def BoutIh
  (dl: DefList)
  (n: Nat)
  (intCause: Cause Pair)
:
  Prop
:=
  {x p: _} →
  intCause.bout x p →
  ¬ vals.uniSetMap.posMem (.pair (uniSetMapIndexDef dl n x) p)
  

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
    (fun xInt pInt =>
      vals.uniSetMap.defMem
        (.pair (uniSetMapIndexDef dl n xInt) pInt))

def AllIntCausesInappIh
  (dl: DefList)
  (n: Nat)
  (intCycle: Nat → Set Pair)
  (fv: List Pair)
  (expr: BasicExpr)
  (p: Pair)
:=
  ∀ {intCause: Cause Pair},
    intCause.IsWeakCauseFv fv .empty expr p →
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
def internalCauseElimComplProd {dl n fv left rite p}
  {intCause: Cause Pair}
  (intIsCause:
    intCause.IsStrongCauseFv fv .empty
      (.compl (.prod left rite)) p)
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
    (.pair (uniSetMapIndex dl n fv (.compl (.prod left rite))) p)
  
:=
  open DefList in
  let isAt:
    InUniSetMapAt dl n fv usmWfm usmWfm .empty
      (.un .null (.un (.prod left.compl .any) (.prod .any rite.compl)))
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
        InWfm.of_in_def_no_fv (lane := .defLane) (isInMap (isAtNull (o := .empty)))
      isAtUn (Or.inl atNull)
    | .pair pL pR =>
      match ih pL pR rfl with
      | Or.inl ihL =>
        isAtUn
          (Or.inr
            (InWfm.of_in_def_no_fv
              (isInMap
                (isAtUn
                  (o := .empty)
                  (Or.inl
                    (InWfm.of_in_def_no_fv
                      (isInMap
                        (isAtProd
                          (o := .empty)
                          ihL
                          (InWfm.of_in_def_no_fv
                            (isInMap isAtAny))))))))))
      | Or.inr ihR =>
        isAtUn
          (Or.inr
            (InWfm.of_in_def_no_fv
              (isInMap
                (isAtUn
                  (o := .empty)
                  (Or.inr
                    (InWfm.of_in_def_no_fv
                      (isInMap
                        (isAtProd
                          (o := .empty)
                          (InWfm.of_in_def_no_fv
                            (isInMap isAtAny))
                          ihR))))))))
  InWfm.of_in_def_no_fv (lane := .defLane) (isInMap (isAt))

def internalCauseElim {dl n fv expr p}
  {intCause: Cause Pair}
  (intIsCause: intCause.IsStrongCauseFv fv .empty expr p)
  (cinsIh: CinsIh dl n intCause)
  (boutIh: BoutIh dl n intCause)
:
  vals.uniSetMap.defMem (.pair (uniSetMapIndex dl n fv expr) p)
:=
  open DefList in
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
    let isAt := isAtConst (lane := .defLane) (o := .empty) inDefExt insGetNth
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.const x) =>
    let isAt :=
      isAtComplConst
        (lane := .defLane)
        (o := .empty)
        (fun exprNeq inGetNth => exprNeq (getNthEq inGetNth))
        (boutIh intIsCause.complConstElim)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .var x =>
    let inVar := intIsCause intCause.leastValsApxAreSat
    let xLt: x < fv.length :=
      byContradiction fun nlt => (inVarNope inVar) nlt
    let pEq: fv[x] = p := inVarElimLt inVar xLt
    let isAt := isAtVar (o := .empty) (pEq ▸ getNth xLt)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.var x) =>
    let isAt :=
      isAtComplVar
        (o := .empty)
        (fun inGetNth =>
          inComplElim
            (intIsCause intCause.leastValsApxAreSat)
            (inVar (getNthElim inGetNth)))
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
    | .null =>
      let pEq := inNullElim (intIsCause intCause.leastValsApxAreSat)
      pEq ▸ InWfm.of_in_def_no_fv (lane := .defLane) (isInMap (isAtNull (o := .empty)))
  | .compl .null =>
    match p with
    | .null =>
      let inCompl := intIsCause intCause.leastValsApxAreSat
      False.elim (inComplElim inCompl inNull)
    | .pair pL pR =>
      let isAt: InUniSetMapAt dl n fv _ _ .empty (.prod .any .any) _ _ :=
        isAtProd
          (InWfm.of_in_def_no_fv (isInMap isAtAny))
          (InWfm.of_in_def_no_fv (isInMap isAtAny))
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .prod left rite =>
    match p with
    | .null =>
      let isPair := intIsCause intCause.leastValsApxAreSat
      False.elim (inProdElimNope isPair)
    | .pair pL pR =>
      let isCauseL _ _ isSat := (inProdElim (intIsCause isSat)).left
      let isCauseR _ _ isSat := (inProdElim (intIsCause isSat)).right
      let isAt :=
        isAtProd
          (lane := .defLane)
          (o := .empty)
          (internalCauseElim isCauseL cinsIh boutIh)
          (internalCauseElim isCauseR cinsIh boutIh)
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.prod left rite) =>
    internalCauseElimComplProd
      intIsCause
      (fun _ _ eq =>
        match p with
        | .pair _ _ =>
        match intIsCause.complProdElim with
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
        (o := .empty)
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
          (o := .empty)
          (Or.inl (internalCauseElim intIsCauseL cinsIh boutIh))
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
    | Or.inr intIsCauseR =>
      have := complBinLtR left rite
      let ih := internalCauseElim intIsCauseR cinsIh boutIh
      let isAt :=
        isAtUn
          (lane := .defLane)
          (o := .empty)
          (Or.inr (internalCauseElim intIsCauseR cinsIh boutIh))
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .full body =>
    let isAt :=
      isAtFull
        (lane := .defLane)
        (o := .empty)
        (fun pB =>
          internalCauseElim
            (fun _ _ isSat => inFullElim (intIsCause isSat) pB)
            cinsIh
            boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.full body) =>
    have := complUnaryLt body
    let ⟨pB, intIsCauseBody⟩ := intIsCause.complFullElim
    let isAt :=
      isAtSome
        (lane := .defLane)
        (o := .empty)
        pB
        (internalCauseElim intIsCauseBody cinsIh boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .arbIr body =>
    let isAt :=
      isAtArbIr
        (lane := .defLane)
        (o := .empty)
        (fun pX =>
          internalCauseElim
            (fun _ _ isSat => inArbIrElim (intIsCause isSat) pX)
            cinsIh
            boutIh)
    InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAt)
  | .compl (.arbIr body) =>
    have := complUnaryLt body
    let ⟨pX, intIsCauseBody⟩ := intIsCause.complArbIrElim
    let isAt:
      InUniSetMapAt dl n fv usmWfm usmWfm .empty body.arbIr.compl Set3.Lane.defLane p
    :=
      isAtArbUn
        (lane := .defLane)
        pX
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
  | .oracle _ =>
    (intIsCause intCause.leastValsApxAreSat).elim
  | .compl (.oracle _) =>
    show
      vals.uniSetMap.defMem ((uniSetMapIndex dl n fv .any).pair p)
    from
      InWfm.of_in_def_no_fv (lane := .defLane) (isInMap isAtAny)
termination_by sizeOf expr

def allCausesInappElim {dl n fv intCycle expr p}
  (allInapp: AllIntCausesInappIh dl n intCycle fv expr p)
  (intCauseInappIh:
    {x p: _} →
    intCycle x p →
    {intCause: _} →
    intCause.IsWeakCauseFv [] .empty ((dl.prefix n).getDef x) p →
    IntCauseIsInappIh dl n intCycle intCause)
  {extCause: Cause Pair}
  (isCause:
    extCause.IsWeakCause
      .empty
      (uniSetMapDl.getDef consts.uniSetMap)
      (.pair (uniSetMapIndex dl n fv expr) p))
:
  uniSetMapDl.IsCauseInapplicableExtended
    .empty
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
    | .blockedCins ⟨xEq, pEq⟩ inCycle =>
      let allInapp intCause :=
        intCauseInappIh (xEq ▸ pEq ▸ inCycle) (intCause := intCause)
      let isInExtCycle := ⟨rfl, ⟨_, _, _, allInapp _, rfl⟩⟩
      isApplicable (.blockedCinsCycle isAtDef isInExtCycle)
  | .compl (.const x) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    
    match allInapp Cause.IsWeakCauseFv.complConst with
    | .blockedBout ⟨xEq, pEq⟩ ins =>
    let ins := xEq ▸ pEq ▸ ins
    
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
          .empty
          (.prod .any .any)
          .defLane
          .null
      :=
        isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
      nomatch isAtProdElim isAtAny
    | .pair pL pR =>
      let inComplNull _ _ _ :=
        inCompl fun inNull => inNullElimNope inNull
      nomatch allInapp (intCause := Cause.empty) inComplNull
  | .prod left rite =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨pL, pR, pEq, inCinsLeft, inCinsRite⟩ := isAtProdElim isAt
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
          (pEq ▸ Cause.IsWeakCauseFv.prod isCauseL isCauseR)
      False.elim
        (Cause.IsInapplicable.Not.union isAppL isAppR isInappUnion)
  | .compl (.prod left rite) =>
    let isAt:
      InUniSetMapAt dl n fv
        extCause.maximalBackgroundApx
        extCause.maximalContextApx
        .empty
        (.un .null (.un (.prod left.compl .any) (.prod .any rite.compl)))
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
            pEq ▸ inCompl fun inProdNull => inProdElimNope inProdNull
      let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappNull, rfl⟩⟩
      .blockedCinsCycle inCinsComplComplNull isInExtCycle
    | Or.inr inCinsInner =>
      let inner := .un (.prod left.compl .any) (.prod .any rite.compl)
      let allInappInner:
        AllIntCausesInappIh dl n intCycle fv inner p
      :=
        fun isCauseInner =>
          allInapp fun b c isSat inProdP =>
            let innerLeft := BasicExpr.toPosLane (.prod left.compl .any)
            let innerRite := BasicExpr.toPosLane (.prod .any rite.compl)
            have isInner: (un innerLeft innerRite).intp2 fv b c .empty p :=
              -- (why tf is by exact needed here?)
              by exact isCauseInner isSat
            match inUnElim (isInner) with
            | .inl inLeft =>
              let ⟨pL, pR, pEq, inComplLeft, _⟩ := inProdElimEx inLeft
              inComplElim inComplLeft (inProdElim (pEq ▸ inProdP)).left
            | .inr inRite =>
              let ⟨pL, pR, pEq, _, inComplRite⟩ := inProdElimEx inRite
              inComplElim inComplRite (inProdElim (pEq ▸ inProdP)).right
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
    if h: ∃ pB, AllIntCausesInappIh dl n intCycle fv body pB then
      let ⟨pB, hBody⟩ := h
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hBody, rfl⟩⟩
      .blockedCinsCycle (isAtFullElim isAt pB) isInExtCycle
    else
      let allApplicable :=
        h.toAll fun pB notAllInapp =>
          (notAllInapp.toEx fun _ => Classical.not_imp.mp).unwrap
      let causes pB := (allApplicable pB).val
      let fullIsCause _ _ isSat pB :=
          (allApplicable pB).property.left (isSat.arbUnElim pB)
      False.elim
        (Cause.IsInapplicable.Not.arbUn
          (fun pB => (allApplicable pB).property.right)
          (allInapp fullIsCause))
  | .compl (.full body) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨pB, inCinsBody⟩ := isAtComplFullElim isAt
    let allInappBody:
      AllIntCausesInappIh dl n intCycle fv body.compl pB
    :=
      fun isCauseBody =>
        allInapp fun b c isSat inFull =>
          inComplElim (isCauseBody isSat) (inFullElim inFull pB)
    let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappBody, rfl⟩⟩
    .blockedCinsCycle inCinsBody isInExtCycle
  | .arbIr body =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    if h: ∃ pX, AllIntCausesInappIh dl n intCycle (pX :: fv) body p then
      let ⟨pX, hBody⟩ := h
      let isInExtCycle := ⟨rfl, ⟨_, _, _, hBody, rfl⟩⟩
      .blockedCinsCycle (isAtArbIrElim isAt pX) isInExtCycle
    else
      let allApplicable :=
        h.toAll fun pX notAllInapp =>
          (notAllInapp.toEx fun _ => Classical.not_imp.mp).unwrap
      let causes pX := (allApplicable pX).val
      let arbIrIsCause _ _ isSat pX :=
        (allApplicable pX).property.left (isSat.arbUnElim pX)
      False.elim
        (Cause.IsInapplicable.Not.arbUn
          (fun pX => (allApplicable pX).property.right)
          (allInapp arbIrIsCause))
  | .compl (.arbIr body) =>
    let isAt := isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let ⟨pX, inCinsBody⟩ := isAtComplArbIrElim isAt
    let allInappBody:
      AllIntCausesInappIh dl n intCycle (pX :: fv) body.compl p
    :=
      fun isCauseBody =>
        allInapp fun b c isSat inArbIr =>
          inComplElim (isCauseBody isSat) (inArbIrElim inArbIr pX)
    let isInExtCycle := ⟨rfl, ⟨_, _, _, allInappBody, rfl⟩⟩
    .blockedCinsCycle inCinsBody isInExtCycle
  | .compl (.compl body) =>
    allCausesInappElim
      (fun isCause => allInapp isCause.complCompl)
      intCauseInappIh
      isCause
  | .oracle _ =>
    let isAt:
      InUniSetMapAt dl n fv
        extCause.maximalBackgroundApx
        extCause.maximalContextApx
        .empty
        (.arbIr (.compl (.var 0)))
        .defLane
        p
    :=
      isAtOfInsDef (isCause extCause.maximalValsApxAreSat)
    let hBody:
      AllIntCausesInappIh dl n intCycle (p :: fv) (.compl (.var 0)) p
    :=
      fun {intCause} hCause =>
        let inV:
          ((BasicExpr.var 0).toLane Set3.Lane.posLane.toggle).intp2
            (p :: fv)
            intCause.maximalContextApx
            intCause.maximalBackgroundApx
            .empty
            p
        :=
          inVar rfl
        (hCause intCause.maximalValsApxAreSat inV).elim
    let isInExtCycle := ⟨rfl, ⟨_, _, _, hBody, rfl⟩⟩
    .blockedCinsCycle (isAtArbIrElim isAt p) isInExtCycle
  | .compl (.oracle _) =>
    let triv _ _ _ := Set3.empty.nin.def p
    nomatch allInapp (intCause := Cause.empty) triv


mutual
def internalInsElim {dl n x p}
  (ins: (DefList.prefix dl n).Ins .empty x p)
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
  (out: (DefList.prefix dl n).Out .empty x p)
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
          .empty
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
          let ⟨xEq, ⟨_, _, _, ⟨allInapp, pEq⟩⟩⟩ := inExtCycle
          allCausesInappElim
            allInapp
            intCauseInapp
            (xEq ▸ pEq ▸ isExtCause))
        ⟨rfl, ⟨_, _, _, ⟨intCauseInapp inIntCycle, rfl⟩⟩⟩
    out.isSound
end


def uniSetMapAt_ge
  (dl: DefList)
  (n: Nat)
  (fv: List Pair)
  (expr: BasicExpr)
:
  expr.triIntp fv ((dl.prefix n).wfm .empty) .empty ⊑ uniSetMapAt dl n fv expr
:= {
  defLe _ isDef :=
    internalCauseElim
      (Cause.IsStrongCauseFv.ofValDef isDef)
      (internalInsElim ∘ DefList.Ins.isComplete)
      (internalOutElim ∘ DefList.Out.isComplete)
  posLe x (isPos: (uniSetMapAt dl n fv expr).posMem x) :=
    byContradiction fun
      (notPos: ¬ (expr.triIntp fv ((dl.prefix n).wfm .empty) .empty).posMem x)
    =>
      let intCycle: Nat → Set Pair := (dl.prefix n).Out .empty
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
        (isCause: intCause.IsWeakCauseFv [] .empty ((dl.prefix n).getDef x) p)
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
            let ⟨xEq, ⟨_, _, _, ⟨allInapp, pEq⟩⟩⟩ := inExtCycle
            allCausesInappElim
              allInapp
              intCauseInapp
              (xEq ▸ pEq ▸ isExtCause))
          ⟨rfl, ⟨_, _, _, ⟨allInapp, rfl⟩⟩⟩
      out.nopePos isPos
}
