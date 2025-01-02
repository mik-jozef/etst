import WFC.Ch6_S1_AProofSystem

/-
  A convenience helper type for `Out.intro4` below. Includes support
  for bound variables in case one needs to account for them.
-/
inductive IsCauseInappExtended
  (salg: Salgebra sig)
  (dl: DefList Var sig)
  (cycle: Set (ValVar Var salg.D))
  (cause: Cause Var salg.D)
:
  Prop
|
  cinsFailsCycle
  {d x}
  (inCins: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  IsCauseInappExtended salg dl cycle cause
|
  cinsFailsOut
  {d x}
  (inCins: ⟨d, x⟩ ∈ cause.contextIns)
  (isOut: Out salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause
|
  binsFails
  {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: Out salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause
|
  boutFails
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: Ins salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause


/-
  A convenience constructor that allows smaller cycles to be used,
  by allowing the empty cycle to also depend through context on a
  non-cycle element as long as that element is provably out.
  
  Without this option, the cycle would have to recursively include
  all such elements.
  
  TODO consider:
  There is one more thing that probably could (ought?) be done to
  make the proof system more convenient to use: the
  `Is[Strongly|Weakly]SatisfiedBy` predicates could be made to
  only consider valuations that are models of the definition list.
  This would make the proofs easier to construct, but destructing
  them would give less information.
-/
def Out.intro4
  {salg: Salgebra sig}
  {dl: DefList Var sig}
  (cycle: Set (ValVar Var salg.D))
  (isEmptyCycle:
    ∀ {d x},
    ⟨d, x⟩ ∈ cycle →
    (cause: Cause Var salg.D) →
    IsWeakCause salg cause d (dl.getDef x) →
    IsCauseInappExtended salg dl cycle cause)
  {d x}
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  Out salg dl d x
:=
  let largeCycle vv :=
    vv ∈ cycle ∨
    vv.d ∉ (dl.wellFoundedModel salg vv.x).posMem
  
  open IsCauseInapplicable in
  open IsCauseInappExtended in
  Out.intro
    largeCycle
    (fun inLargeCycle cause isCause =>
      inLargeCycle.elim
        (fun inCycle =>
          let isInappExtended := isEmptyCycle inCycle cause isCause
          match isInappExtended with
          | cinsFailsOut inCins isOut =>
            blockedContextIns cause inCins (Or.inr isOut.isSound)
          | cinsFailsCycle inCins inCycle =>
            blockedContextIns cause inCins (Or.inl inCycle)
          | binsFails inBins isOut =>
            blockedBackgroundIns cause inBins isOut
          | boutFails inBout isIns =>
            blockedBackgroundOut cause inBout isIns)
        (fun notPos =>
          match Out.isComplete _ _ notPos with
          | Out.intro innerCycle isEmpty inInnerCycle =>
            let isInappInner := isEmpty inInnerCycle cause isCause
            match isInappInner with
            | blockedContextIns _ inCins inInner =>
              let out := Out.intro innerCycle isEmpty inInner
              blockedContextIns cause inCins (Or.inr out.isSound)
            | blockedBackgroundIns _ inBins notPos =>
              blockedBackgroundIns cause inBins notPos
            | blockedBackgroundOut _ inBout isIns =>
              blockedBackgroundOut cause inBout isIns))
    (Or.inl inCycle)

def IsCauseInapplicable.toExtended
  (isInapp: IsCauseInapplicable salg dl cycle cause)
:
  IsCauseInappExtended salg dl cycle cause
:=
  open IsCauseInappExtended in
  match isInapp with
  | blockedContextIns cause inCins inCycle =>
    cinsFailsCycle inCins inCycle
  | blockedBackgroundIns cause inBins isOut =>
    binsFails inBins isOut
  | blockedBackgroundOut cause inBout isIns =>
    boutFails inBout isIns

def IsCauseInappExtended.toSuperCause
  (isInapp: IsCauseInappExtended salg dl cycle causeA)
  (isSuper: causeA ⊆ causeB)
:
  IsCauseInappExtended salg dl cycle causeB
:=
  match isInapp with
  | cinsFailsCycle inCins inCycle =>
    cinsFailsCycle (isSuper.cinsLe inCins) inCycle
  | cinsFailsOut inCins isOut =>
    cinsFailsOut (isSuper.cinsLe inCins) isOut
  | binsFails inBins isOut =>
    binsFails (isSuper.binsLe inBins) isOut
  | boutFails inBout isIns =>
    boutFails (isSuper.boutLe inBout) isIns

def IsCauseInappExtended.toSuperCycle
  (isInapp: IsCauseInappExtended salg dl cycleA cause)
  (isSuper: cycleA ⊆ cycleB)
:
  IsCauseInappExtended salg dl cycleB cause
:=
  match isInapp with
  | cinsFailsCycle inCins inCycle =>
    cinsFailsCycle inCins (isSuper inCycle)
  | cinsFailsOut inCins isOut =>
    cinsFailsOut inCins isOut
  | binsFails inBins isOut =>
    binsFails inBins isOut
  | boutFails inBout isIns =>
    boutFails inBout isIns

def IsCauseInappExtended.toSuper
  (isInapp: IsCauseInappExtended salg dl cycleA causeA)
  (isSuper: cycleA ⊆ cycleB)
  (isSuperCause: causeA ⊆ causeB)
:
  IsCauseInappExtended salg dl cycleB causeB
:=
  let isInapp := isInapp.toSuperCause isSuperCause
  isInapp.toSuperCycle isSuper


def IsCauseInappExtended.Not.union
  (isAppLeft:
    ¬ IsCauseInappExtended salg dl cycle causeLeft)
  (isAppRite:
    ¬ IsCauseInappExtended salg dl cycle causeRite)
:
  Not
    (IsCauseInappExtended
      salg dl cycle (causeLeft.union causeRite))
|
  cinsFailsCycle inCins inCycle =>
    inCins.elim
      (fun inCinsLeft =>
        isAppLeft (cinsFailsCycle inCinsLeft inCycle))
      (fun inCinsRite =>
        isAppRite (cinsFailsCycle inCinsRite inCycle))
|
  cinsFailsOut inCins isOut =>
    inCins.elim
      (fun inCinsLeft =>
        isAppLeft (cinsFailsOut inCinsLeft isOut))
      (fun inCinsRite =>
        isAppRite (cinsFailsOut inCinsRite isOut))
|
  binsFails inBins isOut =>
    inBins.elim
      (fun inBinsLeft =>
        isAppLeft (binsFails inBinsLeft isOut))
      (fun inBinsRite =>
        isAppRite (binsFails inBinsRite isOut))
|
  boutFails inBout isIns =>
    inBout.elim
      (fun inBoutLeft =>
        isAppLeft (boutFails inBoutLeft isIns))
      (fun inBoutRite =>
        isAppRite (boutFails inBoutRite isIns))

def IsCauseInappExtended.Not.arbUn
  {causes: salg.D → Cause Var salg.D}
  (isApp: ∀ dX, ¬ IsCauseInappExtended salg dl cycle (causes dX))
:
  ¬ IsCauseInappExtended salg dl cycle (Cause.arbUn causes)
|
  cinsFailsCycle ⟨dX, inCins⟩ inCycle =>
    isApp dX (cinsFailsCycle inCins inCycle)
| cinsFailsOut ⟨dX, inCins⟩ isOut =>
    isApp dX (cinsFailsOut inCins isOut)
| binsFails ⟨dX, inBins⟩ isOut =>
    isApp dX (binsFails inBins isOut)
| boutFails ⟨dX, inBout⟩ isIns =>
    isApp dX (boutFails inBout isIns)
