import WFC.Ch6_S1_AProofSystem

def IsVarFree
  (boundVars: List (ValVar D))
  (x: Nat)
:
  Prop
:=
  ∀ d, ⟨d, x⟩ ∉ boundVars

/-
  A convenience helper type for `Out.intro4` below. Includes support
  for bound variables in case one needs to account for them.
-/
inductive IsCauseInappExtended
  (salg: Salgebra sig)
  (dl: DefList sig)
  (cycle: Set (ValVar salg.D))
  (cause: Cause salg.D)
  (boundVars: List (ValVar salg.D))
:
  Prop
|
  cinsFailsCycle
  {d x}
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (isFree: IsVarFree boundVars x)
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  IsCauseInappExtended salg dl cycle cause boundVars
|
  cinsFailsOut
  {d x}
  (inCins: ⟨d, x⟩ ∈ cause.contextIns)
  (isFree: IsVarFree boundVars x)
  (isOut: Out salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause boundVars
|
  binsFails
  {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isFree: IsVarFree boundVars x)
  (isOut: Out salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause boundVars
|
  boutFails
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isFree: IsVarFree boundVars x)
  (isIns: Ins salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause boundVars


/-
  A convenience constructor that allows smaller cycles to be used,
  by allowing the empty cycle to also depend through context on a
  non-cycle element as long as that element is provably out.
  
  Without this option, the cycle would have to recursively include
  all such elements.
  
  TODO consider:
  0. There is one more thing that probably could (ought?) be done
  to make the proof system more convenient to use: the
  `Is[Strongly|Weakly]SatisfiedBy` predicates could be made to
  only consider valuations that are models of the definition list.
  This would make the proofs easier to construct, but destructing
  them would give less information.
  1. Is tracking bound variables really necessary in Ch9? Figure
  this out.
-/
def Out.intro4
  {salg: Salgebra sig}
  {dl: DefList sig}
  (cycle: Set (ValVar salg.D))
  (isEmptyCycle:
    ∀ {d x},
    ⟨d, x⟩ ∈ cycle →
    (cause: Cause salg.D) →
    IsWeakCause salg cause d (dl.getDef x) →
    IsCauseInappExtended salg dl cycle cause [])
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
          | cinsFailsOut inCins _ isOut =>
            blockedContextIns cause inCins (Or.inr isOut.isSound)
          | cinsFailsCycle inCins _ inCycle =>
            blockedContextIns cause inCins (Or.inl inCycle)
          | binsFails inBins _ isOut =>
            blockedBackgroundIns cause inBins isOut
          | boutFails inBout _ isIns =>
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
  IsCauseInappExtended salg dl cycle cause []
:=
  open IsCauseInappExtended in
  match isInapp with
  | blockedContextIns cause inCins inCycle =>
    cinsFailsCycle inCins nofun inCycle
  | blockedBackgroundIns cause inBins isOut =>
    binsFails inBins nofun isOut
  | blockedBackgroundOut cause inBout isIns =>
    boutFails inBout nofun isIns

def IsCauseInappExtended.toSuperCause
  (isInapp: IsCauseInappExtended salg dl cycle causeA boudVars)
  (isSuper: causeA ⊆ causeB)
:
  IsCauseInappExtended salg dl cycle causeB boudVars
:=
  match isInapp with
  | cinsFailsCycle inCins bv inCycle =>
    cinsFailsCycle (isSuper.cinsLe inCins) bv inCycle
  | cinsFailsOut inCins bv isOut =>
    cinsFailsOut (isSuper.cinsLe inCins) bv isOut
  | binsFails inBins bv isOut =>
    binsFails (isSuper.binsLe inBins) bv isOut
  | boutFails inBout bv isIns =>
    boutFails (isSuper.boutLe inBout) bv isIns

def IsCauseInappExtended.toSuperCycle
  (isInapp: IsCauseInappExtended salg dl cycleA cause boudVars)
  (isSuper: cycleA ⊆ cycleB)
:
  IsCauseInappExtended salg dl cycleB cause boudVars
:=
  match isInapp with
  | cinsFailsCycle inCins bv inCycle =>
    cinsFailsCycle inCins bv (isSuper inCycle)
  | cinsFailsOut inCins bv isOut =>
    cinsFailsOut inCins bv isOut
  | binsFails inBins bv isOut =>
    binsFails inBins bv isOut
  | boutFails inBout bv isIns =>
    boutFails inBout bv isIns

def IsCauseInappExtended.toSuper
  (isInapp: IsCauseInappExtended salg dl cycleA causeA boudVars)
  (isSuper: cycleA ⊆ cycleB)
  (isSuperCause: causeA ⊆ causeB)
:
  IsCauseInappExtended salg dl cycleB causeB boudVars
:=
  let isInapp := isInapp.toSuperCause isSuperCause
  isInapp.toSuperCycle isSuper

def IsCauseInappExtended.toEmptyBoundVars
  (isInapp: IsCauseInappExtended salg dl cycle cause boundVars)
:
  IsCauseInappExtended salg dl cycle cause []
:=
  match isInapp with
  | cinsFailsCycle inCins _ inCycle =>
    cinsFailsCycle inCins nofun inCycle
  | cinsFailsOut inCins _ isOut =>
    cinsFailsOut inCins nofun isOut
  | binsFails inBins _ isOut =>
    binsFails inBins nofun isOut
  | boutFails inBout _ isIns =>
    boutFails inBout nofun isIns


def IsCauseInappExtended.Not.union
  (isAppLeft:
    ¬ IsCauseInappExtended salg dl cycle causeLeft boundVars)
  (isAppRite:
    ¬ IsCauseInappExtended salg dl cycle causeRite boundVars)
:
  Not
    (IsCauseInappExtended
      salg
      dl
      cycle
      (causeLeft.union causeRite)
      boundVars)
|
  cinsFailsCycle inCins bv inCycle =>
    inCins.elim
      (fun inCinsLeft =>
        isAppLeft (cinsFailsCycle inCinsLeft bv inCycle))
      (fun inCinsRite =>
        isAppRite (cinsFailsCycle inCinsRite bv inCycle))
|
  cinsFailsOut inCins bv isOut =>
    inCins.elim
      (fun inCinsLeft =>
        isAppLeft (cinsFailsOut inCinsLeft bv isOut))
      (fun inCinsRite =>
        isAppRite (cinsFailsOut inCinsRite bv isOut))
|
  binsFails inBins bv isOut =>
    inBins.elim
      (fun inBinsLeft =>
        isAppLeft (binsFails inBinsLeft bv isOut))
      (fun inBinsRite =>
        isAppRite (binsFails inBinsRite bv isOut))
|
  boutFails inBout bv isIns =>
    inBout.elim
      (fun inBoutLeft =>
        isAppLeft (boutFails inBoutLeft bv isIns))
      (fun inBoutRite =>
        isAppRite (boutFails inBoutRite bv isIns))
