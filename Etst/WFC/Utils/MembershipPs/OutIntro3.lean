import Etst.WFC.Ch4_S1_MembershipPs

namespace Etst

inductive DefList.IsCauseInapplicableExtended
  (dl: DefList)
  (o: Valuation Pair)
  (cycle: Nat → Set Pair)
  (cause: Cause Pair)
:
  Prop
|
  blockedCinsCycle
  {x p}
  (inCins: cause.cins x p)
  (inCycle: cycle x p)
:
  IsCauseInapplicableExtended dl o cycle cause
|
  blockedCinsOut
  {x p}
  (inCins: cause.cins x p)
  (isOut: DefList.Out dl o x p)
:
  IsCauseInapplicableExtended dl o cycle cause
|
  blockedBout
  {x p}
  (inBout: cause.bout x p)
  (isIns: DefList.Ins dl o x p)
:
  IsCauseInapplicableExtended dl o cycle cause

def DefList.Out.intro3
  {dl: DefList}
  {o: Valuation Pair}
  (cycle: Nat → Set Pair)
  (isEmptyCycle:
    ∀ {x p},
    cycle x p →
    (cause: Cause Pair) →
    cause.IsWeakCause o (dl.getDef x) p →
    dl.IsCauseInapplicableExtended o cycle cause)
  {x p}
  (inCycle: cycle x p)
:
  DefList.Out dl o x p
:=
  let largeCycle x p := cycle x p ∨ ¬(dl.wfm o x).posMem p

  DefList.Out.intro
    largeCycle
    (fun inLargeCycle cause isCause =>
      match inLargeCycle with
      | Or.inl inCycle =>
        match isEmptyCycle inCycle cause isCause with
        | .blockedCinsOut inCins isOut =>
          .blockedCins cause inCins (Or.inr isOut.isSound)
        | .blockedCinsCycle inCins inCycle =>
          .blockedCins cause inCins (Or.inl inCycle)
        | .blockedBout inBout isIns =>
          .blockedBout cause inBout isIns
      | Or.inr notPos =>
        match DefList.Out.isComplete notPos with
        | .intro innerCycle isEmpty inInnerCycle =>
          match isEmpty inInnerCycle cause isCause with
          | .blockedCins _ inCins inInner =>
            let out := DefList.Out.intro innerCycle isEmpty inInner
            .blockedCins cause inCins (Or.inr out.isSound)
          | .blockedBout _ inBout isIns =>
            .blockedBout cause inBout isIns)
    (Or.inl inCycle)

end Etst
