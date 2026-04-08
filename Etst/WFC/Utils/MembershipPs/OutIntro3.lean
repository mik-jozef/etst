import Etst.WFC.Ch4_S1_MembershipPs

namespace Etst

inductive DefList.IsCauseInapplicableExtended
  (dl: DefList)
  (cycle: Nat → Set Pair)
  (cause: Cause Pair)
:
  Prop
|
  blockedCinsCycle
  {x d}
  (inCins: cause.cins x d)
  (inCycle: cycle x d)
:
  IsCauseInapplicableExtended dl cycle cause
|
  blockedCinsOut
  {x d}
  (inCins: cause.cins x d)
  (isOut: DefList.Out dl x d)
:
  IsCauseInapplicableExtended dl cycle cause
|
  blockedBout
  {x d}
  (inBout: cause.bout x d)
  (isIns: DefList.Ins dl x d)
:
  IsCauseInapplicableExtended dl cycle cause

def DefList.Out.intro3
  {dl: DefList}
  (cycle: Nat → Set Pair)
  (isEmptyCycle:
    ∀ {x d},
    cycle x d →
    (cause: Cause Pair) →
    cause.IsWeakCause (dl.getDef x) d →
    dl.IsCauseInapplicableExtended cycle cause)
  {x d}
  (inCycle: cycle x d)
:
  DefList.Out dl x d
:=
  let largeCycle x d := cycle x d ∨ ¬(dl.wfm x).posMem d

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
