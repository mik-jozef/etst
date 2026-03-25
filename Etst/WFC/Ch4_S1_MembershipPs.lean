/-
  This is the section 1 of chapter 4. It contains the very last
  part of the proofs of soundness and completeness of the proof
  system.
  
  For the full proofs, see the file
  `/Etst/WFC/Utils/MembershipPsHelpers.lean`.
-/

import Etst.WFC.Utils.MembershipPsHelpers

namespace Etst


mutual
def DefList.Ins.isSound {dl d x}
  (ins: Ins dl d x)
:
  (dl.wfm x).defMem d
:=
  match ins with
  | Ins.intro _ _ _ isCause insCins insBins outBout =>
    DefList.wfm_isModel dl ▸
    isCause {
      contextInsHold := fun h => Ins.isSound (insCins h)
      backgroundInsHold := fun h => Ins.isSound (insBins h)
      backgroundOutHold := fun h => Out.isSound (outBout h)
    }

def DefList.Out.isSound {dl d x}
  (out: Out dl d x)
:
  ¬(dl.wfm x).posMem d
:=
  match out with
  | .intro cycle isEmptyCycle inCycle =>
    empty_cycle_is_out dl cycle
      (fun inCycle cause isWeak =>
        match isEmptyCycle inCycle cause isWeak with
        | .blockedContextIns _ inCins inCycle =>
          .blockedContextIns inCins inCycle
        | .blockedBackgroundIns _ inBins isOut =>
          .blockedBackgroundIns inBins isOut.isSound
        | .blockedBackgroundOut _ inBout isIns =>
          .blockedBackgroundOut inBout isIns.isSound
        )
      inCycle
end


def DefList.Ins.isComplete {dl d x}
  (ins: (dl.wfm x).defMem d)
:
  Ins dl d x
:=
  (completenessProofB dl).insIsComplete ins

def DefList.Out.isComplete {dl d x}
  (out: ¬(dl.wfm x).posMem d)
:
  Out dl d x
:=
  (completenessProofB dl).outIsComplete out


def DefList.Ins.nopeOut {P dl d x}
  (isIns: Ins dl d x)
  (isOut: Out dl d x)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Ins.nopeNotDef {P dl d x}
  (isIns: Ins dl d x)
  (notDef: ¬(dl.wfm x).defMem d)
:
  P
:=
  False.elim (notDef (isIns.isSound))

def DefList.Ins.nopeNotPos {P dl d x}
  (isIns: Ins dl d x)
  (notPos: ¬(dl.wfm x).posMem d)
:
  P
:=
  False.elim (notPos (isIns.isSound.toPos))


def DefList.Out.nopeIns {P dl d x}
  (isOut: Out dl d x)
  (isIns: Ins dl d x)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Out.nopeDef {P dl d x}
  (isOut: Out dl d x)
  (isDef: (dl.wfm x).defMem d)
:
  P
:=
  False.elim (isOut.isSound (isDef.toPos))

def DefList.Out.nopePos {P dl d x}
  (isOut: Out dl d x)
  (isPos: (dl.wfm x).posMem d)
:
  P
:=
  False.elim (isOut.isSound isPos)
