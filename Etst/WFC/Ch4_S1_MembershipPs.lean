/-
  This is the section 1 of chapter 4. It contains the very last
  part of the proofs of soundness and completeness of the proof
  system.
  
  For the full proofs, see the file
  `/Etst/WFC/Utils/MembershipPs/Helpers.lean`.
-/

import Etst.WFC.Utils.MembershipPs.Helpers

namespace Etst


mutual
def DefList.Ins.isSound {dl x p}
  (ins: Ins dl x p)
:
  (dl.wfm x).defMem p
:=
  match ins with
  | Ins.intro _ _ _ isCause insCins outBout =>
    DefList.wfm_isModel dl ▸
    isCause {
      cinsSat h := Ins.isSound (insCins h)
      boutSat h := Out.isSound (outBout h)
    }

def DefList.Out.isSound {dl x p}
  (out: Out dl x p)
:
  ¬(dl.wfm x).posMem p
:=
  match out with
  | .intro cycle isEmptyCycle inCycle =>
    empty_cycle_is_out dl cycle
      (fun inCycle cause isWeak =>
        match isEmptyCycle inCycle cause isWeak with
        | .blockedCins _ inCins inCycle =>
          .blockedCins inCins inCycle
        | .blockedBout _ inBout isIns =>
          .blockedBout inBout isIns.isSound
        )
      inCycle
end


def DefList.Ins.isComplete {dl x p}
  (ins: (dl.wfm x).defMem p)
:
  Ins dl x p
:=
  (completenessProofB dl).insIsComplete ins

def DefList.Out.isComplete {dl x p}
  (out: ¬(dl.wfm x).posMem p)
:
  Out dl x p
:=
  (completenessProofB dl).outIsComplete out


def DefList.Ins.nopeOut {P dl x p}
  (isIns: Ins dl x p)
  (isOut: Out dl x p)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Ins.nopeNotDef {P dl x p}
  (isIns: Ins dl x p)
  (notDef: ¬(dl.wfm x).defMem p)
:
  P
:=
  False.elim (notDef isIns.isSound)

def DefList.Ins.nopeNotPos {P dl x p}
  (isIns: Ins dl x p)
  (notPos: ¬(dl.wfm x).posMem p)
:
  P
:=
  False.elim (notPos isIns.isSound.toPos)


def DefList.Out.nopeIns {P dl x p}
  (isOut: Out dl x p)
  (isIns: Ins dl x p)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Out.nopeDef {P dl x p}
  (isOut: Out dl x p)
  (isDef: (dl.wfm x).defMem p)
:
  P
:=
  False.elim (isOut.isSound isDef.toPos)

def DefList.Out.nopePos {P dl x p}
  (isOut: Out dl x p)
  (isPos: (dl.wfm x).posMem p)
:
  P
:=
  False.elim (isOut.isSound isPos)
