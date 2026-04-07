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
def DefList.Ins.isSound {dl x d}
  (ins: Ins dl x d)
:
  (dl.wfm x).defMem d
:=
  match ins with
  | Ins.intro _ _ _ isCause insCins outBout =>
    DefList.wfm_isModel dl ▸
    isCause {
      cinsSat := fun h => Ins.isSound (insCins h)
      boutSat := fun h => Out.isSound (outBout h)
    }

def DefList.Out.isSound {dl x d}
  (out: Out dl x d)
:
  ¬(dl.wfm x).posMem d
:=
  match out with
  | .intro cycle isEmptyCycle inCycle =>
    empty_cycle_is_out dl cycle
      (fun inCycle cause isWeak =>
        match isEmptyCycle inCycle cause isWeak with
        | .blockedContext _ inCins inCycle =>
          .blockedContext inCins inCycle
        | .blockedBackground _ inBout isIns =>
          .blockedBackground inBout isIns.isSound
        )
      inCycle
end


def DefList.Ins.isComplete {dl x d}
  (ins: (dl.wfm x).defMem d)
:
  Ins dl x d
:=
  (completenessProofB dl).insIsComplete ins

def DefList.Out.isComplete {dl x d}
  (out: ¬(dl.wfm x).posMem d)
:
  Out dl x d
:=
  (completenessProofB dl).outIsComplete out


def DefList.Ins.nopeOut {P dl x d}
  (isIns: Ins dl x d)
  (isOut: Out dl x d)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Ins.nopeNotDef {P dl x d}
  (isIns: Ins dl x d)
  (notDef: ¬(dl.wfm x).defMem d)
:
  P
:=
  False.elim (notDef (isIns.isSound))

def DefList.Ins.nopeNotPos {P dl x d}
  (isIns: Ins dl x d)
  (notPos: ¬(dl.wfm x).posMem d)
:
  P
:=
  False.elim (notPos (isIns.isSound.toPos))


def DefList.Out.nopeIns {P dl x d}
  (isOut: Out dl x d)
  (isIns: Ins dl x d)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Out.nopeDef {P dl x d}
  (isOut: Out dl x d)
  (isDef: (dl.wfm x).defMem d)
:
  P
:=
  False.elim (isOut.isSound (isDef.toPos))

def DefList.Out.nopePos {P dl x d}
  (isOut: Out dl x d)
  (isPos: (dl.wfm x).posMem d)
:
  P
:=
  False.elim (isOut.isSound isPos)
