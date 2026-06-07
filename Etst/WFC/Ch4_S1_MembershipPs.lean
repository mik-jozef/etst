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
def DefList.Ins.isSound {dl o x p}
  (ins: Ins dl o x p)
:
  (dl.wfm o x).defMem p
:=
  match ins with
  | Ins.intro _ _ _ isCause insCins outBout =>
    DefList.wfm_isModel dl o ▸
    isCause {
      cinsSat h := Ins.isSound (insCins h)
      boutSat h := Out.isSound (outBout h)
    }

def DefList.Out.isSound {dl o x p}
  (out: Out dl o x p)
:
  ¬(dl.wfm o x).posMem p
:=
  match out with
  | .intro cycle isEmptyCycle inCycle =>
    empty_cycle_is_out dl o cycle
      (fun inCycle cause isWeak =>
        match isEmptyCycle inCycle cause isWeak with
        | .blockedCins _ inCins inCycle =>
          .blockedCins inCins inCycle
        | .blockedBout _ inBout isIns =>
          .blockedBout inBout isIns.isSound
        )
      inCycle
end


def DefList.Ins.isComplete {dl o x p}
  (ins: (dl.wfm o x).defMem p)
:
  Ins dl o x p
:=
  (completenessProofB dl o).insIsComplete ins

def DefList.Out.isComplete {dl o x p}
  (out: ¬(dl.wfm o x).posMem p)
:
  Out dl o x p
:=
  (completenessProofB dl o).outIsComplete out


def DefList.Ins.nopeOut {P dl o x p}
  (isIns: Ins dl o x p)
  (isOut: Out dl o x p)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Ins.nopeNotDef {P dl o x p}
  (isIns: Ins dl o x p)
  (notDef: ¬(dl.wfm o x).defMem p)
:
  P
:=
  False.elim (notDef isIns.isSound)

def DefList.Ins.nopeNotPos {P dl o x p}
  (isIns: Ins dl o x p)
  (notPos: ¬(dl.wfm o x).posMem p)
:
  P
:=
  False.elim (notPos isIns.isSound.toPos)


def DefList.Out.nopeIns {P dl o x p}
  (isOut: Out dl o x p)
  (isIns: Ins dl o x p)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def DefList.Out.nopeDef {P dl o x p}
  (isOut: Out dl o x p)
  (isDef: (dl.wfm o x).defMem p)
:
  P
:=
  False.elim (isOut.isSound isDef.toPos)

def DefList.Out.nopePos {P dl o x p}
  (isOut: Out dl o x p)
  (isPos: (dl.wfm o x).posMem p)
:
  P
:=
  False.elim (isOut.isSound isPos)
