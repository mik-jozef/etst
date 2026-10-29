/-
  This is the section 1 of chapter 4. It contains the very last
  part of the proofs of soundness and completeness of the proof
  system.
  
  For the full proofs, see the file
  `/Etst/WFC/Utils/MembershipPs/Helpers.lean`.
-/
module
public import Etst.WFC.Ch4_S0_MembershipPs
import Etst.WFC.Utils.MembershipPs.Helpers

public section
namespace Etst


mutual
theorem DefList.Ins.isSound {dl x p}
  (ins: Ins dl x p)
:
  p ∈ (dl.wfm x).defMem
:=
  match ins with
  | Ins.intro _ _ _ isCause insCins outBout =>
    DefList.wfm_isModel dl ▸
    isCause {
      cinsSat h := Ins.isSound (insCins h)
      boutSat h := Out.isSound (outBout h)
    }

theorem DefList.Out.isSound {dl x p}
  (out: Out dl x p)
:
  ¬ p ∈ (dl.wfm x).posMem
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


theorem DefList.Ins.isComplete {dl x p}
  (ins: p ∈ (dl.wfm x).defMem)
:
  Ins dl x p
:=
  (completenessProofB dl).insIsComplete ins

theorem DefList.Out.isComplete {dl x p}
  (out: ¬ p ∈ (dl.wfm x).posMem)
:
  Out dl x p
:=
  (completenessProofB dl).outIsComplete out


theorem DefList.Ins.nopeOut {dl x p}
  (isIns: Ins dl x p)
  (isOut: Out dl x p)
  {P: Prop}
:
  P
:=
  False.elim (isOut.isSound (Set3.defToPos isIns.isSound))

theorem DefList.Ins.nopeNotDef {dl x p}
  (isIns: Ins dl x p)
  (notDef: ¬ p ∈ (dl.wfm x).defMem)
  {P: Prop}
:
  P
:=
  False.elim (notDef isIns.isSound)

theorem DefList.Ins.nopeNotPos {dl x p}
  (isIns: Ins dl x p)
  (notPos: ¬ p ∈ (dl.wfm x).posMem)
  {P: Prop}
:
  P
:=
  False.elim (notPos (Set3.defToPos isIns.isSound))


theorem DefList.Out.nopeIns {dl x p}
  (isOut: Out dl x p)
  (isIns: Ins dl x p)
  {P: Prop}
:
  P
:=
  False.elim (isOut.isSound (Set3.defToPos isIns.isSound))

theorem DefList.Out.nopeDef {dl x p}
  (isOut: Out dl x p)
  (isDef: p ∈ (dl.wfm x).defMem)
  {P: Prop}
:
  P
:=
  False.elim (isOut.isSound (Set3.defToPos isDef))

theorem DefList.Out.nopePos {dl x p}
  (isOut: Out dl x p)
  (isPos: p ∈ (dl.wfm x).posMem)
  {P: Prop}
:
  P
:=
  False.elim (isOut.isSound isPos)
