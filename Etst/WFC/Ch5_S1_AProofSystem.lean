/-
  This is the section 1 of chapter 6. It contains the very last
  part of the proofs of soundness and completeness of the proof
  system.
  
  For the full proofs, see the file `/Etst/WFC/Utils/AProofSystem.lean`.
-/

import Etst.WFC.Utils.AProofSystem

namespace Etst


def Ins.isSound
  (ins: Ins dl d x)
:
  (dl.wfm x).defMem d
:=
  -- Cannot use structural recursion :(
  -- 
  -- ```
  --   failed to infer structural recursion:
  --   Cannot use parameter ins:
  --     the type Ins dl does not have a `.brecOn` recursor
  -- ```
  -- 
  -- This would be a terrific feature, Lean:
  -- 
  -- match ins with
  -- | Ins.intro _ _ cause isCause insCins insBins outBout =>
  --   let ihCins {d x} (inCins: ⟨d, x⟩ ∈ cause.contextIns) :=
  --     Ins.isSound (insCins inCins)
    
  --   DefList.wellFoundedModel.isModel dl ▸
  --   isCause {
  --     contextInsHold := ihCins
  --     backgroundInsHold := sorry
  --     backgroundOutHold := sorry
  --   }
  
  open Cause.IsInapplicable in
  ins.rec
    (motive_1 := fun d x _ => (dl.wfm x).defMem d)
    (motive_2 := fun cycle cause _ =>
      cause.IsInapplicable cycle (dl.wfm))
    (motive_3 := fun d x _ => ¬(dl.wfm x).posMem d)
    (fun _ _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wfm_isModel dl ▸
      isCause ⟨⟨ihBins, ihBout⟩, ihCins⟩)
    (fun _ _ _ => blockedContextIns)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundIns ihBins ihBout)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundOut ihBins ihBout)
    (fun cycle _ inCycle ih =>
      empty_cycle_is_out dl cycle ih inCycle)

def Out.isSound
  (out: Out dl d x)
:
  ¬(dl.wfm x).posMem d
:=
  open Cause.IsInapplicable in
  out.rec
    (motive_1 := fun d x _ => (dl.wfm x).defMem d)
    (motive_2 := fun cycle cause _ =>
      Cause.IsInapplicable cause cycle (dl.wfm))
    (motive_3 := fun d x _ => ¬(dl.wfm x).posMem d)
    (fun _ _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wfm_isModel dl ▸
      isCause ⟨⟨ihBins, ihBout⟩, ihCins⟩)
    (fun _ _ _ => blockedContextIns)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundIns ihBins ihBout)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundOut ihBins ihBout)
    (fun cycle _ inCycle ih =>
      empty_cycle_is_out dl cycle ih inCycle)


def Ins.isComplete
  (dl: DefList)
  {d: Pair}
  {x: Nat}
  (ins: (dl.wfm x).defMem d)
:
  Ins dl d x
:=
  (completenessProofB dl).insIsComplete ins

def Out.isComplete
  (dl: DefList)
  {d: Pair}
  {x: Nat}
  (out: ¬(dl.wfm x).posMem d)
:
  Out dl d x
:=
  (completenessProofB dl).outIsComplete out


def Ins.nopeOut
  (isIns: Ins dl d x)
  (isOut: Out dl d x)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def Ins.nopeNotDef
  (isIns: Ins dl d x)
  (notDef: ¬(dl.wfm x).defMem d)
:
  P
:=
  False.elim (notDef (isIns.isSound))

def Ins.nopeNotPos
  (isIns: Ins dl d x)
  (notPos: ¬(dl.wfm x).posMem d)
:
  P
:=
  False.elim (notPos (isIns.isSound.toPos))


def Out.nopeIns
  (isOut: Out dl d x)
  (isIns: Ins dl d x)
:
  P
:=
  False.elim (isOut.isSound isIns.isSound.toPos)

def Out.nopeDef
  (isOut: Out dl d x)
  (isDef: (dl.wfm x).defMem d)
:
  P
:=
  False.elim (isOut.isSound (isDef.toPos))

def Out.nopePos
  (isOut: Out dl d x)
  (isPos: (dl.wfm x).posMem d)
:
  P
:=
  False.elim (isOut.isSound isPos)
