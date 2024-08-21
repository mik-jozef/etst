/-
  This is the section 1 of chapter 6. It contains the very last
  part of the proofs of soundness and completeness of the proof
  system.
  
  For the full proofs, see the file `Utils/AProofSystem.lean`.
-/

import Utils.AProofSystem


def Ins.isSound
  (ins: Ins salg dl d x)
:
  (dl.wellFoundedModel salg x).defMem d
:=
  -- Cannot use structural recursion, most likely because of
  -- this issue:
  -- https://github.com/leanprover/lean4/issues/4751
  open Cause.IsInapplicable in
  ins.rec
    (motive_1 := fun d x _ => (dl.wellFoundedModel salg x).defMem d)
    (motive_2 := fun cycle cause _ => cause.IsInapplicable cycle (dl.wellFoundedModel salg))
    (motive_3 := fun d x _ => ¬(dl.wellFoundedModel salg x).posMem d)
    (fun _ _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wellFoundedModel.isModel salg dl ▸
      isCause ⟨ihCins, ihBins, ihBout⟩)
    (fun _ _ _ => Cause.IsInapplicable.blockedContextIns)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundIns ihBins ihBout)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundOut ihBins ihBout)
    (fun cycle _ inCycle ih => emptyCycleIsOut salg dl cycle ih inCycle)

def Out.isSound
  (out: Out salg dl d x)
:
  ¬(dl.wellFoundedModel salg x).posMem d
:=
  open Cause.IsInapplicable in
  out.rec
    (motive_1 := fun d x _ => (dl.wellFoundedModel salg x).defMem d)
    (motive_2 := fun cycle cause _ => Cause.IsInapplicable cause cycle (dl.wellFoundedModel salg))
    (motive_3 := fun d x _ => ¬(dl.wellFoundedModel salg x).posMem d)
    (fun _ _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wellFoundedModel.isModel salg dl ▸
      isCause ⟨ihCins, ihBins, ihBout⟩)
    (fun _ _ _ => Cause.IsInapplicable.blockedContextIns)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundIns ihBins ihBout)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundOut ihBins ihBout)
    (fun cycle _ inCycle ih => emptyCycleIsOut salg dl cycle ih inCycle)


def Ins.isComplete
  (salg: Salgebra sig)
  (dl: DefList sig)
  {d: salg.D}
  {x: Nat}
  (ins: (dl.wellFoundedModel salg x).defMem d)
:
  Ins salg dl d x
:=
  (completenessProofB salg dl).insIsComplete ins

def Out.isComplete
  (salg: Salgebra sig)
  (dl: DefList sig)
  {d: salg.D}
  {x: Nat}
  (out: ¬(dl.wellFoundedModel salg x).posMem d)
:
  Out salg dl d x
:=
  (completenessProofB salg dl).outIsComplete out
