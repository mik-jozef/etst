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
  -- Cannot use structural recursion :(
  -- 
  -- ```
  --   failed to infer structural recursion:
  --   Cannot use parameter ins:
  --     the type Ins salg dl does not have a `.brecOn` recursor
  -- ```
  -- 
  -- This would be a terrific feature, Lean:
  -- 
  -- match ins with
  -- | Ins.intro _ _ cause isCause insCins insBins outBout =>
  --   let ihCins {d x} (inCins: ⟨d, x⟩ ∈ cause.contextIns) :=
  --     Ins.isSound (insCins inCins)
    
  --   DefList.wellFoundedModel.isModel salg dl ▸
  --   isCause ⟨ihCins, sorry, sorry⟩
  
  open Cause.IsInapplicable in
  ins.rec
    (motive_1 := fun d x _ => (dl.wellFoundedModel salg x).defMem d)
    (motive_2 := fun cycle cause _ => cause.IsInapplicable cycle (dl.wellFoundedModel salg))
    (motive_3 := fun d x _ => ¬(dl.wellFoundedModel salg x).posMem d)
    (fun _ _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wellFoundedModel.isModel salg dl ▸
      isCause ⟨⟨ihCins⟩, ihBins, ihBout⟩)
    (fun _ _ _ => blockedContextIns)
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
      isCause ⟨⟨ihCins⟩, ihBins, ihBout⟩)
    (fun _ _ _ => blockedContextIns)
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


-- A convenience helper type for `Out.intro4` below.
inductive IsCauseInappExtended
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Set (ValVar salg.D) →
  Cause salg.D →
  Prop

| cinsFailsCycle
  (cause: Cause salg.D)
  {d x}
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  IsCauseInappExtended salg dl cycle cause

| cinsFailsOut
  (cause: Cause salg.D)
  {d x}
  (inCins: ⟨d, x⟩ ∈ cause.contextIns)
  (isOut: Out salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause

| binsFails
  (cause: Cause salg.D)
  {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: Out salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause

| boutFails
  (cause: Cause salg.D)
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: Ins salg dl d x)
:
  IsCauseInappExtended salg dl cycle cause


/-
  A convenience constructor that allows smaller cycles to be used,
  by allowing a cycle to also depend through context on a non-cycle
  element as long as that element is provably out.
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
    IsCauseInappExtended salg dl cycle cause)
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
          | cinsFailsOut cause inCins isOut =>
            blockedContextIns cause inCins (Or.inr isOut.isSound)
          | cinsFailsCycle cause inCins inCycle =>
            blockedContextIns cause inCins (Or.inl inCycle)
          | binsFails cause inBins isOut =>
            blockedBackgroundIns cause inBins isOut
          | boutFails cause inBout isIns =>
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
