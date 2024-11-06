import UniSet3.Ch8_S12_DefListToEncoding


def Cause.SatisfiesBoundVars
  (cause: Cause Pair)
  (boundVars: List (ValVar Pair))
:=
  ∀ {x xEnc d},
    xEnc = Pair.fromNat x →
    Pair.uniSet3.IsGetBound
      (Pair.boundVarsEncoding boundVars) xEnc d →
    cause.SatisfiesBoundVar x d

def Cause.SatisfiesBoundVars.union
  {causeL causeR: Cause Pair}
  (satL: causeL.SatisfiesBoundVars boundVars)
  (satR: causeR.SatisfiesBoundVars boundVars)
:
  (causeL.union causeR).SatisfiesBoundVars boundVars
:=
  fun eq isBound => (satL eq isBound).union (satR eq isBound)

def Cause.SatisfiesBoundVars.arbUn
  (causes: Pair → Cause Pair)
  (x: Nat)
  (sat: ∀ dH, (causes dH).SatisfiesBoundVars (⟨dH, x⟩ :: boundVars))
:
  Cause.SatisfiesBoundVars
    (Cause.arbUn fun dH => (causes dH).exceptX x)
    boundVars
:=
  open Pair.uniSet3 in
  fun xEncEq isBound =>
    {
      cinsSat := fun vv ⟨dH, ⟨inCins, xNeq⟩⟩ xEq =>
        let xEncNeq :=
          xEncEq ▸ Pair.fromNat.injNeq (xEq ▸ Ne.symm xNeq)
        let isBound := IsGetBound.InTail isBound dH xEncNeq
        let satBoundVar := sat dH xEncEq isBound
        satBoundVar.cinsSat vv inCins xEq
      binsSat := fun vv ⟨dH, ⟨inBins, xNeq⟩⟩ xEq =>
        let xEncNeq :=
          xEncEq ▸ Pair.fromNat.injNeq (xEq ▸ Ne.symm xNeq)
        let isBound := IsGetBound.InTail isBound dH xEncNeq
        let satBoundVar := sat dH xEncEq isBound
        satBoundVar.binsSat vv inBins xEq
      boutSat := fun vv ⟨dH, ⟨inBout, xNeq⟩⟩ xEq =>
        let xEncNeq :=
          xEncEq ▸ Pair.fromNat.injNeq (xEq ▸ Ne.symm xNeq)
        let isBound := IsGetBound.InTail isBound dH xEncNeq
        let satBoundVar := sat dH xEncEq isBound
        satBoundVar.boutSat vv inBout xEq
    }

def Cause.SatisfiesBoundVars.withBoundSat
  {cause: Cause Pair}
  (boundVarsSat: cause.SatisfiesBoundVars boundVars)
  (xEncEq: xEnc = Pair.fromNat x)
  (isGetBound:
    Pair.uniSet3.IsGetBound
      (Pair.boundVarsEncoding (⟨dB, xB⟩ :: boundVars))
      xEnc
      d)
:
  (cause.withBound xB dB).SatisfiesBoundVar x d
:=
  open Pair.uniSet3.IsGetBound in
  match isGetBound with
  | InHead _ _ _ =>
    Pair.fromNat.injEq xEncEq ▸ {
      cinsSat :=
        fun _ inCinsWith xEq =>
          inCinsWith.elim (absurd xEq ∘ And.right) And.left
      binsSat :=
        fun _ inBinsWith xEq =>
          inBinsWith.elim (absurd xEq ∘ And.right) And.left
      boutSat :=
        fun _ inBoutWith xEq =>
          inBoutWith.elim (absurd xEq ∘ And.right) And.left
    }
  | InTail isGetTail _ xEncNeq => {
    cinsSat :=
      fun _ inCinsWith xEqX =>
        inCinsWith.elim
          (fun ⟨inCins, _⟩ =>
            let isBoundSat :=
              boundVarsSat xEncEq isGetTail
            isBoundSat.cinsSat _ inCins xEqX)
          (fun ⟨_, xEqXb⟩ =>
            absurd (xEqXb ▸ xEqX ▸ xEncEq.symm) xEncNeq)
    binsSat :=
      fun _ inBinsWith xEqX =>
        inBinsWith.elim
          (fun ⟨inBins, _⟩ =>
            let isBoundSat :=
              boundVarsSat xEncEq isGetTail
            isBoundSat.binsSat _ inBins xEqX)
          (fun ⟨_, xEqXb⟩ =>
            absurd (xEqXb ▸ xEqX ▸ xEncEq.symm) xEncNeq)
    boutSat :=
      fun _ inBoutWith xEqX =>
        inBoutWith.elim
          (fun ⟨inBout, _⟩ =>
            let isBoundSat :=
              boundVarsSat xEncEq isGetTail
            isBoundSat.boutSat _ inBout xEqX)
          (fun ⟨_, xEqXb⟩ =>
            absurd (xEqXb ▸ xEqX ▸ xEncEq.symm) xEncNeq)
  }

def Cause.SatisfiesBoundVars.satTailExceptHead
  {cause: Cause Pair}
  (boundVarsSat: cause.SatisfiesBoundVars (⟨d, x⟩ :: tail))
:
  (cause.exceptX x).SatisfiesBoundVars tail
:=
  fun {xx _xxEnc _d} xEncEq isBoundTail =>
    if h: xx = x then
      {
        cinsSat := fun _ ⟨_, xNeq⟩ xEq => (xNeq (xEq.trans h)).elim
        binsSat := fun _ ⟨_, xNeq⟩ xEq => (xNeq (xEq.trans h)).elim
        boutSat := fun _ ⟨_, xNeq⟩ xEq => (xNeq (xEq.trans h)).elim
      }
    else
      open Pair.uniSet3.IsGetBound in
      let xEncNeq := xEncEq ▸ Pair.fromNat.injNeq (Ne.symm h)
      let causeSat :=
        boundVarsSat xEncEq (InTail isBoundTail _ xEncNeq)
      causeSat.toSubCause (Cause.exceptXIsSub cause x)
