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
