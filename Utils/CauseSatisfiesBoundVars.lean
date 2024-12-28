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
    (Cause.arbUn fun dH => (causes dH).exceptVar x)
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

def Cause.SatisfiesBoundVars.satWithBound
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

-- TODO move to Valuation.lean.
def Valuation.withBoundVars.eqOfIsGetBound
  (b: Valuation Pair)
  (isGetBound:
    Pair.uniSet3.IsGetBound
      (Pair.boundVarsEncoding boundVars)
    (Pair.fromNat x)
    d)
:
  (b.withBoundVars boundVars x) = Set3.just d
:=
  match boundVars with
  | ⟨dd, xx⟩ :: tail => by
    unfold Valuation.withBoundVars
    exact  
      if h: x = xx then
        Valuation.update.eqBoundOfEq _ h.symm dd ▸
        congr rfl (isGetBound.listHead h).symm
      else
        Valuation.update.eqOrig _ (Ne.symm h) dd ▸
        eqOfIsGetBound b (isGetBound.listToTail h)

-- TODO move to Valuation.lean.
def Valuation.withBoundVars.eqOrigOfIsFree
  (b: Valuation Pair)
  (isFree: ¬ Pair.IsBound boundVars x)
:
  (b.withBoundVars boundVars x) = b x
:=
  match boundVars with
  | [] => rfl
  | ⟨dd, xx⟩ :: tail =>
    if h: x = xx then
      let isGetBound := Pair.uniSet3.IsGetBound.InHead
        (Pair.fromNat.isNatEncoding x) _ _
      
      absurd ⟨dd, h ▸ isGetBound⟩ isFree
    else by
      unfold Valuation.withBoundVars
      exact
        Valuation.update.eqOrig _ (Ne.symm h) dd ▸
        eqOrigOfIsFree b (Pair.IsBound.Not.notBoundTail isFree)

-- TODO move to AProofSystem to other SatisfiesBoundVar stuff.
def Cause.SatisfiesBoundVar.bWithBoundsSatBoundVar
  (b: Valuation Pair)
  (isGetBound:
    Pair.uniSet3.IsGetBound
      (Pair.boundVarsEncoding boundVars)
    (Pair.fromNat x)
    d)
:
  Cause.SatisfiesBoundVar
    (ofValPos
      (b.withBoundVars boundVars)
      Valuation.empty)
    x
    d
:=
  let eq :=
    Valuation.withBoundVars.eqOfIsGetBound b isGetBound
  {
    cinsSat := nofun
    binsSat :=
      fun vv inBins xEq =>
        show (Set3.just d).posMem vv.d from eq ▸ xEq ▸ inBins
    boutSat :=
      fun vv inBout xEq =>
        show ¬ (Set3.just d).defMem vv.d from eq ▸ xEq ▸ inBout
  }

def Cause.SatisfiesBoundVars.bWithBoundsSatBoundVars
  (b: Valuation Pair)
  (boundVars: List (ValVar Pair))
:
  Cause.SatisfiesBoundVars
    (Cause.ofValPos
      (b.withBoundVars boundVars)
      Valuation.empty)
    boundVars
:=
  fun xEncEq isGetBound =>
    SatisfiesBoundVar.bWithBoundsSatBoundVar
      b
      (xEncEq ▸ isGetBound)

def Cause.SatisfiesBoundVars.exceptHeadSatTail
  {cause: Cause Pair}
  (boundVarsSat: cause.SatisfiesBoundVars (⟨d, x⟩ :: tail))
:
  (cause.exceptVar x).SatisfiesBoundVars tail
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
      causeSat.toSubCause (Cause.exceptVarIsSub cause x)

-- TODO move to AProofSystem to other SatisfiesBoundVar stuff.
def Cause.SatisfiesBoundVar.withBoundsSatBoundVar
  (isGetBound:
    Pair.uniSet3.IsGetBound
      (Pair.boundVarsEncoding boundVars)
      (Pair.fromNat x)
      d)
  (v: Valuation Pair)
:
  Cause.SatisfiesBoundVar
    (ofValPos
      (v.withBoundVars boundVars)
      (v.withBoundVars boundVars))
    x
    d
:=
  let eq :=
    Valuation.withBoundVars.eqOfIsGetBound v isGetBound
  {
    cinsSat :=
      fun _ inCins xEq =>
        show (Set3.just d).posMem _ from eq ▸ xEq ▸ inCins
    binsSat :=
      fun _ inBins xEq =>
        show (Set3.just d).posMem _ from eq ▸ xEq ▸ inBins
    boutSat :=
      fun _ inBout xEq =>
        show ¬ (Set3.just d).defMem _ from eq ▸ xEq ▸ inBout
  }

def Cause.SatisfiesBoundVars.withBoundsSatBoundVars
  (boundVars: List (ValVar Pair))
  (v: Valuation Pair)
:
  Cause.SatisfiesBoundVars
    (Cause.ofValPos
      (v.withBoundVars boundVars)
      (v.withBoundVars boundVars))
    boundVars
:=
  fun xEncEq isGetBound =>
    SatisfiesBoundVar.withBoundsSatBoundVar
      (xEncEq ▸ isGetBound) v
