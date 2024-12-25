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
def Cause.SatisfiesBoundVar.backgroundWithBoundsSat
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

def Cause.SatisfiesBoundVars.backgroundWithBoundsSat
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
    SatisfiesBoundVar.backgroundWithBoundsSat
      b
      (xEncEq ▸ isGetBound)

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


def Cause.FulfillsBoundVars
  (cause: Cause Pair)
  (boundVars: List (ValVar Pair))
:=
  ∀ {x xEnc d},
    xEnc = Pair.fromNat x →
    Pair.uniSet3.IsGetBound
      (Pair.boundVarsEncoding boundVars) xEnc d →
    cause.FulfillsBoundVar x d

def Cause.FulfillsBoundVars.unionSat
  {causeL causeR: Cause Pair}
  (fulfillsL: causeL.FulfillsBoundVars boundVars)
  (satR: causeR.SatisfiesBoundVars boundVars)
:
  (causeL.union causeR).FulfillsBoundVars boundVars
:=
  fun eq isBound => {
    cinsSat := fun
    | _, Or.inl inCins => (fulfillsL eq isBound).cinsSat _ inCins
    | _, Or.inr inCins => (satR eq isBound).cinsSat _ inCins
    binsSat := fun
    | _, Or.inl inBins => (fulfillsL eq isBound).binsSat _ inBins
    | _, Or.inr inBins => (satR eq isBound).binsSat _ inBins
    boutSat := fun
    | _, Or.inl inBout => (fulfillsL eq isBound).boutSat _ inBout
    | _, Or.inr inBout => (satR eq isBound).boutSat _ inBout
    cinsFulfills := Or.inl (fulfillsL eq isBound).cinsFulfills
    binsFulfills := Or.inl (fulfillsL eq isBound).binsFulfills
    boutFulfills := fun dOther dNeq =>
      Or.inl ((fulfillsL eq isBound).boutFulfills dOther dNeq)
  }
