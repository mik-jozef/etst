import UniSet3.Ch8_S12_DefListToEncoding
import Utils.IsBound


def Cause.SatisfiesBoundVars
  (cause: Cause Pair)
  (boundVars: List (ValVar Pair))
:=
  ∀ {x d},
    IsBoundTo boundVars x d →
    cause.SatisfiesBoundVar x d

def Cause.SatisfiesBoundVars.union
  {causeL causeR: Cause Pair}
  (satL: causeL.SatisfiesBoundVars boundVars)
  (satR: causeR.SatisfiesBoundVars boundVars)
:
  (causeL.union causeR).SatisfiesBoundVars boundVars
:=
  fun isBoundTo => (satL isBoundTo).union (satR isBoundTo)

def Cause.SatisfiesBoundVars.arbUn
  (causes: Pair → Cause Pair)
  (x: Var)
  (sat: ∀ dH, (causes dH).SatisfiesBoundVars (⟨dH, x⟩ :: boundVars))
:
  Cause.SatisfiesBoundVars
    (Cause.arbUn fun dH => (causes dH).exceptVar x)
    boundVars
:=
  fun isBoundTo =>
    {
      cinsSat := fun vv ⟨dH, ⟨inCins, xNeq⟩⟩ xEq =>
        let isBound := IsBoundTo.InTail isBoundTo (xEq ▸ xNeq) dH
        let satBoundVar := sat dH isBound
        satBoundVar.cinsSat vv inCins xEq
      binsSat := fun vv ⟨dH, ⟨inBins, xNeq⟩⟩ xEq =>
        let isBound := IsBoundTo.InTail isBoundTo (xEq ▸ xNeq) dH
        let satBoundVar := sat dH isBound
        satBoundVar.binsSat vv inBins xEq
      boutSat := fun vv ⟨dH, ⟨inBout, xNeq⟩⟩ xEq =>
        let isBound := IsBoundTo.InTail isBoundTo (xEq ▸ xNeq) dH
        let satBoundVar := sat dH isBound
        satBoundVar.boutSat vv inBout xEq
    }

def Cause.SatisfiesBoundVars.satWithBound
  {cause: Cause Pair}
  (boundVarsSat: cause.SatisfiesBoundVars boundVars)
  (isBoundTo: IsBoundTo (⟨dB, xB⟩ :: boundVars) x d)
:
  (cause.withBound xB dB).SatisfiesBoundVar x d
:=
  open IsBoundTo in
  match isBoundTo with
  | InHead => {
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
  | InTail isBoundTail xNeqXb _ => {
    cinsSat :=
      fun _ inCinsWith xEqX =>
        inCinsWith.elim
          (fun ⟨inCins, _⟩ =>
            (boundVarsSat isBoundTail).cinsSat _ inCins xEqX)
          (fun ⟨_, xEqXb⟩ => absurd (xEqX ▸ xEqXb) xNeqXb)
    binsSat :=
      fun _ inBinsWith xEqX =>
        inBinsWith.elim
          (fun ⟨inBins, _⟩ =>
            (boundVarsSat isBoundTail).binsSat _ inBins xEqX)
          (fun ⟨_, xEqXb⟩ => absurd (xEqX ▸ xEqXb) xNeqXb)
    boutSat :=
      fun _ inBoutWith xEqX =>
        inBoutWith.elim
          (fun ⟨inBout, _⟩ =>
            (boundVarsSat isBoundTail).boutSat _ inBout xEqX)
          (fun ⟨_, xEqXb⟩ => absurd (xEqX ▸ xEqXb) xNeqXb)
  }

-- TODO move to AProofSystem to other SatisfiesBoundVar stuff.
def Cause.SatisfiesBoundVar.bWithBoundsSatBoundVar
  (b: Valuation Pair)
  (isBoundTo: IsBoundTo boundVars x d)
:
  Cause.SatisfiesBoundVar
    (ofValPos
      (b.withBoundVars boundVars)
      Valuation.empty)
    x
    d
:=
  let eq :=
    Valuation.withBoundVars.eqOfIsBoundTo b isBoundTo
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
  SatisfiesBoundVar.bWithBoundsSatBoundVar b

def Cause.SatisfiesBoundVars.exceptHeadSatTail
  {cause: Cause Pair}
  (boundVarsSat: cause.SatisfiesBoundVars (⟨d, x⟩ :: tail))
:
  (cause.exceptVar x).SatisfiesBoundVars tail
:=
  fun {xx _d} isBoundTail =>
    if h: xx = x then
      {
        cinsSat := fun _ ⟨_, xNeq⟩ xEq => (xNeq (xEq.trans h)).elim
        binsSat := fun _ ⟨_, xNeq⟩ xEq => (xNeq (xEq.trans h)).elim
        boutSat := fun _ ⟨_, xNeq⟩ xEq => (xNeq (xEq.trans h)).elim
      }
    else
      let causeSat :=
        boundVarsSat (IsBoundTo.InTail isBoundTail h _)
      causeSat.toSubCause (Cause.exceptVarIsSub cause x)

-- TODO move to AProofSystem to other SatisfiesBoundVar stuff.
def Cause.SatisfiesBoundVar.withBoundsSatBoundVar
  (v: Valuation Pair)
  (isBoundTo: IsBoundTo boundVars x d)
:
  Cause.SatisfiesBoundVar
    (ofValPos
      (v.withBoundVars boundVars)
      (v.withBoundVars boundVars))
    x
    d
:=
  let eq := Valuation.withBoundVars.eqOfIsBoundTo v isBoundTo
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
  SatisfiesBoundVar.withBoundsSatBoundVar v
