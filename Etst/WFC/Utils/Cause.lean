import Mathlib.Logic.Basic

import Etst.WFC.Ch4_S0_MembershipPs

namespace Etst

variable {D: Type*}


def Cause.eq:
  {a b: Cause D} →
  a.cins = b.cins →
  a.bout = b.bout →
  a = b

| ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

def Cause.empty: Cause D := {
  cins _ := ∅
  bout _ := ∅
}

def Cause.cinsJust
  (x: Nat)
  (d: D)
:
  Cause D
:= {
  cins xx dd := xx = x ∧ dd = d
  bout _ := ∅
}

def Cause.boutJust
  (x: Nat)
  (d: D)
:
  Cause D
:= {
  cins _ := ∅
  bout xx dd := xx = x ∧ dd = d
}

def Cause.union
  (a b: Cause D)
:
  Cause D
:= {
  cins x d := a.cins x d ∨ b.cins x d
  bout x d := a.bout x d ∨ b.bout x d
}

def Cause.arbUn
  {I: Type*}
  (f: I → Cause D)
:
  Cause D
:= {
  -- Originally defining these as follows was a mistake!
  -- 
  -- ```
  --   cins := ⋃ i, (f i).cins,
  --   bout := ⋃ i, (f i).bout,
  -- ```
  -- 
  -- Instead of
  -- 
  --     { d: D | ∃ i: I, d ∈ f i } \,,
  -- 
  -- the arbitrary set union is defined in Mathlib as
  -- 
  --     { d: D | ∃ s: Set D, (∃ i: I, s = f i) ∧ d ∈ s } \,.
  -- 
  -- This is silly. (And yes, it is because it's the result of
  -- instantiating a more general definition to a specific context
  -- where it makes less sense, and that doesn't make it less silly).
  cins x d := ∃ i, (f i).cins x d
  bout x d := ∃ i, (f i).bout x d
}

def Cause.ofValDef
  (b c: Valuation D)
:
  Cause D
:= {
  cins := c.defMembers
  bout := b.defNonMembers
}

def Cause.ofValPos
  (b c: Valuation D)
:
  Cause D
:= {
  cins := c.posMembers
  bout := b.posNonMembers
}

structure Cause.IsSubset
  (a b: Cause D)
:
  Prop
where
  cinsLe: a.cins ≤ b.cins
  boutLe: a.bout ≤ b.bout

instance (D: Type*): HasSubset (Cause D) := ⟨Cause.IsSubset⟩


def Cause.IsWeaklySatisfiedBy.unionElimL
  {a b: Cause D}
  {bg c: Valuation D}
  (isSat: (Cause.union a b).IsWeaklySatisfiedBy bg c)
:
  a.IsWeaklySatisfiedBy bg c
:= {
  cinsSat := fun inCins => isSat.cinsSat (Or.inl inCins)
  boutSat := fun inBout => isSat.boutSat (Or.inl inBout)
}

def Cause.IsWeaklySatisfiedBy.unionElimR
  {a b: Cause D}
  {bg c: Valuation D}
  (isSat: (Cause.union a b).IsWeaklySatisfiedBy bg c)
:
  b.IsWeaklySatisfiedBy bg c
:= {
  cinsSat := fun inCins => isSat.cinsSat (Or.inr inCins)
  boutSat := fun inBout => isSat.boutSat (Or.inr inBout)
}

def Cause.IsWeaklySatisfiedBy.arbUn
  {I: Type*}
  {f: I → Cause D}
  {bg c: Valuation D}
  (allSat: ∀ i, (f i).IsWeaklySatisfiedBy bg c)
:
  (Cause.arbUn f).IsWeaklySatisfiedBy bg c
:= {
  cinsSat := fun ⟨i, inCins⟩ => (allSat i).cinsSat inCins
  boutSat := fun ⟨i, inBout⟩ => (allSat i).boutSat inBout
}

def Cause.IsWeaklySatisfiedBy.arbUnElim
  {I: Type*}
  {f: I → Cause D}
  {bg c: Valuation D}
  (isSat: (Cause.arbUn f).IsWeaklySatisfiedBy bg c)
  (i: I)
:
  (f i).IsWeaklySatisfiedBy bg c
:= {
  cinsSat := fun inCins => isSat.cinsSat ⟨i, inCins⟩
  boutSat := fun inBout => isSat.boutSat ⟨i, inBout⟩
}


/-
  This definition differs from `IsCauseInapplicable` in that it
  is semantic instead of proof-theoretic.
-/
inductive Cause.IsInapplicable
  (cause: Cause D)
  (outSet inSet: Nat → Set D)
:
  Prop
|
  blockedCins {x d}
  (inCins: cause.cins x d)
  (inCycle: outSet x d)
:
  IsInapplicable cause outSet inSet
|
  blockedBout {x d}
  (inBout: cause.bout x d)
  (isIns: inSet x d)
:
  IsInapplicable cause outSet inSet

def Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy
  {cause: Cause D}
  {b c: Valuation D}
  (isApplicable:
    ¬ Cause.IsInapplicable cause c.defNonMembers b.defMembers)
:
  Cause.IsWeaklySatisfiedBy cause b c
:=
  open Cause.IsWeaklySatisfiedBy in
  {
    cinsSat :=
      fun inCins =>
        byContradiction fun notPos =>
          isApplicable (blockedCins inCins notPos)
    boutSat :=
      fun inBout =>
        byContradiction fun isDef =>
          isApplicable (blockedBout inBout isDef.dne)
  }

def Cause.IsInapplicable.Not.union
  {a b: Cause D}
  {outSet inSet: Nat → Set D}
  (aIsApp: ¬ Cause.IsInapplicable a outSet inSet)
  (bIsApp: ¬ Cause.IsInapplicable b outSet inSet)
  (abIsInapp: Cause.IsInapplicable (a.union b) outSet inSet)
:
  False
:=
  match abIsInapp with
  | .blockedCins (Or.inl inCins) inCycle =>
    aIsApp (.blockedCins inCins inCycle)
  | .blockedCins (Or.inr inCins) inCycle =>
    bIsApp (.blockedCins inCins inCycle)
  | .blockedBout (Or.inl inBout) isIns =>
    aIsApp (.blockedBout inBout isIns)
  | .blockedBout (Or.inr inBout) isIns =>
    bIsApp (.blockedBout inBout isIns)

def Cause.IsInapplicable.Not.arbUn
  {I: Type*}
  {causes: I → Cause D}
  {outSet inSet: Nat → Set D}
  (isApp: ∀ i, ¬ Cause.IsInapplicable (causes i) outSet inSet)
  (isInapp: Cause.IsInapplicable (Cause.arbUn causes) outSet inSet)
:
  False
:=
  match isInapp with
  | .blockedCins ⟨i, inCins⟩ inCycle =>
    isApp i (.blockedCins inCins inCycle)
  | .blockedBout ⟨i, inBout⟩ isIns =>
    isApp i (.blockedBout inBout isIns)

def Cause.IsWeaklySatisfiedBy.toIsApplicable
  {cause b c}
  (isSat: Cause.IsWeaklySatisfiedBy cause b c)
  (outSet: Nat → Set D)
  (outSetIsEmpty: ∀ {x d}, outSet x d → ¬ (c x).posMem d)
:
  ¬ Cause.IsInapplicable cause outSet b.defMembers
|
  .blockedCins inCins inOutSet =>
    outSetIsEmpty inOutSet (isSat.cinsSat inCins)
|
  .blockedBout inBout isDef =>
    isSat.boutSat inBout isDef

def Cause.IsWeaklySatisfiedBy.ofValPos
  (b c: Valuation D)
:
  (Cause.ofValPos b c).IsWeaklySatisfiedBy b c
:= {
  cinsSat := id
  boutSat := id
}


def Cause.IsWeakCauseFv.ofValPos {expr fv b c d}
  (isPos: (expr.triIntp2 fv b c).posMem d)
:
  (Cause.ofValPos b c).IsWeakCauseFv fv expr d
:=
  fun _ _ isSat =>
    BasicExpr.triIntp2_mono_std_posMem
      (fun _ _ isDef => byContradiction (isSat.boutSat · isDef))
      (fun _ _ => isSat.cinsSat)
      isPos

def Cause.IsStrongCauseFv.ofValDef {expr fv b c d}
  (isDef: (expr.triIntp2 fv b c).defMem d)
:
  (Cause.ofValDef b c).IsStrongCauseFv fv expr d
:=
  fun _ _ isSat =>
    BasicExpr.triIntp2_mono_std_defMem
      (fun _ _ isDef => byContradiction (isSat.boutSat · isDef))
      (fun _ _ => isSat.cinsSat)
      isDef


def Cause.IsWeakCauseFv.isPosOfIsApplicable {fv d expr}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv expr d)
  {b c}
  (isApp: ¬ cause.IsInapplicable c.defNonMembers b.defMembers)
:
  (expr.triIntp2 fv b c).posMem d
:=
  isCause (Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy isApp)

def Cause.IsWeakCauseFv.isInapplicableOfIsNonmember {fv d expr}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv expr d)
  {b c: Valuation Pair}
  (notPos: ¬(expr.triIntp2 fv b c).posMem d)
:
  cause.IsInapplicable c.defNonMembers b.defMembers
:=
  (not_imp_not.mpr (isPosOfIsApplicable isCause) notPos).dne


/-
  The least valuation in the approximation order that strongly
  satisfies the background part of a cause.
-/
def Cause.leastBackgroundApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := ∅
    posMem := compl ∘ cause.bout x
    defLePos := nofun
  }

/-
  The least valuation in the approximation order that strongly
  satisfies the context part of a cause.
-/
def Cause.leastContextApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := cause.cins x
    posMem := Set.univ
    defLePos _ _ := trivial
  }

def Cause.leastValsApxAreSat
  (cause: Cause D)
:
  cause.IsStronglySatisfiedBy
    cause.leastBackgroundApx
    cause.leastContextApx
:= {
  cinsSat := id
  boutSat := Function.eval
}


/-
  A maximal valuation in the approximation order that weakly
  satisfies the background part of a cause.
-/
def Cause.maximalBackgroundApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := compl ∘ cause.bout x
    posMem := compl ∘ cause.bout x
    defLePos _ := id
  }

/-
  A maximal valuation in the approximation order that weakly
  satisfies the context part of a cause.
-/
def Cause.maximalContextApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := cause.cins x
    posMem := cause.cins x
    defLePos _ := id
  }

def Cause.maximalValsApxAreSat
  (cause: Cause D)
:
  cause.IsWeaklySatisfiedBy
    cause.maximalBackgroundApx
    cause.maximalContextApx
:= {
  cinsSat := id
  boutSat := Function.eval
}


def Cause.IsStrongCauseFv.ofLeastCompl {fv expr d}
  {cause: Cause Pair}
  (notPos:
    ¬ expr.triIntp2Pos fv cause.leastContextApx cause.leastBackgroundApx d)
:
  cause.IsStrongCauseFv fv (.compl expr) d
:=
  fun _ c isSat =>
    let bgLe: cause.leastContextApx ⊑ c :=
      fun _ => {
        defLe _ := isSat.cinsSat
        posLe _ _ := trivial
      }
    let posLe :=
      BasicExpr.triIntp2_mono_apx_posMem
        (expr := expr)
        (c0 := cause.leastBackgroundApx)
        bgLe
        (fun _ _ isPos inBout => isSat.boutSat inBout isPos)
    fun isPos => notPos (posLe isPos)


def Cause.IsWeakCauseFv.const {fv x d}:
  IsWeakCauseFv (Cause.cinsJust x d) fv (.const x) d
:=
  fun _ _ isSat => isSat.cinsSat ⟨rfl, rfl⟩

def Cause.IsWeakCauseFv.constElim {fv x d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.const x) d)
:
  cause.cins x d
:=
  isCause cause.maximalValsApxAreSat

def Cause.IsWeakCauseFv.complConst {fv x d}:
   IsWeakCauseFv (Cause.boutJust x d) fv (.compl (.const x)) d
:=
  fun _ _ isSat => isSat.boutSat ⟨rfl, rfl⟩

def Cause.IsWeakCauseFv.complConstElim {fv x d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.compl (.const x)) d)
:
  cause.bout x d
:=
  (isCause cause.maximalValsApxAreSat).dne

def Cause.IsStrongCauseFv.const {fv x d}:
  IsStrongCauseFv (Cause.cinsJust x d) fv (.const x) d
:=
  fun _ _ isSat => isSat.cinsSat ⟨rfl, rfl⟩

def Cause.IsStrongCauseFv.constElim {fv x d}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv (.const x) d)
:
  cause.cins x d
:=
  isCause cause.leastValsApxAreSat

def Cause.IsStrongCauseFv.complConstElim {fv x d}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv (.compl (.const x)) d)
:
  cause.bout x d
:=
  (isCause cause.leastValsApxAreSat).dne


def Cause.IsWeakCauseFv.pair {fv l r pL pR}
  {causeL causeR: Cause Pair}
  (leftIsCause: causeL.IsWeakCauseFv fv l pL)
  (riteIsCause: causeR.IsWeakCauseFv fv r pR)
:
  (causeL.union causeR).IsWeakCauseFv fv (.pair l r) (.pair pL pR)
:=
  fun _ _ isSat => ⟨
    pL,
    pR,
    rfl,
    leftIsCause isSat.unionElimL,
    riteIsCause isSat.unionElimR,
  ⟩

def Cause.IsWeakCauseFv.complPairElim {fv l r pL pR}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.compl (.pair l r)) (.pair pL pR))
  (b c: Valuation Pair)
:
  Or
    ((cause.union (Cause.ofValPos b c)).IsWeakCauseFv fv (.compl l) pL)
    ((cause.union (Cause.ofValPos b c)).IsWeakCauseFv fv (.compl r) pR)
:=
  let causeUn := cause.union (Cause.ofValPos b c)
  let isSat := causeUn.maximalValsApxAreSat.unionElimL
  match not_and_or.mp (fun inPair => isCause isSat ⟨pL, pR, rfl, inPair.left, inPair.right⟩) with
  | Or.inl isPosL =>
    Or.inl (fun _ _ isSat =>
      BasicExpr.triIntp2_mono_std_posMem
        (expr := .compl l)
        (b0 := causeUn.maximalBackgroundApx)
        (c0 := causeUn.maximalContextApx)
        (fun _ _ inDef inBout => isSat.boutSat inBout inDef)
        (fun _ _ inCins => isSat.cinsSat inCins)
        isPosL)
  | Or.inr isPosR =>
    Or.inr (fun _ _ isSat =>
      BasicExpr.triIntp2_mono_std_posMem
        (expr := .compl r)
        (b0 := causeUn.maximalBackgroundApx)
        (c0 := causeUn.maximalContextApx)
        (fun _ _ inDef inBout => isSat.boutSat inBout inDef)
        (fun _ _ inCins => isSat.cinsSat inCins)
        isPosR)

def Cause.IsStrongCauseFv.complPairElim {fv l r pL pR}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv (.compl (.pair l r)) (.pair pL pR))
:
  Or
    (cause.IsStrongCauseFv fv (.compl l) pL)
    (cause.IsStrongCauseFv fv (.compl r) pR)
:=
  match
    not_and_or.mp
      (fun inPair =>
        isCause cause.leastValsApxAreSat
          ⟨pL, pR, rfl, inPair.left, inPair.right⟩)
  with
  | Or.inl notPosL => Or.inl (Cause.IsStrongCauseFv.ofLeastCompl notPosL)
  | Or.inr notPosR => Or.inr (Cause.IsStrongCauseFv.ofLeastCompl notPosR)


def Cause.IsWeakCauseFv.ir {fv l r d}
  {causeL causeR: Cause Pair}
  (leftIsCause: causeL.IsWeakCauseFv fv l d)
  (riteIsCause: causeR.IsWeakCauseFv fv r d)
:
  (causeL.union causeR).IsWeakCauseFv fv (.ir l r) d
:=
  fun _ _ isSat => ⟨
    leftIsCause isSat.unionElimL,
    riteIsCause isSat.unionElimR,
  ⟩

def Cause.IsWeakCauseFv.complIrElim {fv l r d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.compl (.ir l r)) d)
  (b c: Valuation Pair)
:
  Or
    ((cause.union (Cause.ofValPos b c)).IsWeakCauseFv fv (.compl l) d)
    ((cause.union (Cause.ofValPos b c)).IsWeakCauseFv fv (.compl r) d)
:=
  let causeUn := cause.union (Cause.ofValPos b c)
  let isSat := causeUn.maximalValsApxAreSat.unionElimL
  match not_and_or.mp (isCause isSat) with
  | Or.inl isPosL =>
    Or.inl (fun _ _ isSat =>
      BasicExpr.triIntp2_mono_std_posMem
        (expr := .compl l)
        (b0 := causeUn.maximalBackgroundApx)
        (c0 := causeUn.maximalContextApx)
        (fun _ _ inDef inBout => isSat.boutSat inBout inDef)
        (fun _ _ inCins => isSat.cinsSat inCins)
        isPosL)
  | Or.inr isPosR =>
    Or.inr (fun _ _ isSat =>
      BasicExpr.triIntp2_mono_std_posMem
        (expr := .compl r)
        (b0 := causeUn.maximalBackgroundApx)
        (c0 := causeUn.maximalContextApx)
        (fun _ _ inDef inBout => isSat.boutSat inBout inDef)
        (fun _ _ inCins => isSat.cinsSat inCins)
        isPosR)

def Cause.IsStrongCauseFv.complIrElim {fv l r d}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv (.compl (.ir l r)) d)
:
  Or
    (cause.IsStrongCauseFv fv (.compl l) d)
    (cause.IsStrongCauseFv fv (.compl r) d)
:=
  match not_and_or.mp (isCause cause.leastValsApxAreSat) with
  | Or.inl notPosL => Or.inl (Cause.IsStrongCauseFv.ofLeastCompl notPosL)
  | Or.inr notPosR => Or.inr (Cause.IsStrongCauseFv.ofLeastCompl notPosR)

def Cause.IsWeakCauseFv.complFullElim {fv body d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.compl (.full body)) d)
  (b c: Valuation Pair)
:
  ∃ dB,
    ((cause.union (Cause.ofValPos b c)).IsWeakCauseFv
      fv
      (.compl body)
      dB)
:=
  let causeUn := cause.union (Cause.ofValPos b c)
  let isSat := causeUn.maximalValsApxAreSat.unionElimL
  match Classical.not_forall.mp (isCause isSat) with
  | ⟨dB, notDefBody⟩ =>
    ⟨dB, fun _ _ isSat =>
      BasicExpr.triIntp2_mono_std_posMem
        (expr := body.compl)
        (b0 := causeUn.maximalBackgroundApx)
        (c0 := causeUn.maximalContextApx)
        (fun _ _ inDef inBout => isSat.boutSat inBout inDef)
        (fun _ _ inCins => isSat.cinsSat inCins)
        notDefBody⟩

def Cause.IsWeakCauseFv.complCompl {fv body d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv body d)
:
  cause.IsWeakCauseFv fv (.compl (.compl body)) d
:=
  open SingleLaneExpr in
  fun _ _ isSat => inCompl (ninCompl (isCause isSat))

def Cause.IsWeakCauseFv.complComplElim {fv body d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.compl (.compl body)) d)
:
  cause.IsWeakCauseFv fv body d
:=
  fun _ _ isSat => (isCause isSat).dne

def Cause.IsWeakCauseFv.complArbIrElim {fv body d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv (.compl (.arbIr body)) d)
  (b c: Valuation Pair)
:
  ∃ dX,
    ((cause.union (Cause.ofValPos b c)).IsWeakCauseFv
      (dX :: fv)
      (.compl body)
      d)
:=
  let causeUn := cause.union (Cause.ofValPos b c)
  let isSat := causeUn.maximalValsApxAreSat.unionElimL
  match Classical.not_forall.mp (isCause isSat) with
  | ⟨dX, notDefBody⟩ =>
    ⟨dX, fun _ _ isSat =>
      BasicExpr.triIntp2_mono_std_posMem
        (expr := body.compl)
        (b0 := causeUn.maximalBackgroundApx)
        (c0 := causeUn.maximalContextApx)
        (fun _ _ inDef inBout => isSat.boutSat inBout inDef)
        (fun _ _ inCins => isSat.cinsSat inCins)
        notDefBody⟩


def Cause.IsWeakCauseFv.noneElim {fv d}
  {cause: Cause Pair}
  (isCause: cause.IsWeakCauseFv fv .none d)
  {P: Prop}
:
  P
:=
  SingleLaneExpr.inNoneElim
    (isCause cause.maximalValsApxAreSat)

def Cause.IsStrongCauseFv.noneElim {fv d}
  {cause: Cause Pair}
  (isCause: cause.IsStrongCauseFv fv .none d)
  {P: Prop}
:
  P
:=
  SingleLaneExpr.inNoneElim
    (isCause cause.leastValsApxAreSat)
