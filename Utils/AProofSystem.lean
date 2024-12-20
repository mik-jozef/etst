/-
  This files contains the helper definitions and lemmas for the
  chapter 6, plus related utility defs for later chapters.
-/

import WFC.Ch6_S0_AProofSystem

set_option linter.unusedVariables false


def ValVar.eq: d0 = d1 → x0 = x1 → ValVar.mk d0 x0 = ⟨d1, x1⟩
| rfl, rfl => rfl

def ValVar.eqX: @Eq (ValVar D) ⟨d0, x0⟩ ⟨d1, x1⟩ → x0 = x1
| rfl => rfl

-- The (definite) nonmembers of a valuation.
def Valuation.nonmembers
  (v: Valuation D)
:
  Set (ValVar D)
:=
  fun ⟨d, x⟩ => ¬ (v x).posMem d


def Cause.empty: Cause D := {
  contextIns := ∅
  backgroundIns := ∅
  backgroundOut := ∅
}

def Cause.eq:
  {a b: Cause D} →
  a.contextIns = b.contextIns →
  a.backgroundIns = b.backgroundIns →
  a.backgroundOut = b.backgroundOut →
  a = b

| ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

structure Cause.IsSubset
  (a b: Cause D)
:
  Prop
where
  cinsLe: a.contextIns ⊆ b.contextIns
  binsLe: a.backgroundIns ⊆ b.backgroundIns
  boutLe: a.backgroundOut ⊆ b.backgroundOut

def Cause.var (x: Nat) (d: D): Cause D := {
  contextIns := fun ⟨dd, xx⟩ => dd = d ∧ xx = x
  backgroundIns := ∅
  backgroundOut := ∅
}

def Cause.union (c1 c2: Cause D): Cause D := {
  contextIns := c1.contextIns ∪ c2.contextIns,
  backgroundIns := c1.backgroundIns ∪ c2.backgroundIns,
  backgroundOut := c1.backgroundOut ∪ c2.backgroundOut,
}

instance (D: Type*): Union (Cause D) := ⟨Cause.union⟩
instance (D: Type*): HasSubset (Cause D) := ⟨Cause.IsSubset⟩

def Cause.arbUn (f: I → Cause D): Cause D := {
  -- Originally defining these as follows was a mistake!
  -- 
  -- ```
  --   contextIns := ⋃ i, (f i).contextIns,
  --   backgroundIns := ⋃ i, (f i).backgroundIns,
  --   backgroundOut := ⋃ i, (f i).backgroundOut,
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
  -- This is silly.
  
  contextIns := fun vv => ∃ i, vv ∈ (f i).contextIns,
  backgroundIns := fun vv => ∃ i, vv ∈ (f i).backgroundIns,
  backgroundOut := fun vv => ∃ i, vv ∈ (f i).backgroundOut,
}

def Cause.exceptX
  (cause: Cause D)
  (x: Nat)
:
  Cause D
:= {
  contextIns := cause.contextIns \ fun vv => vv.x = x
  backgroundIns := cause.backgroundIns \ fun vv => vv.x = x
  backgroundOut :=
    cause.backgroundOut \ fun vv => vv.x = x
}

def Cause.exceptXIsSub
  (cause: Cause D)
  (x: Nat)
:
  cause.exceptX x ⊆ cause
:= {
  cinsLe := fun _ => And.left
  binsLe := fun _ => And.left
  boutLe := fun _ => And.left
}

def Cause.exceptBound
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  Cause D
:= {
  contextIns := cause.contextIns \ {⟨d, x⟩}
  backgroundIns := cause.backgroundIns \ {⟨d, x⟩}
  backgroundOut :=
    cause.backgroundOut \ fun ⟨dd, xx⟩ => dd ≠ d ∧ xx = x
}

def Cause.withBound
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  Cause D
:= {
  contextIns :=
    fun ⟨dd, xx⟩ =>
      Or
        (cause.contextIns ⟨dd, xx⟩ ∧ xx ≠ x)
        (dd = d ∧ xx = x)
  backgroundIns :=
    fun ⟨dd, xx⟩ =>
      Or
        (cause.backgroundIns ⟨dd, xx⟩ ∧ xx ≠ x)
        (dd = d ∧ xx = x)
  backgroundOut :=
    fun ⟨dd, xx⟩ =>
      Or
        (cause.backgroundOut ⟨dd, xx⟩ ∧ xx ≠ x)
        (dd ≠ d ∧ xx = x)
}

def Cause.withBoundCancelsPrevious
  (cause: Cause D)
  (x: Nat)
  (dA dB: D)
:
  (cause.withBound x dA).withBound x dB = cause.withBound x dB
:=
  Cause.eq
    (funext fun ⟨dd, xx⟩ =>
      propext
        (Iff.intro
          (fun inCinsAB =>
            inCinsAB.elim
              (fun ⟨inCinsA, xNeq⟩ =>
                inCinsA.elim
                  Or.inl
                  (False.elim ∘ xNeq ∘ And.right))
              Or.inr)
          (fun inCinsB =>
            inCinsB.elim
              (fun ⟨inCins, xNeq⟩ =>
                Or.inl ⟨(Or.inl ⟨inCins, xNeq⟩), xNeq⟩)
              Or.inr)))
    (funext fun ⟨dd, xx⟩ =>
      propext
        (Iff.intro
          (fun inBinsAB =>
            inBinsAB.elim
              (fun ⟨inBinsA, xNeq⟩ =>
                inBinsA.elim
                  Or.inl
                  (False.elim ∘ xNeq ∘ And.right))
              Or.inr)
          (fun inBinsB =>
            inBinsB.elim
              (fun ⟨inBins, xNeq⟩ =>
                Or.inl ⟨(Or.inl ⟨inBins, xNeq⟩), xNeq⟩)
              Or.inr)))
    (funext fun ⟨dd, xx⟩ =>
      propext
        (Iff.intro
          (fun inBoutAB =>
            inBoutAB.elim
              (fun ⟨inBoutA, xNeq⟩ =>
                inBoutA.elim
                  Or.inl
                  (False.elim ∘ xNeq ∘ And.right))
              Or.inr)
          (fun inBoutB =>
            inBoutB.elim
              (fun ⟨inBout, xNeq⟩ =>
                Or.inl ⟨(Or.inl ⟨inBout, xNeq⟩), xNeq⟩)
              Or.inr)))

def Cause.inCinsOfInWithAndNotBound
  {cause: Cause D}
  (inCinsWith: ⟨d, x⟩ ∈ (cause.withBound xB dB).contextIns)
  (xNeq: x ≠ xB)
:
  ⟨d, x⟩ ∈ cause.contextIns
:=
  inCinsWith.elim
    (fun ⟨inCins, _⟩ => inCins)
    (fun ⟨_, xEq⟩ => absurd xEq xNeq)

def Cause.inBinsOfInWithAndNotBound
  {cause: Cause D}
  (inBinsWith: ⟨d, x⟩ ∈ (cause.withBound xB dB).backgroundIns)
  (xNeq: x ≠ xB)
:
  ⟨d, x⟩ ∈ cause.backgroundIns
:=
  inBinsWith.elim
    (fun ⟨inBins, _⟩ => inBins)
    (fun ⟨_, xEq⟩ => absurd xEq xNeq)

def Cause.inBoutOfInWithAndNotBound
  {cause: Cause D}
  (inBoutWith: ⟨d, x⟩ ∈ (cause.withBound xB dB).backgroundOut)
  (xNeq: x ≠ xB)
:
  ⟨d, x⟩ ∈ cause.backgroundOut
:=
  inBoutWith.elim
    (fun ⟨inBout, _⟩ => inBout)
    (fun ⟨_, xEq⟩ => absurd xEq xNeq)

def Cause.background
  (cause: Cause D)
:
  Cause D
:= {
  contextIns := Set.empty
  backgroundIns := cause.backgroundIns
  backgroundOut := cause.backgroundOut
}


structure Cause.SatisfiesBoundVar
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  Prop
where
  cinsSat:
    ∀ vv ∈ cause.contextIns, vv.x = x → vv.d = d
  binsSat:
    ∀ vv ∈ cause.backgroundIns, vv.x = x → vv.d = d
  boutSat:
    ∀ vv ∈ cause.backgroundOut, vv.x = x → vv.d ≠ d

def Cause.SatisfiesBoundVar.ninBinsBout
  {cause: Cause D}
  (sat: cause.SatisfiesBoundVar x dBound)
  (d: D)
:
  ⟨d, x⟩ ∉ cause.backgroundIns ∨ ⟨d, x⟩ ∉ cause.backgroundOut
:=
  if h: ⟨d, x⟩ ∈ cause.backgroundIns then
    let dEq := sat.binsSat ⟨d, x⟩ h rfl
    Or.inr (sat.boutSat _ · rfl dEq)
  else
    Or.inl h

def Cause.SatisfiesBoundVar.union
  {causeL causeR: Cause D}
  (satL: causeL.SatisfiesBoundVar x dBound)
  (satR: causeR.SatisfiesBoundVar x dBound)
:
  (causeL ∪ causeR).SatisfiesBoundVar x dBound
:= {
  cinsSat :=
    fun vv inCins xEq =>
      inCins.elim
        (fun inCinsL =>
          satL.cinsSat vv inCinsL xEq)
        (fun inCinsR =>
          satR.cinsSat vv inCinsR xEq),
  binsSat :=
    fun vv inBins xEq =>
      inBins.elim
        (fun inBinsL =>
          satL.binsSat vv inBinsL xEq)
        (fun inBinsR =>
          satR.binsSat vv inBinsR xEq),
  boutSat :=
    fun vv inBout xEq =>
      inBout.elim
        (fun inBoutL =>
          satL.boutSat vv inBoutL xEq)
        (fun inBoutR =>
          satR.boutSat vv inBoutR xEq),
}

def Cause.SatisfiesBoundVar.leWithBound
  {cause: Cause D}
  (sat: cause.SatisfiesBoundVar x d)
:
  cause ⊆ cause.withBound x d
:= {
  cinsLe :=
    fun vv inCins =>
      if h: vv.x = x then
        Or.inr ⟨sat.cinsSat vv inCins h, h⟩
      else
        Or.inl ⟨inCins, h⟩
  binsLe :=
    fun vv inBins =>
      if h: vv.x = x then
        Or.inr ⟨sat.binsSat vv inBins h, h⟩
      else
        Or.inl ⟨inBins, h⟩
  boutLe :=
    fun vv inBout =>
      if h: vv.x = x then
        Or.inr ⟨sat.boutSat vv inBout h, h⟩
      else
        Or.inl ⟨inBout, h⟩
}

def Cause.SatisfiesBoundVar.toSubCause
  {cause: Cause D}
  (sat: cause.SatisfiesBoundVar x d)
  (isLe: subcause ⊆ cause)
:
  subcause.SatisfiesBoundVar x d
:= {
  cinsSat :=
    fun vv inCins xEq =>
      sat.cinsSat vv (isLe.cinsLe inCins) xEq
  binsSat :=
    fun vv inBins xEq =>
      sat.binsSat vv (isLe.binsLe inBins) xEq
  boutSat :=
    fun vv inBout xEq =>
      sat.boutSat vv (isLe.boutLe inBout) xEq
}


/-
  This definition differs from `IsCauseInapplicable` in that it
  is semantic instead of proof-theoretic.
-/
inductive Cause.IsInapplicable
  (cause: Cause D)
  (outSet: Set (ValVar D))
  (b: Valuation D)
:
  Prop

| blockedContextIns
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ outSet)
:
  IsInapplicable cause outSet b

| blockedBackgroundIns
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: ¬(b x).posMem d)
:
  IsInapplicable cause outSet b

| blockedBackgroundOut
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: (b x).defMem d)
:
  IsInapplicable cause outSet b

-- Note: Accepts a negation of IsInapplicable
def Cause.IsInapplicable.toIsWeaklySatisfiedBy
  {cause: Cause D}
  {b c: Valuation D}
  (isApplicable: ¬ Cause.IsInapplicable cause c.nonmembers b)
:
  Cause.IsWeaklySatisfiedBy cause b c
:=
  open Cause.IsWeaklySatisfiedBy in
  {
    contextInsHold :=
      fun inCins =>
        byContradiction fun notPos =>
          isApplicable (blockedContextIns inCins notPos)
    backgroundInsHold :=
      fun inBins =>
        byContradiction fun notPos =>
          isApplicable (blockedBackgroundIns inBins notPos)
    backgroundOutHold :=
      fun inBout =>
        byContradiction fun isDef =>
          isApplicable (blockedBackgroundOut inBout isDef.dne)
  }

-- Note: Accepts a negation of IsWeaklySatisfiedBy
def Cause.IsWeaklySatisfiedBy.toIsInapplicable
  {cause: Cause D}
  {b c: Valuation D}
  (notSat: ¬ Cause.IsWeaklySatisfiedBy cause b c)
:
  Cause.IsInapplicable cause c.nonmembers b
:=
  Function.contraA
    Cause.IsInapplicable.toIsWeaklySatisfiedBy
    notSat

def Cause.IsWeaklySatisfiedBy.toIsApplicable
  {b c: Valuation D}
  (isSat: Cause.IsWeaklySatisfiedBy cause b c)
  (outSet: Set (ValVar D))
  (outSetIsEmpty: ∀ {d x}, ⟨d, x⟩ ∈ outSet → ¬ (c x).posMem d)
:
  ¬ Cause.IsInapplicable cause outSet b

| IsInapplicable.blockedContextIns inCins inOutSet =>
  outSetIsEmpty inOutSet (isSat.contextInsHold inCins)

| IsInapplicable.blockedBackgroundIns inBins notPos =>
  notPos (isSat.backgroundInsHold inBins)

| IsInapplicable.blockedBackgroundOut inBout isDef =>
  isSat.backgroundOutHold inBout isDef

def Cause.IsWeaklySatisfiedBy.union
  (isSatLeft: Cause.IsWeaklySatisfiedBy causeLeft b c)
  (isSatRite: Cause.IsWeaklySatisfiedBy causeRite b c)
:
  (causeLeft ∪ causeRite).IsWeaklySatisfiedBy b c
:= {
  contextInsHold :=
    fun inCins =>
      inCins.elim
        isSatLeft.contextInsHold
        isSatRite.contextInsHold,
  backgroundInsHold :=
    fun inBins =>
      inBins.elim
        isSatLeft.backgroundInsHold
        isSatRite.backgroundInsHold,
  backgroundOutHold :=
    fun inBout =>
      inBout.elim
        isSatLeft.backgroundOutHold
        isSatRite.backgroundOutHold,
}

def Cause.IsWeaklySatisfiedBy.ofSuper
  (isSat: Cause.IsWeaklySatisfiedBy causeSuper b c)
  (le: cause ⊆ causeSuper)
:
  Cause.IsWeaklySatisfiedBy cause b c
:= {
  contextInsHold :=
    fun inCins => isSat.contextInsHold (le.cinsLe inCins)
  backgroundInsHold :=
    fun inBins => isSat.backgroundInsHold (le.binsLe inBins)
  backgroundOutHold :=
    fun inBout => isSat.backgroundOutHold (le.boutLe inBout)
}


def IsWeakCause.union
  (isCauseLeft: IsWeakCause salg causeLeft d exprLeft)
  (isCauseRite: IsWeakCause salg causeRite d exprRite)
:
  IsWeakCause
    salg
    (causeLeft ∪ causeRite)
    d
    (Expr.ir exprLeft exprRite)
:=
  fun isSat =>
    And.intro
      (isCauseLeft {
        contextInsHold := isSat.contextInsHold ∘ Or.inl
        backgroundInsHold := isSat.backgroundInsHold ∘ Or.inl
        backgroundOutHold := isSat.backgroundOutHold ∘ Or.inl
      })
      (isCauseRite {
        contextInsHold := isSat.contextInsHold ∘ Or.inr
        backgroundInsHold := isSat.backgroundInsHold ∘ Or.inr
        backgroundOutHold := isSat.backgroundOutHold ∘ Or.inr
      })

noncomputable def IsWeakCause.exSatOfIsPos
  {expr: Expr sig}
  (isPos: (expr.interpretation salg b c).posMem d)
:
  { cause // IsWeakCause salg cause d expr ∧ cause.IsWeaklySatisfiedBy b c }
:=
  match expr with
  | Expr.var x => ⟨
    {
      contextIns := fun ⟨dd, xx⟩ => dd = d ∧ xx = x
      backgroundIns := ∅
      backgroundOut := ∅
    },
    (fun isSat => isSat.contextInsHold ⟨rfl, rfl⟩),
    {
      contextInsHold := fun ⟨dEq, xEq⟩ => dEq ▸ xEq ▸ isPos
      backgroundInsHold := False.elim
      backgroundOutHold := False.elim
    },
  ⟩
  
  | Expr.op op args =>
    let posMem param :=
      ((args param).interpretation salg b c).posMem
    
    let causes (param: sig.Params op) (d: posMem param) :=
      exSatOfIsPos d.property
    
    ⟨
      Cause.arbUn fun (i: Σ param, posMem param) =>
        let ⟨param, d⟩ := i
        causes param d,
      fun {b1 c1} isSat =>
        let posMem1 param :=
          ((args param).interpretation salg b1 c1).posMem
        
        let posMemLe param: posMem param ≤ posMem1 param :=
          fun dd isPos =>
            (causes param ⟨dd, isPos⟩).property.left {
              contextInsHold :=
                fun inCins =>
                  isSat.contextInsHold
                    ⟨⟨param, dd, isPos⟩, inCins⟩
              backgroundInsHold :=
                fun inBins =>
                  isSat.backgroundInsHold
                    ⟨⟨param, dd, isPos⟩, inBins⟩
              backgroundOutHold :=
                fun inBout =>
                  isSat.backgroundOutHold
                    ⟨⟨param, dd, isPos⟩, inBout⟩
            }
        
        salg.isMonotonic op posMem posMem1 posMemLe isPos,
      {
        contextInsHold :=
          fun {dd xx} ⟨⟨param, d⟩, inCins⟩ =>
            (causes param d).property.right.contextInsHold inCins
        backgroundInsHold :=
          fun {dd xx} ⟨⟨param, d⟩, inBins⟩ =>
            (causes param d).property.right.backgroundInsHold inBins
        backgroundOutHold :=
          fun {dd xx} ⟨⟨param, d⟩, inBout⟩ =>
            (causes param d).property.right.backgroundOutHold inBout
      },
    ⟩
  | Expr.un left rite =>
    if hL: (left.interpretation salg b c).posMem d then
      let ⟨cause, isCause, isSat⟩ := exSatOfIsPos hL
      ⟨cause, Or.inl ∘ isCause, isSat⟩
    else if hR: (rite.interpretation salg b c).posMem d then
      let ⟨cause, isCause, isSat⟩ := exSatOfIsPos hR
      ⟨cause, Or.inr ∘ isCause, isSat⟩
    else
      (isPos.elim hL hR).elim
  | Expr.ir left rite =>
    let ⟨causeLeft, isCauseLeft, isSatLeft⟩ := exSatOfIsPos isPos.left
    let ⟨causeRite, isCauseRite, isSatRite⟩ := exSatOfIsPos isPos.right
    
    ⟨
      Cause.union causeLeft causeRite,
      isCauseLeft.union isCauseRite,
      isSatLeft.union isSatRite,
    ⟩
  | Expr.cpl expr =>
    ⟨
      {
        contextIns := ∅
        backgroundIns := fun ⟨d, x⟩ => (b x).posMem d
        backgroundOut := fun ⟨d, x⟩ => ¬(b x).defMem d
      },
      fun {b1 c1} isSat =>
        let isLe: b1 ⊑ b :=
          fun x => {
            defLe := fun d isDef =>
              byContradiction fun notDef =>
                isSat.backgroundOutHold notDef isDef
            posLe := fun _ => isSat.backgroundInsHold
          }
        
        let isMono :=
          Expr.interpretation.isMonotonic.approximation
            salg expr.cpl isLe isLe
        
        isMono.posLe isPos,
      {
        contextInsHold := False.elim
        backgroundInsHold := id
        backgroundOutHold := id
      },
    ⟩
  | Expr.ifThen cond body =>
    let ⟨dC, isPosCond⟩ := isPos.left.unwrap
    let ⟨causeCond, isCauseCond, isSatCond⟩ := exSatOfIsPos isPosCond
    let ⟨causeBody, isCauseBody, isSatBody⟩ := exSatOfIsPos isPos.right
    
    ⟨
      Cause.union causeCond causeBody,
      fun isSat =>
        And.intro
          ⟨
            dC,
            (isCauseCond {
              contextInsHold := isSat.contextInsHold ∘ Or.inl
              backgroundInsHold := isSat.backgroundInsHold ∘ Or.inl
              backgroundOutHold := isSat.backgroundOutHold ∘ Or.inl
            })
          ⟩
          (isCauseBody {
            contextInsHold := isSat.contextInsHold ∘ Or.inr
            backgroundInsHold := isSat.backgroundInsHold ∘ Or.inr
            backgroundOutHold := isSat.backgroundOutHold ∘ Or.inr
          }),
      {
        contextInsHold :=
          fun inCins =>
            inCins.elim
              isSatCond.contextInsHold
              isSatBody.contextInsHold,
        backgroundInsHold :=
          fun inBins =>
            inBins.elim
              isSatCond.backgroundInsHold
              isSatBody.backgroundInsHold,
        backgroundOutHold :=
          fun inBout =>
            inBout.elim
              isSatCond.backgroundOutHold
              isSatBody.backgroundOutHold,
      },
    ⟩
  | Expr.Un x body =>
    let ⟨dX, isPosBody⟩ := isPos.unwrap
    let ⟨causeBody, isCauseBody, isSatBody⟩ := exSatOfIsPos isPosBody
    ⟨
      causeBody.exceptBound x dX,
      fun isSat =>
        ⟨
          dX,
          isCauseBody {
            contextInsHold :=
              fun {dd xx} inCins =>
                if h: x = xx then
                  Valuation.update.eqBoundOfEq _ h dX ▸
                  Valuation.update.eqBoundOfEq c h dX ▸
                  isSatBody.contextInsHold inCins
                else
                  Valuation.update.eqOrig _ h _ ▸
                  isSat.contextInsHold
                    ⟨inCins, h ∘ Eq.symm ∘ ValVar.eqX⟩
            backgroundInsHold :=
              fun {dd xx} inBins =>
                if h: x = xx then
                  Valuation.update.eqBoundOfEq _ h dX ▸
                  Valuation.update.eqBoundOfEq b h dX ▸
                  isSatBody.backgroundInsHold inBins
                else
                  Valuation.update.eqOrig _ h _ ▸
                  isSat.backgroundInsHold
                    ⟨inBins, h ∘ Eq.symm ∘ ValVar.eqX⟩
            backgroundOutHold :=
              fun {dd xx} inBout =>
                if h: x = xx then
                  Valuation.update.eqBoundOfEq _ h dX ▸
                  Valuation.update.eqBoundOfEq b h dX ▸
                  isSatBody.backgroundOutHold inBout
                else
                  Valuation.update.eqOrig _ h _ ▸
                  isSat.backgroundOutHold
                    ⟨inBout, fun ⟨_, eqX⟩ => h eqX.symm⟩
          },
        ⟩,
      {
        contextInsHold :=
          fun {dd xx} inCins =>
            if h: x = xx then
              let dEq: (Set3.just dX).posMem dd :=
                Valuation.update.eqBound _ xx dX ▸
                (h ▸ isSatBody.contextInsHold) inCins.left
              (inCins.right (ValVar.eq dEq h.symm)).elim
            else
              Valuation.update.eqOrig c h _ ▸
              isSatBody.contextInsHold inCins.left
        backgroundInsHold :=
          fun {dd xx} inBins =>
            if h: x = xx then
              let dEq: (Set3.just dX).posMem dd :=
                Valuation.update.eqBound _ xx dX ▸
                (h ▸ isSatBody.backgroundInsHold) inBins.left
              (inBins.right (ValVar.eq dEq h.symm)).elim
            else
              Valuation.update.eqOrig b h _ ▸
              isSatBody.backgroundInsHold inBins.left
        backgroundOutHold :=
          fun {dd xx} inBout =>
            if h: x = xx then
              let dNeq: ¬(Set3.just dX).defMem dd :=
                Valuation.update.eqBound _ xx dX ▸
                (h ▸ isSatBody.backgroundOutHold) inBout.left
              (inBout.right ⟨dNeq, h.symm⟩).elim
            else
              Valuation.update.eqOrig b h _ ▸
              isSatBody.backgroundOutHold inBout.left
      },
    ⟩
  | Expr.Ir x body =>
    -- Has to be a separate variable because of
    -- https://github.com/leanprover/lean4/issues/1694
    let ih dX := exSatOfIsPos (isPos dX)
    ⟨
      Cause.arbUn (fun dX => (ih dX).val.exceptBound x dX),
      fun isSat dX =>
        -- This ought to work, Lean:
        -- let ⟨causeBody, isCauseBody, isSatBody⟩ := ofIsPos (isPos dX)
        let cause := exSatOfIsPos (isPos dX)
        let causeBody := cause.val
        let isCauseBody := cause.property.left
        let isSatBody := cause.property.right
        
        isCauseBody {
          contextInsHold :=
            fun {dd xx} inCins =>
              if h: x = xx then
                Valuation.update.eqBoundOfEq _ h dX ▸
                Valuation.update.eqBoundOfEq c h dX ▸
                isSatBody.contextInsHold inCins
              else
                Valuation.update.eqOrig _ h _ ▸
                isSat.contextInsHold
                  ⟨dX, inCins, h ∘ Eq.symm ∘ ValVar.eqX⟩
          backgroundInsHold :=
            fun {dd xx} inBins =>
              if h: x = xx then
                Valuation.update.eqBoundOfEq _ h dX ▸
                Valuation.update.eqBoundOfEq b h dX ▸
                isSatBody.backgroundInsHold inBins
              else
                Valuation.update.eqOrig _ h _ ▸
                isSat.backgroundInsHold
                  ⟨dX, inBins, h ∘ Eq.symm ∘ ValVar.eqX⟩
          backgroundOutHold :=
            fun {dd xx} inBout =>
              if h: x = xx then
                Valuation.update.eqBoundOfEq _ h dX ▸
                Valuation.update.eqBoundOfEq b h dX ▸
                isSatBody.backgroundOutHold inBout
              else
                Valuation.update.eqOrig _ h _ ▸
                isSat.backgroundOutHold
                  ⟨dX, inBout, fun ⟨_, eqX⟩ => h eqX.symm⟩
        },
      {
        contextInsHold :=
          fun {dd xx} inCins =>
            let ⟨dX, inCinsAtDx⟩ := inCins.unwrap
            
            let cause := exSatOfIsPos (isPos dX)
            let causeBody := cause.val.exceptBound x dX
            let isSatBody := cause.property.right
            
            if h: x = xx then
              let dEq: (Set3.just dX).posMem dd :=
                Valuation.update.eqBoundOfEq _ h dX ▸
                isSatBody.contextInsHold inCinsAtDx.left
              (inCinsAtDx.right (ValVar.eq dEq h.symm)).elim
            else
              Valuation.update.eqOrig c h _ ▸
              isSatBody.contextInsHold inCinsAtDx.left
        backgroundInsHold :=
          fun {dd xx} inBins =>
            let ⟨dX, inBinsAtDx⟩ := inBins.unwrap
            
            let cause := exSatOfIsPos (isPos dX)
            let causeBody := cause.val.exceptBound x dX
            let isSatBody := cause.property.right
            
            if h: x = xx then
              let dEq: (Set3.just dX).posMem dd :=
                Valuation.update.eqBoundOfEq _ h dX ▸
                isSatBody.backgroundInsHold inBinsAtDx.left
              (inBinsAtDx.right (ValVar.eq dEq h.symm)).elim
            else
              Valuation.update.eqOrig b h _ ▸
              isSatBody.backgroundInsHold inBinsAtDx.left
        backgroundOutHold :=
          fun {dd xx} inBout =>
            let ⟨dX, inBoutAtDx⟩ := inBout.unwrap
            
            let cause := exSatOfIsPos (isPos dX)
            let causeBody := cause.val.exceptBound x dX
            let isSatBody := cause.property.right
            
            if h: x = xx then
              let dNeq: ¬(Set3.just dX).defMem dd :=
                Valuation.update.eqBoundOfEq _ h dX ▸
                isSatBody.backgroundOutHold inBoutAtDx.left
              (inBoutAtDx.right ⟨dNeq, h.symm⟩).elim
            else
              Valuation.update.eqOrig b h _ ▸
              isSatBody.backgroundOutHold inBoutAtDx.left
      },
    ⟩

def IsWeakCause.isPosOfIsApplicable
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  (isCause: IsWeakCause salg cause d expr)
  {b c: Valuation salg.D}
  (isApp: ¬ cause.IsInapplicable c.nonmembers b)
:
  (expr.interpretation salg b c).posMem d
:=
  isCause (Cause.IsInapplicable.toIsWeaklySatisfiedBy isApp)

def IsWeakCause.isInapplicableOfIsNonmember
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  (isCause: IsWeakCause salg cause d expr)
  {b c: Valuation salg.D}
  (notPos: ¬(expr.interpretation salg b c).posMem d)
:
  cause.IsInapplicable c.nonmembers b
:=
  Not.dne ((isPosOfIsApplicable isCause).contra notPos)


def everyCauseInapplicableImpliesDefinitiveNonmember
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (d: salg.D)
  (expr: Expr sig)
  (outSet: Set (ValVar salg.D))
  (isEveryCauseInapplicable:
    {cause: Cause salg.D} →
    IsWeakCause salg cause d expr →
    cause.IsInapplicable outSet b)
  (outSetIsEmpty:
    ∀ {d x}, ⟨d, x⟩ ∈ outSet → ¬ (c x).posMem d)
:
  ¬(expr.interpretation salg b c).posMem d
:=
  fun isPos =>
    let ⟨cause, isCause, isSat⟩ := IsWeakCause.exSatOfIsPos isPos
    let isApp := isSat.toIsApplicable outSet outSetIsEmpty
    
    isApp (isEveryCauseInapplicable isCause)

def emptyCycleIsOut
  (salg: Salgebra sig)
  (dl: DefList sig)
  (cycle: Set (ValVar salg.D))
  (isEmptyCycle:
    ∀ {d x},
    ⟨d, x⟩ ∈ cycle →
    (cause: Cause salg.D) →
    IsWeakCause salg cause d (dl.getDef x) →  
    cause.IsInapplicable cycle (dl.wellFoundedModel salg))
  {d x}
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  ¬(dl.wellFoundedModel salg x).posMem d
:=
  let wfm := dl.wellFoundedModel salg
  let ⟨isFp, _⟩ := DefList.wellFoundedModel.isLfpB salg dl
  
  isFp ▸
  lfp.induction
    (fun v => ∀ vv ∈ cycle, ¬(v vv.x).posMem vv.d)
    (Valuation.ord.standard.isChainComplete salg.D)
    (operatorC salg dl wfm)
    (operatorC.isMonotonic salg dl wfm)
    (fun n ih ⟨d, x⟩ isInCycle =>
      if h: n.IsActualLimit then
        let isSup := operatorC.stage.limit salg dl wfm h
        
        Valuation.ord.standard.allNinSet.ninSup.posMem
          ⟨_, isSup⟩
          fun ⟨prev, ⟨i, eqAtI⟩⟩ => eqAtI ▸ ih i ⟨d, x⟩ isInCycle
      else
        let eqPred := operatorC.stage.predEq salg dl wfm h
        
        let nPredLt := Ordinal.predLtOfNotLimit h
        
        show
          ¬(operatorC.stage salg dl wfm n x).posMem d
        from
          let ihPred := ih ⟨n.pred, nPredLt⟩
          eqPred ▸
          everyCauseInapplicableImpliesDefinitiveNonmember
            salg wfm _ d
            (dl.getDef x)
            cycle
            (isEmptyCycle isInCycle _)
            (ih ⟨n.pred, nPredLt⟩ _))
    ⟨d, x⟩
    inCycle


structure InsOutComplete
  (salg: Salgebra sig)
  (dl: DefList sig)
  (v: Valuation salg.D)
:
  Prop
where
  insIsComplete:
    ∀ {d x}, (v x).defMem d → Ins salg dl d x
  outIsComplete:
    ∀ {d x}, ¬(v x).posMem d → Out salg dl d x

def completenessProofC
  (isComplete: InsOutComplete salg dl b)
:
  InsOutComplete salg dl (operatorC.lfp salg dl b).val
:=
  let isCc := Valuation.ord.standard.isChainComplete salg.D
  let opC := operatorC salg dl b
  let isMono {v0 v1: Valuation salg.D} (isLe: v0 ≤ v1) :=
    operatorC.isMonotonic salg dl b isLe
  
  {
    insIsComplete :=
      lfp.induction
        (fun v => ∀ {d x}, (v x).defMem d → Ins salg dl d x)
        isCc
        opC
        isMono
        (fun n ih d x isDefN =>
          if h: n.IsActualLimit then
            let isSup := lfp.stage.limit isCc opC isMono h
            let ⟨⟨v, ⟨nn, vEqStageNn⟩⟩, inDefPrev⟩ :=
              Valuation.ord.standard.inSup.inSomeSet.defMem
                ⟨_, isSup⟩
                isDefN
            let eq: lfp.stage isCc opC isMono nn = v := vEqStageNn
            ih nn (eq ▸ inDefPrev)
          else
            let eqPred := lfp.stage.predEq isCc opC isMono h
            let nPredLt := Ordinal.predLtOfNotLimit h
            let predStage := lfp.stage isCc opC isMono n.pred
            
            let isDefOfBPred:
              Set3.defMem
                ((dl.getDef x).interpretation salg b predStage)
                d
            :=
              show (opC _ x).defMem d from
              eqPred ▸ isDefN
            
            
            let cause: Cause salg.D := {
              contextIns :=
                fun ⟨dd, xx⟩ => (predStage xx).defMem dd
              backgroundIns :=
                fun ⟨dd, xx⟩ => (b xx).defMem dd
              backgroundOut :=
                fun ⟨dd, xx⟩ => ¬(b xx).posMem dd
            }
            
            let isCause: IsStrongCause salg cause d (dl.getDef x) :=
              fun {b1 c1} isSat =>
                let isLe: b ⊑ b1 :=
                  fun x => {
                    defLe := fun d isDef =>
                      isSat.backgroundInsHold isDef
                    posLe := fun d isPos =>
                      byContradiction (isSat.backgroundOutHold · isPos)
                  }
                
                let isMono :=
                  Expr.interpretation.isMonotonic.approximation
                    salg (dl.getDef x) isLe
                    ((Valuation.ord.approximation _).le_refl _)
                
                Expr.interpretation.isMonotonic.defMem
                  (fun _ _ => isSat.contextInsHold)
                  (isMono.defLe isDefOfBPred)
            
            Ins.intro d x cause isCause
              (ih ⟨n.pred, nPredLt⟩)
              isComplete.insIsComplete
              isComplete.outIsComplete)
    outIsComplete :=
      Out.intro
        (fun ⟨d, x⟩ => ¬((operatorC.lfp salg dl b).val x).posMem d)
        (fun {dd xx} notPos cause isCause =>
          let lfp := operatorC.lfp salg dl b
          let ⟨isFp, _⟩ := lfp.property
          
          let eqAtXx:
            (dl.getDef xx).interpretation salg b lfp.val = lfp.val xx
          :=
            congr isFp.symm rfl
          
          let isInapp :=
            isCause.isInapplicableOfIsNonmember (eqAtXx ▸ notPos)
          
          match isInapp with
          | Cause.IsInapplicable.blockedContextIns inCins inCycle =>
            IsCauseInapplicable.blockedContextIns _ inCins inCycle
          | Cause.IsInapplicable.blockedBackgroundIns inBins notPos =>
            let isOut := isComplete.outIsComplete notPos
            IsCauseInapplicable.blockedBackgroundIns _ inBins isOut
          | Cause.IsInapplicable.blockedBackgroundOut inBout isIns =>
            let isIns := isComplete.insIsComplete isIns
            IsCauseInapplicable.blockedBackgroundOut _ inBout isIns)
  }

def completenessProofB
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  InsOutComplete salg dl (dl.wellFoundedModel salg)
:=
  let isCc := Valuation.ord.approximation.isChainComplete salg.D
  let opB := operatorB salg dl
  let isMono {v0 v1: Valuation salg.D} (isLe: v0 ⊑ v1) :=
    operatorB.isMonotonic salg dl isLe
  
  lfp.induction
    (InsOutComplete salg dl)
    isCc
    opB
    isMono
    (fun n ih =>
      if h: n.IsActualLimit then
        {
          insIsComplete :=
            fun isDefN =>
              let isSup := lfp.stage.limit isCc opB isMono h
              let ⟨⟨v, ⟨nn, vEqStageNn⟩⟩, inDefPrev⟩ :=
                Valuation.ord.approximation.inSup.inSomeSet.defMem
                  ⟨_, isSup⟩
                  isDefN
              let eq: lfp.stage isCc opB isMono nn = v := vEqStageNn
              (ih nn).insIsComplete (eq ▸ inDefPrev)
          outIsComplete :=
            fun notPosN =>
              let isSup := lfp.stage.limit isCc opB isMono h
              let ⟨⟨v, ⟨nn, vEqStageNn⟩⟩, inDefPrev⟩ :=
                Valuation.ord.approximation.ninSup.ninSomeSet.posMem
                  ⟨_, isSup⟩
                  notPosN
              let eq: lfp.stage isCc opB isMono nn = v := vEqStageNn
              (ih nn).outIsComplete (eq ▸ inDefPrev)
        }
      else
        let eqPred := lfp.stage.predEq isCc opB isMono h
        let nPredLt := Ordinal.predLtOfNotLimit h
        let ihPred := ih ⟨n.pred, nPredLt⟩
        
        eqPred ▸ completenessProofC ihPred)


def IsCauseInapplicable.toSuperCause
  (isInapp: IsCauseInapplicable salg dl cycle causeA)
  (isSuper: causeA ⊆ causeB)
:
  IsCauseInapplicable salg dl cycle causeB
:=
  match isInapp with
  | blockedContextIns _ inCins inCycle =>
    blockedContextIns _ (isSuper.cinsLe inCins) inCycle
  | blockedBackgroundIns _ inBins isOut =>
    blockedBackgroundIns _ (isSuper.binsLe inBins) isOut
  | blockedBackgroundOut _ inBout isIns =>
    blockedBackgroundOut _ (isSuper.boutLe inBout) isIns

def IsCauseInapplicable.toSuperCycle
  (isInapp: IsCauseInapplicable salg dl cycleA cause)
  (isSuper: cycleA ⊆ cycleB)
:
  IsCauseInapplicable salg dl cycleB cause
:=
  match isInapp with
  | blockedContextIns _ inCins inCycle =>
    blockedContextIns _ inCins (isSuper inCycle)
  | blockedBackgroundIns _ inBins isOut =>
    blockedBackgroundIns _ inBins isOut
  | blockedBackgroundOut _ inBout isIns =>
    blockedBackgroundOut _ inBout isIns

def IsCauseInapplicable.toSuper
  (isInapp: IsCauseInapplicable salg dl cycleA causeA)
  (isSuper: cycleA ⊆ cycleB)
  (isSuperCause: causeA ⊆ causeB)
:
  IsCauseInapplicable salg dl cycleB causeB
:=
  let isInapp := isInapp.toSuperCause isSuperCause
  isInapp.toSuperCycle isSuper
