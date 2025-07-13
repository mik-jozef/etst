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

-- The possible nonmembers of a valuation.
def Valuation.posNonmembers
  (v: Valuation D)
:
  Set (ValVar D)
:=
  fun ⟨d, x⟩ => ¬ (v x).defMem d

-- The (definite) members of a valuation.
def Valuation.members
  (v: Valuation D)
:
  Set (ValVar D)
:=
  fun ⟨d, x⟩ => (v x).defMem d

-- The possible members of a valuation.
def Valuation.posMembers
  (v: Valuation D)
:
  Set (ValVar D)
:=
  fun ⟨d, x⟩ => (v x).posMem d


def Cause.ofValPos
  (b c: Valuation D)
:
  Cause D
:= {
  contextIns := c.posMembers
  backgroundIns := b.posMembers
  backgroundOut := b.posNonmembers
}

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

| ⟨⟨_⟩, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

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

def Cause.unionSymm (c0 c1: Cause D): c0 ∪ c1 = c1 ∪ c0 :=
  Cause.eq
    (Set.union_comm c0.contextIns c1.contextIns)
    (Set.union_comm c0.backgroundIns c1.backgroundIns)
    (Set.union_comm c0.backgroundOut c1.backgroundOut)

def Cause.unionEqRightSub
  {c0 c1: Cause D}
  (isSub: c1 ⊆ c0)
:
  c0 ∪ c1 = c0
:=
  Cause.eq
    (Set.union_eq_self_of_subset_right isSub.cinsLe)
    (Set.union_eq_self_of_subset_right isSub.binsLe)
    (Set.union_eq_self_of_subset_right isSub.boutLe)

def Cause.except
  (a b: Cause D)
:
  Cause D
:= {
  contextIns := a.contextIns \ b.contextIns
  backgroundIns := a.backgroundIns \ b.backgroundIns
  backgroundOut := a.backgroundOut \ b.backgroundOut
}

def Cause.exceptVar
  (cause: Cause D)
  (x: Nat)
:
  Cause D
:=
  cause.except {
    contextIns := fun vv => vv.x = x
    backgroundIns := fun vv => vv.x = x
    backgroundOut := fun vv => vv.x = x
  }

def Cause.exceptVarIsSub
  (cause: Cause D)
  (x: Nat)
:
  cause.exceptVar x ⊆ cause
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
:=
  cause.except {
    contextIns := {⟨d, x⟩}
    backgroundIns := {⟨d, x⟩}
    backgroundOut := fun ⟨dd, xx⟩ => dd ≠ d ∧ xx = x
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
  cinsSat := fun
    | _, Or.inl inCins => satL.cinsSat _ inCins
    | _, Or.inr inCins => satR.cinsSat _ inCins
  binsSat := fun
    | _, Or.inl inBins => satL.binsSat _ inBins
    | _, Or.inr inBins => satR.binsSat _ inBins
  boutSat := fun
    | _, Or.inl inBout => satL.boutSat _ inBout
    | _, Or.inr inBout => satR.boutSat _ inBout
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
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: (b x).defMem d)
:
  IsInapplicable cause outSet b

def Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy
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

def Cause.IsWeaklySatisfiedBy.Not.toIsInapplicable
  {cause: Cause D}
  {b c: Valuation D}
  (notSat: ¬ Cause.IsWeaklySatisfiedBy cause b c)
:
  Cause.IsInapplicable cause c.nonmembers b
:=
  Function.contraA
    Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy
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

def Cause.IsWeaklySatisfiedBy.ofValPos
  (b c: Valuation D)
:
  (Cause.ofValPos b c).IsWeaklySatisfiedBy b c
:= {
  contextInsHold := id
  backgroundInsHold := id
  backgroundOutHold := id
}

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

def Cause.IsWeaklySatisfiedBy.elimUnL
  (isSat: Cause.IsWeaklySatisfiedBy (causeL ∪ causeR) b c)
:
  Cause.IsWeaklySatisfiedBy causeL b c
:= {
  contextInsHold := isSat.contextInsHold ∘ Or.inl
  backgroundInsHold := isSat.backgroundInsHold ∘ Or.inl
  backgroundOutHold := isSat.backgroundOutHold ∘ Or.inl
}

def Cause.IsWeaklySatisfiedBy.elimUnR
  (isSat: Cause.IsWeaklySatisfiedBy (causeL ∪ causeR) b c)
:
  Cause.IsWeaklySatisfiedBy causeR b c
:= {
  contextInsHold := isSat.contextInsHold ∘ Or.inr
  backgroundInsHold := isSat.backgroundInsHold ∘ Or.inr
  backgroundOutHold := isSat.backgroundOutHold ∘ Or.inr
}

def Cause.IsWeaklySatisfiedBy.elimArbUn
  {f: I → Cause D}
  (isSat: Cause.IsWeaklySatisfiedBy (Cause.arbUn f) b c)
  (i: I)
:
  Cause.IsWeaklySatisfiedBy (f i) b c
:= {
  contextInsHold := isSat.contextInsHold ∘ fun vv => ⟨_, vv⟩
  backgroundInsHold := isSat.backgroundInsHold ∘ fun vv => ⟨_, vv⟩
  backgroundOutHold := isSat.backgroundOutHold ∘ fun vv => ⟨_, vv⟩
}


noncomputable def IsWeakCause.ofValPos
  (isPos: (expr.interpretation salg b c).posMem d)
:
  IsWeakCause salg (Cause.ofValPos b c) d expr
:=
  fun isSat =>
    Expr.interpretation.isMonotonic.apxPosMem
      (fun _ => {
        defLe :=
          fun _ isDef =>
            byContradiction (isSat.backgroundOutHold · isDef)
        posLe := fun _ => isSat.backgroundInsHold
      })
      (fun _ _ => isSat.contextInsHold)
      isPos

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
  isCause (Cause.IsInapplicable.Not.toIsWeaklySatisfiedBy isApp)

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
  let isSat := Cause.IsWeaklySatisfiedBy.ofValPos b c
  let isApp := isSat.toIsApplicable outSet outSetIsEmpty
  
  isApp ∘ isEveryCauseInapplicable ∘ IsWeakCause.ofValPos

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
      if h: n.IsSuccPrelimit then
        let isSup := operatorC.stage.limit salg dl wfm h
        
        Valuation.ord.standard.allNinSet.ninSup.posMem
          ⟨_, isSup⟩
          fun ⟨prev, ⟨i, eqAtI⟩⟩ => eqAtI ▸ ih i ⟨d, x⟩ isInCycle
      else
        let eqPred := operatorC.stage.predEq salg dl wfm h
        
        let nPredLt := Ordinal.predLtOfNotPrelimit h
        
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
          if h: n.IsSuccPrelimit then
            let isSup := lfp.stage.limit isCc opC isMono h
            let ⟨⟨v, ⟨nn, vEqStageNn⟩⟩, inDefPrev⟩ :=
              Valuation.ord.standard.inSup.inSomeSet.defMem
                ⟨_, isSup⟩
                isDefN
            let eq: lfp.stage isCc opC isMono nn = v := vEqStageNn
            ih nn (eq ▸ inDefPrev)
          else
            let eqPred := lfp.stage.predEq isCc opC isMono h
            let nPredLt := Ordinal.predLtOfNotPrelimit h
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
      if h: n.IsSuccPrelimit then
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
        let nPredLt := Ordinal.predLtOfNotPrelimit h
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
