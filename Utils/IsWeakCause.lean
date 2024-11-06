/-
  This file defines constructors and eliminators for the predicate
  `IsWeakCause`, as well as some related helper definitions.
  
  At least, that was the plan. Turns out, weak causes aren't
  eliminable as easily and conveniently as strong causes (although
  what I have most likely can be improved further). However, it
  turns out I can make do with a hacky solution I've named
  `hurrDurrElim`. Feels a little improper, but it works.
-/

import WFC.Ch6_S1_AProofSystem
import Utils.PairExpr


def WeakSatIsStrongCauseOut
  (salg: Salgebra sig)
  (cause: Cause salg.D)
  (d: salg.D)
  (expr: Expr sig)
:
  Prop
:=
  {b c: Valuation salg.D} →
  cause.IsWeaklySatisfiedBy b c →
  ¬ (expr.interpretation salg b c).posMem d

def WeakSatIsStrongCauseOutUpdated
  (salg: Salgebra sig)
  (cause: Cause salg.D)
  (d: salg.D)
  (expr: Expr sig)
  (x: Nat)
  (dX: salg.D)
:
  Prop
:=
  {b c: Valuation salg.D} →
  cause.IsWeaklySatisfiedBy b c →
  Not
    (Set3.posMem
      (expr.interpretation
        salg
        (b.update x dX)
        (c.update x dX))
      d)

def Cause.IsWeaklySatisfiedBy.exceptToWithBound
  {cause: Cause D}
  {x: Nat}
  (isSat: (cause.exceptX x).IsWeaklySatisfiedBy b c)
  (d: D)
:
  (cause.withBound x d).IsWeaklySatisfiedBy
    (b.update x d)
    (c.update x d)
:= {
  contextInsHold :=
    fun inCinsWith =>
      inCinsWith.elim
        (fun ⟨inCins, xNeq⟩ =>
          Valuation.update.eqOrig _ xNeq.symm d ▸
          isSat.contextInsHold ⟨inCins, xNeq⟩)
        (fun ⟨dEq, xEq⟩ =>
          Valuation.update.eqBoundOfEq _ xEq.symm d ▸
          dEq ▸ rfl)
  backgroundInsHold :=
    fun inBinsWith =>
      inBinsWith.elim
        (fun ⟨inBins, xNeq⟩ =>
          Valuation.update.eqOrig _ xNeq.symm d ▸
          isSat.backgroundInsHold ⟨inBins, xNeq⟩)
        (fun ⟨dEq, xEq⟩ =>
          Valuation.update.eqBoundOfEq _ xEq.symm d ▸
          dEq ▸ rfl)
  backgroundOutHold :=
    fun inBoutWith =>
      inBoutWith.elim
        (fun ⟨inBout, xNeq⟩ =>
          Valuation.update.eqOrig _ xNeq.symm d ▸
          isSat.backgroundOutHold ⟨inBout, xNeq⟩)
        (fun ⟨dNeq, xEq⟩ =>
          Valuation.update.eqBoundOfEq _ xEq.symm d ▸
          dNeq)
}

def Cause.IsWeaklySatisfiedBy.toWithBound
  {cause: Cause D}
  {x: Nat}
  (isSat: cause.IsWeaklySatisfiedBy b c)
  (d: D)
:
  (cause.withBound x d).IsWeaklySatisfiedBy
    (b.update x d)
    (c.update x d)
:=
  (isSat.ofSuper (cause.exceptXIsSub x)).exceptToWithBound d

def Cause.IsWeaklySatisfiedBy.fromWithBound
  {cause: Cause D}
  (isSat: (cause.withBound x dX).IsWeaklySatisfiedBy b c)
:
  cause.IsWeaklySatisfiedBy
    (b.updateSet3 x Set3.undetermined)
    (c.updateSet3 x Set3.undetermined)
:= {
  contextInsHold :=
    fun {_dd xx} inCins =>
      if h: x = xx then
        h ▸
        Valuation.updateSet3.eqBound c x _ ▸
        trivial
      else
        Valuation.updateSet3.eqOrig c h _ ▸
        isSat.contextInsHold (Or.inl ⟨inCins, (Ne.symm h)⟩)
  backgroundInsHold :=
    fun {_dd xx} inBins =>
      if h: x = xx then
        h ▸
        Valuation.updateSet3.eqBound b x _ ▸
        trivial
      else
        Valuation.updateSet3.eqOrig b h _ ▸
        isSat.backgroundInsHold (Or.inl ⟨inBins, (Ne.symm h)⟩)
  backgroundOutHold :=
    fun {_dd xx} inBout =>
      if h: x = xx then
        h ▸
        Valuation.updateSet3.eqBound b x _ ▸
        id
      else
        Valuation.updateSet3.eqOrig b h _ ▸
        isSat.backgroundOutHold (Or.inl ⟨inBout, (Ne.symm h)⟩)
}


def Cause.IsWeaklySatisfiedBy.satLeUpdatedB
  {cause: Cause D}
  (isSat: (cause.withBound x dX).IsWeaklySatisfiedBy b c)
:
  b ⊑ b.update x dX
:=
  fun xx => {
    defLe :=
      fun d isDef =>
        if h: x = xx then
          Valuation.update.eqBoundOfEq b h dX ▸
          byContradiction fun neq: d ≠ dX =>
            isSat.backgroundOutHold (Or.inr ⟨neq, h.symm⟩) isDef
        else
          Valuation.update.eqOrig b h dX ▸
          isDef
    posLe :=
      fun d isPos =>
        if h: x = xx then
          let dEq: d ∈ (Set3.just dX).posMem :=
            Valuation.update.eqBoundOfEq b h dX ▸
            isPos
          isSat.backgroundInsHold (Or.inr ⟨dEq, h.symm⟩)
        else
          Valuation.update.eqOrig b h _ ▸
          isPos
  }

def Cause.IsWeaklySatisfiedBy.satLeUpdatedCPos
  {cause: Cause D}
  (isSat: (cause.withBound x dX).IsWeaklySatisfiedBy b c)
:
  ∀ xx, (c.update x dX xx).posMem ⊆ (c xx).posMem
:=
  fun xx d isPos =>
    if h: x = xx then
      let dEq: d ∈ (Set3.just dX).posMem :=
        Valuation.update.eqBoundOfEq c h dX ▸
        isPos
      isSat.contextInsHold (Or.inr ⟨dEq, h.symm⟩)
    else
      Valuation.update.eqOrig c h _ ▸
      isPos


def Cause.isWeaklySatByUndetermined
  (cause: Cause D)
:
  cause.IsWeaklySatisfiedBy
    Valuation.undetermined
    Valuation.undetermined
:= {
  contextInsHold := fun _ => trivial
  backgroundInsHold := fun _ => trivial
  backgroundOutHold := nofun
}


/-
  The least valuation in the standard order that weakly satisfies
  the background part of a cause.
  
  Useful in this file for (also) being a maximal such valuation
  in the approximation order.
-/
def Cause.leastBackgroundStd
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := Set.empty
    posMem := fun d => ⟨d, x⟩ ∈ cause.backgroundIns
    defLePos := nofun
  }

/-
  The greatest valuation in the standard order that weakly satisfies
  the background part of a cause.
-/
def Cause.greatestBackgroundStd
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := fun d => ⟨d, x⟩ ∉ cause.backgroundOut
    posMem := Set.full
    defLePos := fun _ _ => trivial
  }

/-
  The least valuation in the standard order that weakly satisfies
  the context part of a cause.
  
  Useful in this file for (also) being a maximal such valuation
  in the approximation order.
-/
def Cause.leastContextStd
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := Set.empty
    posMem := fun d => ⟨d, x⟩ ∈ cause.contextIns
    defLePos := nofun
  }


def Cause.leastBackgroundStdIsSat
  (cause: Cause D)
:
  cause.IsWeaklySatisfiedByBackground cause.leastBackgroundStd
:= {
  backgroundInsHold := id
  backgroundOutHold := nofun
}

def Cause.leastValsStdAreSat
  (cause: Cause D)
:
  cause.IsWeaklySatisfiedBy
    cause.leastBackgroundStd
    cause.leastContextStd
:= {
  contextInsHold := id
  backgroundInsHold := id
  backgroundOutHold := nofun
}

def Cause.leastBackgroundIsLeStd
  (cause: Cause D)
  (b: Valuation D)
  (bSat: cause.IsWeaklySatisfiedByBackground b)
:
  cause.leastBackgroundStd ≤ b
:=
  fun _ => {
    defLe := nofun
    posLe := fun _ => bSat.backgroundInsHold
  }

def Cause.leastContextIsLeStd
  (cause: Cause D)
  (c: Valuation D)
  (cSat: cause.IsWeaklySatisfiedByContext c)
:
  cause.leastContextStd ≤ c
:=
  fun _ => {
    defLe := nofun
    posLe := fun _ => cSat.contextInsHold
  }

-- TODO review everything above this line

namespace IsWeakCause
  def hurrDurrElim
    (isCause: IsWeakCause salg cause d expr)
    {P: Prop}
    (goalInC:
      Set3.posMem
        (expr.interpretation
          salg
          cause.leastBackgroundStd
          cause.leastContextStd)
        d →
      P)
  :
    P
  :=
    goalInC (isCause cause.leastValsStdAreSat)
  
  def hurrDurrElimGreat
    (isCause: IsWeakCause salg cause d expr)
    {P: Prop}
    (goalInC:
      Set3.posMem
        (expr.interpretation
          salg
          cause.greatestBackgroundStd
          cause.leastContextStd)
        d →
      P)
  :
    P
  :=
    goalInC (isCause {
      contextInsHold := id
      backgroundInsHold := fun _ => trivial
      backgroundOutHold := nofun
    })
  
  
  def var
    (isIns: ⟨d, x⟩ ∈ cause.contextIns)
  :
    IsWeakCause salg cause d (Expr.var x)
  :=
    fun isSat => isSat.contextInsHold isIns
  
  def elimVar
    (isCause: IsWeakCause salg cause d (Expr.var x))
  :
    ⟨d, x⟩ ∈ cause.contextIns
  :=
    let b := Valuation.undetermined
    let c: Valuation salg.D := fun xx => {
      defMem := Set.empty
      posMem := fun dd => xx ≠ x ∨ dd ≠ d
      defLePos := nofun
    }
    
    byContradiction fun ninCins =>
      let isSat: cause.IsWeaklySatisfiedBy b c := {
        contextInsHold :=
          fun {dd xx} inCins =>
            if h: xx = x ∧ dd = d then
              False.elim (ninCins (h.left ▸ h.right ▸ inCins))
            else
              h.toOr
        backgroundInsHold := fun _ => trivial
        backgroundOutHold := nofun
      }
      (isCause isSat).elim
        (fun nope => False.elim (nope rfl))
        (fun nope => False.elim (nope rfl))

  def notVar
    (ninCins: ⟨d, x⟩ ∉ cause.contextIns)
  :
    ¬ IsWeakCause salg cause d (Expr.var x)
  :=
    fun isCause => ninCins isCause.elimVar

  def Not.elimVar
    (isNotCause: ¬ IsWeakCause salg cause d (Expr.var x))
  :
    ⟨d, x⟩ ∉ cause.contextIns
  :=
    fun isIns => isNotCause (var isIns)
  
  
  def op
    {salg: Salgebra sig}
    {cause: Cause salg.D}
    {d: salg.D}
    
    (argVals: sig.Args opr salg.D)
    (argsCauseD: d ∈ salg.I opr argVals)
    (isCauseArgs:
      ∀ param (dArg: argVals param),
        IsWeakCause salg cause dArg (argExprs param))
  :
    IsWeakCause salg cause d (Expr.op opr argExprs)
  :=
    fun {b c} isSat =>
      salg.isMonotonic
        opr
        argVals
        (fun param =>
          ((argExprs param).interpretation salg b c).posMem)
        (fun param d inArgVals =>
          isCauseArgs param ⟨d, inArgVals⟩ isSat)
        argsCauseD
  
  -- def elimOp
  --   {salg: Salgebra sig}
  --   {cause: Cause salg.D}
  --   {d: salg.D}
    
  --   (isCause: IsWeakCause salg cause d (Expr.op opr argExprs))
  -- :
  --   ∃ (argVals: sig.Args opr salg.D),
  --     d ∈ salg.I opr argVals ∧
  --     ∀ param (dArg: argVals param),
  --       IsWeakCause salg cause dArg (argExprs param)
  -- :=
  --   sorry
  -- 
  -- elimOp would be nice, but more complex & we don't need it.
  -- Imagine we have an operator that happens to be a triset union.
  -- Then in general,
  --
  --     IsWeakCause unionSalg cause d (unionExpr left rite)
  -- 
  -- does not imply
  -- 
  --     Or
  --       IsWeakCause unionSalg cause d left
  --       IsWeakCause unionSalg cause d rite \,.
  -- 
  -- As a counterexample, consider the expression
  -- 
  --     x | ¬ x \,,
  -- 
  -- For which any cause is a weak cause, but that gives us zero
  -- information about the causes of x and ¬ x.
  -- 
  -- I think that in general, union-like expressions, ie. where
  -- two non-comparable valuations may both induce `d ∈ expr` may
  -- only be eliminated into a sub-expression when all but one of
  -- the possible weak causes are strongly eliminated.
  
  def elimZeroExpr
    (isCause: IsWeakCause pairSalgebra cause d PairExpr.zeroExpr)
  :
    d = Pair.zero
  :=
    isCause cause.isWeaklySatByUndetermined
  
  def elimPairExprEx
    (isCause:
      IsWeakCause
        pairSalgebra cause d (PairExpr.pairExpr left rite))
  :
    ∃ (dLeft dRite: Pair),
      d = Pair.pair dLeft dRite ∧
      IsWeakCause pairSalgebra cause dLeft left ∧
      IsWeakCause pairSalgebra cause dRite rite
  :=
    let ⟨dLeft, dRite, eq⟩ :=
      isCause cause.isWeaklySatByUndetermined
    
    ⟨
      dLeft,
      dRite,
      eq,
      fun isSat =>
        let ⟨⟨dLeftAlias, leftAliasIn⟩, _, eqAlias⟩ :=
          eq ▸ isCause isSat
        let eqLeft: dLeft = dLeftAlias :=
          Pair.noConfusion eqAlias fun eqLeft _ => eqLeft
        
        eqLeft ▸ leftAliasIn,
      fun isSat =>
        let ⟨_, ⟨dRiteAlias, riteAliasIn⟩, eqAlias⟩ :=
          eq ▸ isCause isSat
        let eqRite: dRite = dRiteAlias :=
          Pair.noConfusion eqAlias fun _ eqRite => eqRite
        
        eqRite ▸ riteAliasIn
    ⟩
  
  def elimPairExpr
    (isCause:
      IsWeakCause
        pairSalgebra
        cause
        (Pair.pair dLeft dRite)
        (PairExpr.pairExpr left rite))
  :
    IsWeakCause pairSalgebra cause dLeft left ∧
    IsWeakCause pairSalgebra cause dRite rite
  :=
    let ⟨_, _, eq, isCauseLeft, isCauseRite⟩ :=
      elimPairExprEx isCause
    let ⟨eqL, eqR⟩ := Pair.noConfusion eq And.intro
    ⟨eqL ▸ isCauseLeft, eqR ▸ isCauseRite⟩
  
  def Not.elimOp
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (isNotCause: ¬ IsWeakCause salg cause d (Expr.op opr argExprs))
  (argVals: sig.Args opr salg.D)
  (argsCauseD: d ∈ salg.I opr argVals)
:
  ∃ param, ∃ (dArg: argVals param),
    ¬ IsWeakCause salg cause dArg (argExprs param)
:=
  byContradiction fun nex =>
    let allHaveCause:
      ∀ param (dArg: argVals param),
        IsWeakCause salg cause dArg (argExprs param)
    :=
      nex.toAll fun _ tmp => tmp.toAll fun _ isCause => isCause.dne
    
    isNotCause (op argVals argsCauseD allHaveCause)
  
  -- Requires elimOp
  -- def notOp
  --   {salg: Salgebra sig}
  --   {cause: Cause salg.D}
  --   {d: salg.D}
    
  --   (allCausesNot:
  --     ∀ argVals: sig.Args opr salg.D,
  --       d ∈ salg.I opr argVals →
  --     ∃ param, ∃ (dArg: argVals param),
  --       ¬ IsWeakCause salg cause dArg (argExprs param))
  -- :
  --   ¬ IsWeakCause salg cause d (Expr.op opr argExprs)
  -- :=
  --   fun isCause =>
  --     let ⟨argVals, dIn, argsStrong⟩ := isCause.elimOp
  --     let ⟨param, dArg, notStrong⟩ := allCausesNot argVals dIn
  --     notStrong (argsStrong param dArg)
  
  
  def unLeft
    (isCause: IsWeakCause salg cause d left)
    (rite: Expr _)
  :
    IsWeakCause salg cause d (Expr.un left rite)
  :=
    Or.inl ∘ isCause
  
  def unRite
    (isCause: IsWeakCause salg cause d rite)
    (left: Expr _)
  :
    IsWeakCause salg cause d (Expr.un left rite)
  :=
    Or.inr ∘ isCause
  
  def elimUnLeft
    (isCause: IsWeakCause salg cause d (Expr.un left rite))
    -- Note: This feels like a hack, or at least a very partial
    -- solution. For example, we cannot use it to eliminate
    -- 
    --     IsWeakCause salg cause d (Expr.un x x) \,.
    -- 
    -- I don't know if there is anythign better, though.
    (notCauseRite:
      WeakSatIsStrongCauseOut salg cause d rite)
  :
    IsWeakCause salg cause d left
  :=
    fun isSat =>
      (isCause isSat).elim
        id
        (fun isPosRite =>
          False.elim (notCauseRite isSat isPosRite))
  
  def elimUnRite
    (isCause: IsWeakCause salg cause d (Expr.un left rite))
    (notCauseLeft:
      WeakSatIsStrongCauseOut salg cause d left)
  :
    IsWeakCause salg cause d rite
  :=
    fun isSat =>
      (isCause isSat).elim
        (fun isPosLeft =>
          False.elim (notCauseLeft isSat isPosLeft))
        id
  
  def Not.elimUnLeft
    (isNotCause: ¬ IsWeakCause salg cause d (Expr.un left rite))
  :
    ¬ IsWeakCause salg cause d left
  :=
    fun isCause => isNotCause (isCause.unLeft rite)
  
  def Not.elimUnRite
    (isNotCause: ¬ IsWeakCause salg cause d (Expr.un left rite))
  :
    ¬ IsWeakCause salg cause d rite
  :=
    fun isCause => isNotCause (isCause.unRite left)
  
  
  def ir
    (isCauseLeft: IsWeakCause salg cause d left)
    (isCauseRite: IsWeakCause salg cause d rite)
  :
    IsWeakCause salg cause d (Expr.ir left rite)
  :=
    fun isSat =>
      And.intro (isCauseLeft isSat) (isCauseRite isSat)
  
  def elimIrLeft
    (isCause: IsWeakCause salg cause d (Expr.ir left rite))
  :
    IsWeakCause salg cause d left
  :=
    fun isSat => (isCause isSat).left
  
  def elimIrRite
    (isCause: IsWeakCause salg cause d (Expr.ir left rite))
  :
    IsWeakCause salg cause d rite
  :=
    fun isSat => (isCause isSat).right
  
  def elimIr
    (isCause: IsWeakCause salg cause d (Expr.ir left rite))
  :
    And
      (IsWeakCause salg cause d left)
      (IsWeakCause salg cause d rite)
  :=
    ⟨elimIrLeft isCause, elimIrRite isCause⟩
  
  def Not.elimIr
    (isNotCause: ¬ IsWeakCause salg cause d (Expr.ir left rite))
  :
    Or
      (¬ IsWeakCause salg cause d left)
      (¬ IsWeakCause salg cause d rite)
  :=
    byContradiction fun nor =>
      let ⟨isCauseLeft, isCauseRite⟩ := nor.toAnd
      isNotCause (ir isCauseLeft.dne isCauseRite.dne)
  
  def notIrLeft
    (notCauseLeft: ¬ IsWeakCause salg cause d left)
  :
    ¬ IsWeakCause salg cause d (Expr.ir left rite)
  :=
    fun isCause => notCauseLeft (elimIrLeft isCause)
  
  def notIrRite
    (notCauseRite: ¬ IsWeakCause salg cause d rite)
  :
    ¬ IsWeakCause salg cause d (Expr.ir left rite)
  :=
    fun isCause => notCauseRite (elimIrRite isCause)
  
  
  def cpl
    {expr: Expr sig}
    (cause: Cause salg.D)
    (isCauseOut:
      {b: Valuation salg.D} →
      cause.IsWeaklySatisfiedByBackground b →
      ¬ (expr.interpretation salg b b).defMem d)
  :
    IsWeakCause salg cause d (Expr.cpl expr)
  :=
    fun isSat => isCauseOut {
      backgroundInsHold := isSat.backgroundInsHold
      backgroundOutHold := isSat.backgroundOutHold
    }
  
  def Not.elimCplEx
    (isNotCause: ¬ IsWeakCause salg cause d (Expr.cpl expr))
  :
    ∃ b,
      cause.IsWeaklySatisfiedByBackground b ∧
      (expr.interpretation salg b b).defMem d
  :=
    byContradiction fun nex =>
      let allSatPos := nex.toAll fun _ nand => nand.toImpl
      isNotCause (cpl cause (allSatPos _))

  
  def ifThen
    {cond}
    (isCauseCond: IsWeakCause salg cause dC cond)
    (isCauseBody: IsWeakCause salg cause d body)
  :
    IsWeakCause salg cause d (Expr.ifThen cond body)
  :=
    fun isSat =>
      And.intro
        ⟨dC, (isCauseCond isSat)⟩
        (isCauseBody isSat)
  
  def elimIfThenCond
    {cond}
    (isCause: IsWeakCause salg cause d (Expr.ifThen cond body))
    (dC: salg.D)
    (otherDcOut:
      ∀ dOther,
        dOther ≠ dC →
        WeakSatIsStrongCauseOut salg cause dOther cond)
  :
    IsWeakCause salg cause dC cond
  :=
    fun isSat =>
      let ⟨⟨dCAlias, isPosCond⟩, _⟩ := isCause isSat
      let dEq: dCAlias = dC :=
        byContradiction fun neq =>
          otherDcOut dCAlias neq isSat isPosCond
      dEq ▸ isPosCond
  
  def elimIfThenBody
    {cond}
    (isCause: IsWeakCause salg cause d (Expr.ifThen cond body))
  :
    IsWeakCause salg cause d body
  :=
    fun isSat => (isCause isSat).right
  
  def Not.elimIfThen
    {cond}
    (isNotCause:
      ¬ IsWeakCause salg cause d (Expr.ifThen cond body))
  :
    Or
      (∀ dC, ¬ IsWeakCause salg cause dC cond)
      (¬ IsWeakCause salg cause d body)
  :=
    byContradiction fun nor =>
      let ⟨notAllNotCauseCond, isCauseBody⟩ := nor.toAnd
      let ⟨_, isCauseCond⟩ :=
        notAllNotCauseCond.toEx fun _ => Not.dne
      
      isNotCause (isCauseCond.ifThen isCauseBody.dne)
  
  
  def arbUn
    {cause: Cause salg.D}
    (isCause: IsWeakCause salg (cause.withBound x dX) d body)
  :
    IsWeakCause salg (cause.exceptX x) d (Expr.Un x body)
  :=
    fun isSat => ⟨dX, isCause (isSat.exceptToWithBound dX)⟩
  
  def elimArbUn
    (isCause: IsWeakCause salg cause d (Expr.Un x body))
    (dX: salg.D)
    -- Conjecture: this argument is unnecessary.
    -- If not, question: can we do with a weaker condition still?
    (otherDxOut:
      ∀ dOther,
        dOther ≠ dX →
        WeakSatIsStrongCauseOutUpdated
          salg cause d body x dOther)
  :
    IsWeakCause salg (cause.withBound x dX) d body
  :=
    fun {b c} isSat =>
      let ⟨dXAlias, isPos⟩ := isCause isSat.fromWithBound
      let dEq: dXAlias = dX :=
        byContradiction fun neq =>
          otherDxOut dXAlias neq isSat.fromWithBound isPos
      let cancelsPrev := Valuation.update.cancelsPreviousSet3
      let isPos :=
        cancelsPrev b x Set3.undetermined dX ▸
        cancelsPrev c x Set3.undetermined dX ▸
        dEq ▸
        isPos
      Expr.interpretation.isMonotonic.apxPosMem
        salg
        body
        isSat.satLeUpdatedB
        isSat.satLeUpdatedCPos
        isPos
  
  
  def arbIr
    {salg: Salgebra sig}
    {cause: Cause salg.D}
    {d: salg.D}
    
    (isCause: ∀ dX, IsWeakCause salg (cause.withBound x dX) d body)
  :
    IsWeakCause salg (cause.exceptX x) d (Expr.Ir x body)
  :=
    fun isSat dX => isCause dX (isSat.exceptToWithBound dX)
  
  
  def toSuperCause
    (isCause: IsWeakCause salg cause d expr)
    (le: cause ⊆ causeSuper)
  :
    IsWeakCause salg causeSuper d expr
  :=
    fun isSat => isCause (isSat.ofSuper le)
  
  def arbUnOf
    {causes: salg.D → Cause _}
    (isCause:
      ∀ dX, IsWeakCause salg ((causes dX).withBound x dX) d body)
  :
    IsWeakCause
      salg
      (Cause.arbUn fun dX => (causes dX).exceptX x)
      d
      (Expr.Ir x body)
  :=
    fun isSat dX =>
      let isSatArbUn := isSat.toWithBound dX
      isCause dX {
        contextInsHold :=
          fun inCins =>
            isSatArbUn.contextInsHold
              (inCins.elim
                (fun ⟨inCins, xNeq⟩ =>
                  Or.inl ⟨⟨dX, inCins, xNeq⟩, xNeq⟩)
                Or.inr)
        backgroundInsHold :=
          fun inBins =>
            isSatArbUn.backgroundInsHold
              (inBins.elim
                (fun ⟨inBins, xNeq⟩ =>
                  Or.inl ⟨⟨dX, inBins, xNeq⟩, xNeq⟩)
                Or.inr)
        backgroundOutHold :=
          fun inBout =>
            isSatArbUn.backgroundOutHold
              (inBout.elim
                (fun ⟨inBout, xNeq⟩ =>
                  Or.inl ⟨⟨dX, inBout, xNeq⟩, xNeq⟩)
                Or.inr)
      }
  
end IsWeakCause
