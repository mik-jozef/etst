/-
  This file defines constructors and eliminators for the predicate
  `IsWeakCause`, as well as some related helper definitions.
-/

import WFC.Ch6_S1_AProofSystem
import Utils.PairExpr

open PairExpr


def Cause.IsWeaklySatisfiedBy.toSubcause
  {cause: Cause D}
  (isSat: cause.IsWeaklySatisfiedBy b c)
  (isSub: subcause ⊆ cause)
:
  subcause.IsWeaklySatisfiedBy b c
:= {
  contextInsHold :=
    fun inCinsWith =>
      isSat.contextInsHold (isSub.cinsLe inCinsWith)
  backgroundInsHold :=
    fun inBinsWith =>
      isSat.backgroundInsHold (isSub.binsLe inBinsWith)
  backgroundOutHold :=
    fun inBoutWith =>
      isSat.backgroundOutHold (isSub.boutLe inBoutWith)
}

def Cause.IsWeaklySatisfiedBy.exceptToWithBound
  {cause: Cause D}
  {x: Nat}
  (isSat: (cause.exceptVar x).IsWeaklySatisfiedBy b c)
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
  (isSat: cause.IsWeaklySatisfiedBy b c)
  (d: D)
:
  (cause.withBound x d).IsWeaklySatisfiedBy
    (b.update x d)
    (c.update x d)
:=
  (isSat.ofSuper (cause.exceptVarIsSub x)).exceptToWithBound d

def Cause.IsWeaklySatisfiedBy.updateSet3SatOfSatWithBound
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
        Valuation.updateSet3.eqBoundOfEq c h _ ▸ trivial
      else
        Valuation.updateSet3.eqOrig c h _ ▸
        isSat.contextInsHold (Or.inl ⟨inCins, Ne.symm h⟩)
  backgroundInsHold :=
    fun {_dd xx} inBins =>
      if h: x = xx then
        Valuation.updateSet3.eqBoundOfEq b h _ ▸ trivial
      else
        Valuation.updateSet3.eqOrig b h _ ▸
        isSat.backgroundInsHold (Or.inl ⟨inBins, Ne.symm h⟩)
  backgroundOutHold :=
    fun {_dd xx} inBout =>
      if h: x = xx then
        Valuation.updateSet3.eqBoundOfEq b h _ ▸ nofun
      else
        Valuation.updateSet3.eqOrig b h _ ▸
        isSat.backgroundOutHold (Or.inl ⟨inBout, Ne.symm h⟩)
}

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
  The least valuation in the standard order that weakly satisfies
  the context part of a cause.
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
  Returns the valuation closest to `v` that satisfies `cause`.
  
  Distance: think Hamming distance, with "undetermined" being
  closer to "definite non/member" than these are to each other.
-/
def Cause.closestWeakSatVal
  (cause: Cause D)
  (v: Valuation D)
:
  Valuation D
:=
  fun x => {
    defMem :=
      fun d => (v x).defMem d ∧ ¬ cause.backgroundOut ⟨d, x⟩
    posMem :=
      fun d => (v x).posMem d ∨ cause.backgroundIns ⟨d, x⟩
    defLePos :=
      fun _ ⟨isDef, _⟩ => Or.inl isDef.toPos
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

def Cause.closestWeakSatValIsSat
  (cause: Cause D)
  (v: Valuation D)
:
  cause.IsWeaklySatisfiedBy
    (cause.closestWeakSatVal v)
    cause.leastContextStd
:= {
  contextInsHold := id
  backgroundInsHold :=
    fun inBins => Or.inr inBins
  backgroundOutHold :=
    fun inBout ⟨_, ninBout⟩ => ninBout inBout
}

def Cause.leClosestOfSatUnionB
  (isSat:
    Cause.IsWeaklySatisfiedBy
      (Cause.union cause (Cause.ofValPos v Valuation.empty))
      b
      c)
:
  b ⊑ cause.closestWeakSatVal v
:=
  fun _ => {
    defLe :=
      fun _ isDef =>
        byContradiction fun notDefClosest =>
          let inBout :=
            notDefClosest.toOr.elim
              Or.inr (Or.inl ∘ Not.dne)
          isSat.backgroundOutHold inBout isDef
    posLe :=
      fun _ => isSat.backgroundInsHold ∘ Or.symm
  }

def Cause.leClosestOfSatUnionBUpdated
  {cause: Cause D}
  (isSat:
    Cause.IsWeaklySatisfiedBy
      (Cause.union
        (cause.withBound x dX)
        (Cause.ofValPos (v.update x dX) Valuation.empty))
      b
      c)
:
  b ⊑ (cause.closestWeakSatVal v).update x dX
:=
  fun xx =>
    if h: x = xx then
      Valuation.update.eqBoundOfEq _ h dX ▸
      {
        defLe :=
          fun _ isDef =>
            byContradiction fun neq =>
              (isSat.elimUnL.backgroundOutHold
                (Or.inr ⟨neq, h.symm⟩)
                isDef)
        posLe :=
          fun _ dEq =>
            isSat.elimUnL.backgroundInsHold (Or.inr ⟨dEq, h.symm⟩)
      }
    else
      Valuation.update.eqOrig _ h dX ▸
      {
        defLe :=
          fun _ isDef =>
            byContradiction fun notDefClosest =>
              let inBout :=
                notDefClosest.toOr.elim
                  (fun notDef =>
                    show _ ∨ ¬ (v.update x dX xx).defMem _ from
                    Valuation.update.eqOrig v h dX ▸
                    Or.inr notDef)
                  (fun inBout =>
                    Or.inl (Or.inl ⟨inBout.dne, Ne.symm h⟩))
              isSat.backgroundOutHold inBout isDef
        posLe :=
          fun _ => isSat.backgroundInsHold ∘ fun isPosClosest =>
            isPosClosest.elim
              (fun isPos =>
                let isPosUpdated: (v.update x dX xx).posMem _ :=
                  Valuation.update.eqOrig v h dX ▸ isPos
                Or.inr isPosUpdated)
              (fun inBins => Or.inl (Or.inl ⟨inBins, Ne.symm h⟩))
      }


namespace IsWeakCause
  def hurrDurrElim
    (isCause: IsWeakCause salg cause d expr)
    {R: Sort*}
    (goalInC:
      Set3.posMem
        (expr.interpretation
          salg
          cause.leastBackgroundStd
          cause.leastContextStd)
        d →
      R)
  :
    R
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
  
  def elimOp
    {salg: Salgebra sig}
    {cause: Cause salg.D}
    {d: salg.D}
    
    (isCause: IsWeakCause salg cause d (Expr.op opr argExprs))
    (v: Valuation salg.D)
  :
    ∃ (argVals: sig.Args opr salg.D),
      salg.I opr argVals d ∧
      ∀ param (dArg: argVals param),
        IsWeakCause
          salg
          (cause.union (Cause.ofValPos v Valuation.empty))
          dArg
          (argExprs param)
  :=
    let isPos := isCause (cause.closestWeakSatValIsSat v)
    
    ⟨
      fun param =>
        Set3.posMem
          ((argExprs param).interpretation
            salg
            (cause.closestWeakSatVal v)
            cause.leastContextStd),
      isPos,
      fun _ ⟨_, dInArg⟩ _ _ isSat =>
        Expr.interpretation.isMonotonic.apxPosMem
          (Cause.leClosestOfSatUnionB isSat)
          (fun _ _ => isSat.contextInsHold ∘ Or.inl)
          dInArg
    ⟩
  
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
  
  def unLeft
    (isCause: IsWeakCause pairSalgebra cause d left)
    (rite: Expr _)
  :
    IsWeakCause pairSalgebra cause d (unExpr left rite)
  :=
    Or.inl ∘ isCause
  
  def unRite
    (isCause: IsWeakCause pairSalgebra cause d rite)
    (left: Expr _)
  :
    IsWeakCause pairSalgebra cause d (unExpr left rite)
  :=
    Or.inr ∘ isCause
  
  def elimUn
    (isCause: IsWeakCause pairSalgebra cause d (unExpr left rite))
    (v: Valuation Pair)
  :
    Or
      (IsWeakCause
        pairSalgebra
        (cause.union (Cause.ofValPos v Valuation.empty))
        d
        left)
      (IsWeakCause
        pairSalgebra
        (cause.union (Cause.ofValPos v Valuation.empty))
        d
        rite)
  :=
    (isCause (cause.closestWeakSatValIsSat v)).elim
      (fun isPosL =>
        Or.inl fun isSat =>
          Expr.interpretation.isMonotonic.apxPosMem
            (cause.leClosestOfSatUnionB isSat)
            (fun _ _ => isSat.contextInsHold ∘ Or.inl)
            isPosL)
      (fun isPosR =>
        Or.inr fun isSat =>
          Expr.interpretation.isMonotonic.apxPosMem
            (cause.leClosestOfSatUnionB isSat)
            (fun _ _ => isSat.contextInsHold ∘ Or.inl)
            isPosR)
  
  def elimIrLeft
    (isCause:
      IsWeakCause pairSalgebra cause d (irExpr left rite))
  :
    IsWeakCause pairSalgebra cause d left
  :=
    fun isSat => (isCause isSat).left
  
  def elimIrRite
    (isCause:
      IsWeakCause pairSalgebra cause d (irExpr left rite))
  :
    IsWeakCause pairSalgebra cause d rite
  :=
    fun isSat => (isCause isSat).right
  
  def elimIr
    (isCause: IsWeakCause pairSalgebra cause d (irExpr left rite))
  :
    And
      (IsWeakCause pairSalgebra cause d left)
      (IsWeakCause pairSalgebra cause d rite)
  :=
    ⟨elimIrLeft isCause, elimIrRite isCause⟩
  
  def elimCond
    (isCause:
      IsWeakCause pairSalgebra cause d (condExpr expr))
    (v: Valuation Pair)
  :
    let extCause := cause.union (Cause.ofValPos v Valuation.empty)
    ∃ dE, IsWeakCause pairSalgebra extCause dE expr
  :=
    let ⟨dE, isPosCond⟩ :=
      isCause (cause.closestWeakSatValIsSat v)
    ⟨
      dE,
      fun isSat =>
        Expr.interpretation.isMonotonic.apxPosMem
          (cause.leClosestOfSatUnionB isSat)
          (fun _ _ => isSat.contextInsHold ∘ Or.inl)
          isPosCond
    ⟩
   
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

  
  def arbUn
    {cause: Cause salg.D}
    (isCause: IsWeakCause salg (cause.withBound x dX) d body)
  :
    IsWeakCause salg (cause.exceptVar x) d (Expr.arbUn x body)
  :=
    fun isSat => ⟨dX, isCause (isSat.exceptToWithBound dX)⟩
  
  def arbUnOf
    {causes: salg.D → Cause _}
    (isCause:
      ∀ dX, IsWeakCause salg ((causes dX).withBound x dX) d body)
  :
    IsWeakCause
      salg
      (Cause.arbUn fun dX => (causes dX).exceptVar x)
      d
      (Expr.arbIr x body)
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
  
  def elimArbUn
    (isCause: IsWeakCause salg cause d (Expr.arbUn x body))
    (v: Valuation salg.D)
  :
    ∃ dX,
      IsWeakCause
        salg
        ((cause.withBound x dX).union
          (Cause.ofValPos (v.update x dX) Valuation.empty))
        d
        body
:=
  let ⟨dX, isPos⟩ := isCause (cause.closestWeakSatValIsSat v)
  
  ⟨
    dX,
    fun isSat =>
      Expr.interpretation.isMonotonic.apxPosMem
        (Cause.leClosestOfSatUnionBUpdated isSat)
        (fun xx dd inCinsUpdated =>
          if h: x = xx then
            let dEq: dd ∈ (Set3.just dX).posMem :=
              Valuation.update.eqBoundOfEq _ h dX ▸
              inCinsUpdated
            isSat.contextInsHold (Or.inl (Or.inr ⟨dEq, h.symm⟩))
          else
            let inCins: (cause.leastContextStd xx).posMem dd :=
              Valuation.update.eqOrig (cause.leastContextStd) h dX ▸
              inCinsUpdated
            isSat.contextInsHold
              (Or.inl (Or.inl ⟨inCins, Ne.symm h⟩)))
        isPos
  ⟩
  
  
  def arbIr
    {salg: Salgebra sig}
    {cause: Cause salg.D}
    {d: salg.D}
    
    (isCause: ∀ dX, IsWeakCause salg (cause.withBound x dX) d body)
  :
    IsWeakCause salg (cause.exceptVar x) d (Expr.arbIr x body)
  :=
    fun isSat dX => isCause dX (isSat.exceptToWithBound dX)
  
  def elimArbIr
    (isCause: IsWeakCause salg cause d (Expr.arbIr x body))
  :
    ∀ dX, IsWeakCause salg (cause.withBound x dX) d body
  :=
    fun dX b c isSat =>
      let bLe:
        b ⊑ (b.updateSet3 x Set3.undetermined).update x dX
      :=
        fun xx =>
          {
            defLe :=
              fun _ isDef =>
                if h: x = xx then
                  Valuation.update.eqBoundOfEq _ h dX ▸
                  byContradiction fun neq =>
                    isSat.backgroundOutHold
                      (Or.inr ⟨neq, rfl⟩)
                      (h ▸ isDef)
                else
                  Valuation.update.eqOrig _ h dX ▸
                  Valuation.updateSet3.eqOrig _ h _ ▸
                  isDef
            posLe :=
              fun _ isPosUpdated =>
                if h: x = xx then
                  let dEq: (Set3.just dX).posMem _ :=
                    Valuation.update.eqBoundOfEq _ h dX ▸
                    isPosUpdated
                  isSat.backgroundInsHold
                    (Or.inr ⟨dEq, h.symm⟩)
                else
                  Valuation.updateSet3.eqOrig b h _ ▸
                  Valuation.update.eqOrig _ h dX ▸
                  isPosUpdated
          }
      
      let cLe xx:
        ((c.updateSet3 x Set3.undetermined).update x dX xx).posMem
          ⊆
        (c xx).posMem
      :=
        fun dd inCinsUpdated =>
          if h: x = xx then
            let dEq: dd ∈ (Set3.just dX).posMem :=
              Valuation.update.eqBoundOfEq _ h dX ▸
              inCinsUpdated
            isSat.contextInsHold (Or.inr ⟨dEq, h.symm⟩)
          else
            Valuation.updateSet3.eqOrig c h _ ▸
            Valuation.update.eqOrig _ h dX ▸
            inCinsUpdated
      
      Expr.interpretation.isMonotonic.apxPosMem
        bLe
        cLe
        (isCause isSat.updateSet3SatOfSatWithBound dX)
  
  
  def toSuperCause
    (isCause: IsWeakCause salg cause d expr)
    (le: cause ⊆ causeSuper)
  :
    IsWeakCause salg causeSuper d expr
  :=
    fun isSat => isCause (isSat.ofSuper le)
  
  def toEmptyCinsCpl
    (isCause: IsWeakCause salg cause d (Expr.cpl expr))
  :
    IsWeakCause salg cause.background d (Expr.cpl expr)
  :=
  fun isSat isDef =>
    let isSatB: cause.IsWeaklySatisfiedBy _ Valuation.full := {
      contextInsHold := fun _ => trivial
      backgroundInsHold := isSat.backgroundInsHold
      backgroundOutHold := isSat.backgroundOutHold
    }
    isCause isSatB isDef
  
end IsWeakCause
