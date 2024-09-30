/-
  This file defines constructors and eliminators for the predicate
  `IsStrongCause`.
-/

import Utils.AProofSystem

/-
  A cause is (strongly) consistent if there exists a valuation
  that strongly satisfies it. Note that every cause is weakly
  consistent.
-/
def Cause.IsConsistent
  (cause: Cause D)
:
  Prop
:=
  ∀ vv, vv ∉ cause.backgroundIns ∨ vv ∉ cause.backgroundOut

/-
  The least valuation in the approximation order that strongly
  satisfies the background part of a cause.
-/
def Cause.IsConsistent.leastBackground
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
:
  Valuation D
:=
  fun x => {
    defMem := fun d => ⟨d, x⟩ ∈ cause.backgroundIns
    posMem := fun d => ⟨d, x⟩ ∉ cause.backgroundOut
    defLePos :=
      -- weird that this type annotation is necessary
      fun d (isDef: _ ∈ cause.backgroundIns) =>
        (isConsistent ⟨d, x⟩).elim
          (fun ninBins => (ninBins isDef).elim)
          id
  }

/-
  The least valuation in the approximation order that strongly
  satisfies the context part of a cause.
-/
def Cause.leastContext
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := fun d => ⟨d, x⟩ ∈ cause.contextIns
    posMem := Set.full
    defLePos := fun _ _ => trivial
  }

def Cause.IsConsistent.leastBackgroundIsSat
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
  (c: Valuation D)
:
  cause.backgroundOnly.IsStronglySatisfiedBy
    (isConsistent.leastBackground)
    c
:= {
  contextInsHold := nofun
  backgroundInsHold := id
  backgroundOutHold :=
    fun {dd xx} inBout =>
      (isConsistent ⟨dd, xx⟩).elim
        (fun _ => (· inBout))
        (fun ninbout => False.elim (ninbout inBout))
}

def Cause.IsConsistent.leastValsAreSat
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
:
  cause.IsStronglySatisfiedBy
    (leastBackground isConsistent)
    (leastContext cause)
:= {
  contextInsHold := id
  backgroundInsHold := id
  backgroundOutHold :=
    Cause.IsStronglySatisfiedBy.backgroundOutHold
      (leastBackgroundIsSat isConsistent (leastContext cause))
}

def Cause.IsConsistent.leastIsLeast
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
  (b: Valuation D)
  (bSat: cause.backgroundOnly.IsStronglySatisfiedBy b b)
:
  isConsistent.leastBackground ⊑ b
:=
  fun _ => {
    defLe := fun _ => bSat.backgroundInsHold
    posLe := fun _ => flip bSat.backgroundOutHold
  }


def Cause.IsConsistent.withBound
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
  (x: Nat)
  (d: D)
:
  (cause.withBound x d).IsConsistent
:=
  fun ⟨dd, xx⟩ =>
    (isConsistent ⟨dd, xx⟩).elim
      (fun ninBins =>
        if h: xx = x ∧ dd = d then
          Or.inr (fun inBout =>
            inBout.elim
              (fun ⟨_, xNeq⟩ => xNeq h.left)
              (fun ⟨dNeq, _⟩ => dNeq h.right))
        else
          Or.inl (fun inBins =>
            inBins.elim
              (fun ⟨inBins, _⟩ => ninBins inBins)
              (h ∘ And.symm)))
      (fun ninBout =>
        if h: xx = x ∧ dd ≠ d then
          Or.inl (fun inBins =>
            inBins.elim
              (fun ⟨_, xNeq⟩ => xNeq h.left)
              (fun ⟨dEq, _⟩ => h.right dEq))
        else
          Or.inr (fun inBins =>
            inBins.elim
              (fun ⟨inBins, _⟩ => ninBout inBins)
              (fun ⟨dNeq, xEq⟩ => h ⟨xEq, dNeq⟩)))

def Cause.IsConsistent.leastBackgroundUpdateEq
  {cause: Cause D}
  (isCons: cause.IsConsistent)
  (x: Nat)
  (d: D)
:
  let isConsWith: (cause.withBound x d).IsConsistent :=
    isCons.withBound x d
  
  isCons.leastBackground.update x d
    =
  isConsWith.leastBackground
:=
  funext fun xx =>
    if h: xx = x then
      Valuation.update.eqBoundOfEq _ h.symm d ▸
      Eq.symm
        (Set3.eqJust
          (fun _ isPos =>
            byContradiction fun dNeq =>
              isPos (Or.inr ⟨dNeq, h⟩))
          (Or.inr (And.intro rfl h)))
    else
      Valuation.update.eqOrig _ (Ne.symm h) _ ▸
      Set3.eq
        (funext fun _ =>
          propext
            (Iff.intro
              (fun isDef => Or.inl ⟨isDef, h⟩)
              (fun isDefWith =>
                isDefWith.elim
                  And.left
                  (fun ⟨_, xEq⟩ => (h xEq).elim))))
        (funext fun _ =>
          propext
            (Iff.intro
              (fun isPos inBoutWith =>
                inBoutWith.elim
                  (fun ⟨inBout, _⟩ => isPos inBout)
                  (fun ⟨_, xEq⟩ => h xEq))
              (fun isPosWith inBout =>
                isPosWith (Or.inl ⟨inBout, h⟩))))

def Cause.leastContextUpdateLe
  (cause: Cause D)
  (x: Nat)
  (d: D)
:
  cause.leastContext.update x d
    ≤
  (cause.withBound x d).leastContext
:=
  fun xx => {
    defLe :=
      fun _ isDefWith =>
        if h: xx = x then
          Or.inr ⟨
            Valuation.update.inDef.eq (h ▸ isDefWith),
            h,
          ⟩
        else
          Or.inl ⟨
            Valuation.update.inNeqElim.defMem
              isDefWith (Ne.symm h),
            h,
          ⟩
    posLe := fun _ _ => trivial
  }


def IsStrongCause.Not.exSatNotDef
  (notCause: ¬ IsStrongCause salg cause d expr)
:
  ∃ b c,
    cause.IsStronglySatisfiedBy b c ∧
    ¬ (expr.interpretation salg b c).defMem d
:=
  -- We just invert the quantifiers.
  notCause.toEx
    fun _ tmp0 => tmp0.toEx fun _ tmp1 => tmp1.implToAnd

def IsStrongCause.Not.isConsistent
  (notCause: ¬ IsStrongCause salg cause d expr)
:
  cause.IsConsistent
:=
  let ⟨b, _c, isSat, _notDef⟩ :=
    IsStrongCause.Not.exSatNotDef notCause
  
  fun ⟨d, x⟩ =>
    if h: (b x).defMem d then
      Or.inr (isSat.backgroundOutHold · (Set3.defLePos _ h))
    else
      Or.inl (h ∘ isSat.backgroundInsHold)


def IsStrongCause.var
  (isIns: ⟨d, x⟩ ∈ cause.contextIns)
:
  IsStrongCause salg cause d (Expr.var x)
:=
  fun isSat => isSat.contextInsHold isIns

def IsStrongCause.op
  {salg: Salgebra sig}
  {d: salg.D}
  {cause: Cause salg.D}
  
  (argVals: sig.Args opr salg.D)
  (argsCauseD: d ∈ salg.I opr argVals)
  (isCauseArgs:
    ∀ param (dArg: argVals param),
      IsStrongCause salg cause dArg (argExprs param))
:
  IsStrongCause salg cause d (Expr.op opr argExprs)
:=
  fun {b c} isSat =>
    salg.isMonotonic
      opr
      argVals
      (fun param =>
        ((argExprs param).interpretation salg b c).defMem)
      (fun param d inArgVals =>
        isCauseArgs param ⟨d, inArgVals⟩ isSat)
      argsCauseD

def IsStrongCause.unL
  (isCause: IsStrongCause salg cause d left)
  (rite: Expr _)
:
  IsStrongCause salg cause d (Expr.un left rite)
:=
  Or.inl ∘ isCause

def IsStrongCause.unR
  (isCause: IsStrongCause salg cause d rite)
  (left: Expr _)
:
  IsStrongCause salg cause d (Expr.un left rite)
:=
  Or.inr ∘ isCause

def IsStrongCause.ir
  (isCauseLeft: IsStrongCause salg cause d left)
  (isCauseRite: IsStrongCause salg cause d rite)
:
  IsStrongCause salg cause d (Expr.ir left rite)
:=
  fun isSat =>
    And.intro (isCauseLeft isSat) (isCauseRite isSat)

def IsStrongCause.not
  {expr: Expr sig}
  (cause: Cause salg.D)
  (isCauseOut:
    {b: Valuation salg.D} →
    cause.backgroundOnly.IsStronglySatisfiedBy b b →
    ¬ (expr.interpretation salg b b).posMem d)
:
  IsStrongCause salg cause d (Expr.cpl expr)
:=
  fun isSat => isCauseOut {
    contextInsHold := nofun
    backgroundInsHold := isSat.backgroundInsHold
    backgroundOutHold := isSat.backgroundOutHold
  }

def IsStrongCause.ifThen
  {cond}
  (isCauseCond: IsStrongCause salg cause dC cond)
  (isCauseBody: IsStrongCause salg cause d body)
:
  IsStrongCause salg cause d (Expr.ifThen cond body)
:=
  fun isSat =>
    And.intro
      ⟨dC, (isCauseCond isSat)⟩
      (isCauseBody isSat)

def IsStrongCause.arbUn
  {cause: Cause salg.D}
  (isCause: IsStrongCause salg (cause.withBound x dX) d body)
:
  IsStrongCause salg cause d (Expr.Un x body)
:=
  fun isSat => ⟨
    dX,
    isCause (cause.withBoundSatOfSatStrong isSat),
  ⟩

def IsStrongCause.arbIr
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  (isCause:
    ∀ dX, IsStrongCause salg (cause.withBound x dX) d body)
:
  IsStrongCause salg cause d (Expr.Ir x body)
:=
  fun isSat dX =>
    isCause dX (cause.withBoundSatOfSatStrong isSat)


def IsStrongCause.Not.elimVar
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.var x))
:
  ¬ ⟨d, x⟩ ∈ cause.contextIns
:=
  fun isIns => isNotCause (IsStrongCause.var isIns)

def IsStrongCause.Not.elimOp
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.op opr argExprs))
  (argVals: sig.Args opr salg.D)
  (argsCauseD: d ∈ salg.I opr argVals)
:
  ∃ param, ∃ (dArg: argVals param),
    ¬ IsStrongCause salg cause dArg (argExprs param)
:=
  byContradiction fun nex =>
    let allHaveCause:
      ∀ param (dArg: argVals param),
        IsStrongCause salg cause dArg (argExprs param)
    :=
      nex.toAll fun _ tmp => tmp.toAll fun _ isCause => isCause.dne
    
    let isCause:
      IsStrongCause salg cause d (Expr.op opr argExprs)
    :=
      IsStrongCause.op argVals argsCauseD allHaveCause
    
    isNotCause isCause

def IsStrongCause.Not.elimUnL
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.un left rite))
:
  ¬ IsStrongCause salg cause d left
:=
  fun isCause => isNotCause (isCause.unL rite)

def IsStrongCause.Not.elimUnR
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.un left rite))
:
  ¬ IsStrongCause salg cause d rite
:=
  fun isCause => isNotCause (isCause.unR left)

def IsStrongCause.Not.elimIr
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.ir left rite))
:
  Or
    (¬ IsStrongCause salg cause d left)
    (¬ IsStrongCause salg cause d rite)
:=
  byContradiction fun nor =>
    let ⟨isCauseLeft, isCauseRite⟩ := nor.toAnd
    
    isNotCause (IsStrongCause.ir isCauseLeft.dne isCauseRite.dne)

def IsStrongCause.Not.elimNotEx
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.cpl expr))
:
  ∃ b,
    cause.backgroundOnly.IsStronglySatisfiedBy b b ∧
    (expr.interpretation salg b b).posMem d
:=
  byContradiction fun nex =>
    let allSatPos := nex.toAll fun _ nand => nand.toImpl
    isNotCause (IsStrongCause.not cause (allSatPos _))

def IsStrongCause.Not.elimNot
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.cpl expr))
:
  let isConsistent := IsStrongCause.Not.isConsistent isNotCause
  let b := isConsistent.leastBackground
  
  cause.backgroundOnly.IsStronglySatisfiedBy b b ∧
  (expr.interpretation salg b b).posMem d
:=
  let isConsistent := IsStrongCause.Not.isConsistent isNotCause
  let ⟨b, isSat, isPos⟩ := IsStrongCause.Not.elimNotEx isNotCause
  let isLeB := isConsistent.leastIsLeast b isSat
  
  let isLeExpr :=
    Expr.interpretation.isMonotonic.approximation
      salg expr isLeB isLeB
  
  And.intro
    (isConsistent.leastBackgroundIsSat _)
    (isLeExpr.posLe isPos)

def IsStrongCause.Not.elimIfThen
  {cond}
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.ifThen cond body))
:
  Or
    (∀ dC, ¬ IsStrongCause salg cause dC cond)
    (¬ IsStrongCause salg cause d body)
:=
  byContradiction fun nor =>
    let ⟨notAllNotCauseCond, isCauseBody⟩ := nor.toAnd
    let ⟨_, isCauseCond⟩ :=
      notAllNotCauseCond.toEx fun _ => Not.dne
    
    isNotCause (isCauseCond.ifThen isCauseBody.dne)

def IsStrongCause.Not.elimArbUn
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.Un x body))
  (dX: salg.D)
:
  ¬ IsStrongCause salg (cause.withBound x dX) d body
:=
  fun isCause => isNotCause isCause.arbUn

def IsStrongCause.Not.elimArbIr
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.Ir x body))
:
  ∃ dX, ¬ IsStrongCause salg (cause.withBound x dX) d body
:=
  byContradiction fun nex =>
    let allHaveCause:
      ∀ dX, IsStrongCause salg (cause.withBound x dX) d body
    :=
      nex.toAll fun _ isCause => isCause.dne
    
    isNotCause (IsStrongCause.arbIr allHaveCause)


def IsStrongCause.Not.notDefUnderLeast
  (notCause: ¬ IsStrongCause salg cause d expr)
:
  let isConsistent := IsStrongCause.Not.isConsistent notCause
  
  Not
    (Set3.defMem
      (expr.interpretation
        salg
        isConsistent.leastBackground
        cause.leastContext)
      d)
:=
  match expr with
  | Expr.var _ =>
    fun isDef => (IsStrongCause.Not.elimVar notCause isDef).elim
  |
    Expr.op _ argExprs =>
    let isConsistent := IsStrongCause.Not.isConsistent notCause
    let isDefToExNotCause :=
      IsStrongCause.Not.elimOp
        notCause
        (fun param d =>
          Set3.defMem
            ((argExprs param).interpretation
              salg isConsistent.leastBackground cause.leastContext)
            d)
    fun isDef =>
      let ⟨_param, ⟨_dArg, isDefArg⟩, notCause⟩ :=
        isDefToExNotCause isDef
      
      (notDefUnderLeast notCause) isDefArg
  |
    Expr.un _ _ =>
    let notCauseLeft := IsStrongCause.Not.elimUnL notCause
    let notCauseRite := IsStrongCause.Not.elimUnR notCause
    let ihLeft := notDefUnderLeast notCauseLeft
    let ihRite := notDefUnderLeast notCauseRite
    (Or.elim · ihLeft ihRite)
  |
    Expr.ir _ _ =>
    let notCauseLeftOrRite := IsStrongCause.Not.elimIr notCause
    notCauseLeftOrRite.elim
      (fun notCauseLeft =>
        let ihLeft := notDefUnderLeast notCauseLeft
        fun isDef => ihLeft isDef.left)
      (fun notCauseRite =>
        let ihRite := notDefUnderLeast notCauseRite
        fun isDef => ihRite isDef.right)
  |
    Expr.cpl _ =>
    let ⟨_isSat, isPos⟩ := IsStrongCause.Not.elimNot notCause
    (· isPos)
  |
    Expr.ifThen _ _ =>
    let notCauseCondOrBody := IsStrongCause.Not.elimIfThen notCause
    notCauseCondOrBody.elim
      (fun notCauseCond =>
        fun ⟨⟨dC, isDef⟩, _⟩ =>
          notDefUnderLeast (notCauseCond dC) isDef)
      (fun notCauseBody =>
        let ihBody := notDefUnderLeast notCauseBody
        fun ⟨_, isDef⟩ => ihBody isDef)
  |
    Expr.Un x body =>
      let isConsistent := IsStrongCause.Not.isConsistent notCause
      fun ⟨dX, isDef⟩ =>
        let notCause := IsStrongCause.Not.elimArbUn notCause dX
        let ih := notDefUnderLeast notCause
        let leastBEq := isConsistent.leastBackgroundUpdateEq x dX
        
        let interpLe :=
          Expr.interpretation.isMonotonic.standard
            salg
            body
            (isConsistent.leastBackground.update x dX)
            (cause.leastContextUpdateLe x dX)
        
        ih (leastBEq ▸ interpLe.defLe isDef)
  |
    Expr.Ir x body =>
      let isConsistent := IsStrongCause.Not.isConsistent notCause
      fun isDef =>
        let ⟨dX, notCause⟩ := IsStrongCause.Not.elimArbIr notCause
        let leastBEq := isConsistent.leastBackgroundUpdateEq x dX
        
        let interpLe :=
          Expr.interpretation.isMonotonic.standard
            salg
            body
            (isConsistent.leastBackground.update x dX)
            (cause.leastContextUpdateLe x dX)
        
        notDefUnderLeast
          notCause (leastBEq ▸ interpLe.defLe (isDef dX))


def IsStrongCause.elimVar
  (isCause: IsStrongCause salg cause d (Expr.var x))
  (isConsistent: cause.IsConsistent)
:
  ⟨d, x⟩ ∈ cause.contextIns
:=
  isCause isConsistent.leastValsAreSat

def IsStrongCause.notVar
  (isConsistent: cause.IsConsistent)
  (ninCins: ⟨d, x⟩ ∉ cause.contextIns)
:
  ¬ IsStrongCause salg cause d (Expr.var x)
:=
  fun isCause => ninCins (isCause.elimVar isConsistent)


def IsStrongCause.notOp
  {salg: Salgebra sig}
  {d: salg.D}
  {cause: Cause salg.D}
  
  (causeIsConsistentOrDInOpIsPossible:
    cause.IsConsistent ∨ ∃ argVals, d ∈ salg.I opr argVals)
  (allCausesNot:
    ∀ argVals: sig.Args opr salg.D,
      d ∈ salg.I opr argVals →
    ∃ param, ∃ (dArg: argVals param),
      ¬ IsStrongCause salg cause dArg (argExprs param))
:
  ¬ IsStrongCause salg cause d (Expr.op opr argExprs)
:=
  let isConsistent :=
    causeIsConsistentOrDInOpIsPossible.elim
      id
      (fun ⟨argVals, dIn⟩ =>
        let ⟨_, _, notCause⟩ := allCausesNot argVals dIn
        IsStrongCause.Not.isConsistent notCause)
  
  fun isCause =>
    let isDef := isCause isConsistent.leastValsAreSat
    let ⟨_param, ⟨_dArg, dArgIsDef⟩, notCause⟩ :=
      allCausesNot
        (fun param d =>
          Set3.defMem
            ((argExprs param).interpretation
              salg
              isConsistent.leastBackground
              cause.leastContext)
            d)
        isDef
    Not.notDefUnderLeast notCause dArgIsDef

def IsStrongCause.elimOp
  {salg: Salgebra sig}
  {d: salg.D}
  {cause: Cause salg.D}
  
  (isCause: IsStrongCause salg cause d (Expr.op opr argExprs))
  (causeIsConsistentOrDInOpIsPossible:
    cause.IsConsistent ∨ ∃ argVals, d ∈ salg.I opr argVals)
:
  ∃ (argVals: sig.Args opr salg.D),
    d ∈ salg.I opr argVals ∧
    ∀ param (dArg: argVals param),
      IsStrongCause salg cause dArg (argExprs param)
:=
  byContradiction fun nex =>
    let allExNotCause :=
      nex.toAll
        fun _ nand dIn =>
          (nand.toImpl dIn).toEx
            fun _ nall => nall.toEx fun _ => id
    
    IsStrongCause.notOp
      causeIsConsistentOrDInOpIsPossible
      allExNotCause
      isCause


def IsStrongCause.notUn
  (notCauseLeft: ¬ IsStrongCause salg cause d left)
  (notCauseRite: ¬ IsStrongCause salg cause d rite)
:
  ¬ IsStrongCause salg cause d (Expr.un left rite)
:=
  fun isCause => 
    let isConsistent := IsStrongCause.Not.isConsistent notCauseLeft
    (isCause isConsistent.leastValsAreSat).elim
      (Not.notDefUnderLeast notCauseLeft)
      (Not.notDefUnderLeast notCauseRite)

def IsStrongCause.elimUn
  (isCause: IsStrongCause salg cause d (Expr.un left rite))
:
  Or
    (IsStrongCause salg cause d left)
    (IsStrongCause salg cause d rite)
:=
  byContradiction fun nor =>
    let ⟨notCauseLeft, notCauseRite⟩ := nor.toAnd
    IsStrongCause.notUn notCauseLeft notCauseRite isCause


def IsStrongCause.notIrLeft
  (notCauseLeft: ¬ IsStrongCause salg cause d left)
:
  ¬ IsStrongCause salg cause d (Expr.ir left rite)
:=
  let isConsistent := IsStrongCause.Not.isConsistent notCauseLeft
  fun isCause =>
    let ⟨isDef, _⟩ := isCause isConsistent.leastValsAreSat
    Not.notDefUnderLeast notCauseLeft isDef

def IsStrongCause.notIrRite
  (notCauseRite: ¬ IsStrongCause salg cause d rite)
:
  ¬ IsStrongCause salg cause d (Expr.ir left rite)
:=
  let isConsistent := IsStrongCause.Not.isConsistent notCauseRite
  fun isCause =>
    let ⟨_, isDef⟩ := isCause isConsistent.leastValsAreSat
    Not.notDefUnderLeast notCauseRite isDef

def IsStrongCause.elimIr
  (isCause: IsStrongCause salg cause d (Expr.ir left rite))
:
  And
    (IsStrongCause salg cause d left)
    (IsStrongCause salg cause d rite)
:=
  byContradiction fun nand =>
    nand.toOr.elim
      (IsStrongCause.notIrLeft · isCause)
      (IsStrongCause.notIrRite · isCause)


def IsStrongCause.elimNot
  (_isCause: IsStrongCause salg cause d (Expr.cpl expr))
  (_isConsistent: cause.IsConsistent)
:
  True -- TODO is there anything useful that can be returned???
:=
  trivial


def IsStrongCause.notIfThenCond
  {cond}
  (notCauseCond: ∀ dC, ¬ IsStrongCause salg cause dC cond)
  (d: salg.D)
  (body: Expr _)
:
  ¬ IsStrongCause salg cause d (Expr.ifThen cond body)
:=
  fun isCause =>
    let isConsistent :=
      IsStrongCause.Not.isConsistent (notCauseCond d)
    let ⟨⟨dC, isDef⟩, _⟩ := isCause isConsistent.leastValsAreSat
    Not.notDefUnderLeast (notCauseCond dC) isDef

def IsStrongCause.notIfThenBody
  (notCauseBody: ¬ IsStrongCause salg cause d body)
  (cond: Expr _)
:
  ¬ IsStrongCause salg cause d (Expr.ifThen cond body)
:=
  fun isCause =>
    let isConsistent :=
      IsStrongCause.Not.isConsistent notCauseBody
    let ⟨_, isDef⟩ := isCause isConsistent.leastValsAreSat
    Not.notDefUnderLeast notCauseBody isDef

def IsStrongCause.elimIfThen
  {cond}
  (isCause: IsStrongCause salg cause d (Expr.ifThen cond body))
:
  And
    (∃ dC, IsStrongCause salg cause dC cond)
    (IsStrongCause salg cause d body)
:=
  byContradiction fun nand =>
    nand.toOr.elim
      (fun nex =>
        let allCause := nex.toAll fun _ => id
        IsStrongCause.notIfThenCond allCause d body isCause)
      (fun notCause =>
        IsStrongCause.notIfThenBody notCause cond isCause)


def IsStrongCause.notArbUn
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (notCause: ∀ dX, ¬ IsStrongCause salg (cause.withBound x dX) d body)
  (isConsistent: cause.IsConsistent)
:
  ¬ IsStrongCause salg cause d (Expr.Un x body)
:=
  fun isCause =>
    let ⟨dX, isDef⟩ := isCause isConsistent.leastValsAreSat
    let leastBEq := isConsistent.leastBackgroundUpdateEq x dX
    
    let interpLe :=
      Expr.interpretation.isMonotonic.standard
        salg
        body
        (isConsistent.leastBackground.update x dX)
        (cause.leastContextUpdateLe x dX)
    
    Not.notDefUnderLeast
      (notCause dX) (leastBEq ▸ interpLe.defLe isDef)

def IsStrongCause.elimArbUn
  (isCause: IsStrongCause salg cause d (Expr.Un x body))
  (isConsistent: cause.IsConsistent)
:
  ∃ dX, IsStrongCause salg (cause.withBound x dX) d body
:=
  byContradiction fun nex =>
    let allNotCause := nex.toAll fun _ => id
    IsStrongCause.notArbUn allNotCause isConsistent isCause


def IsStrongCause.notArbIr
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (notCause: ∃ dX, ¬ IsStrongCause salg (cause.withBound x dX) d body)
  (isConsistent: cause.IsConsistent)
:
  ¬ IsStrongCause salg cause d (Expr.Ir x body)
:=
  fun isCause =>
    let ⟨dX, notCause⟩ := notCause
    let leastBEq := isConsistent.leastBackgroundUpdateEq x dX
    let isDef := isCause isConsistent.leastValsAreSat dX
    
    let interpLe :=
      Expr.interpretation.isMonotonic.standard
        salg
        body
        (isConsistent.leastBackground.update x dX)
        (cause.leastContextUpdateLe x dX)
    
    Not.notDefUnderLeast
      notCause (leastBEq ▸ interpLe.defLe isDef)

def IsStrongCause.elimArbIr
  (isCause: IsStrongCause salg cause d (Expr.Ir x body))
  (isConsistent: cause.IsConsistent)
:
  ∀ dX, IsStrongCause salg (cause.withBound x dX) d body
:=
  byContradiction fun nall =>
    let exHasNoCause := nall.toEx fun _ => id
    IsStrongCause.notArbIr exHasNoCause isConsistent isCause
