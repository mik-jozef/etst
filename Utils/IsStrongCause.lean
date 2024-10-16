/-
  This file defines constructors and eliminators for the predicate
  `IsStrongCause`, as well as some related helper definitions.
-/

import WFC.Ch6_S1_AProofSystem
import Utils.PairExpr


def Cause.IsInapplicable.toIsCauseInapplicable
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  
  (dl: DefList sig)
  (isInapplicable:
    Cause.IsInapplicable
      cause
      (dl.wellFoundedModel salg).nonmembers
      (dl.wellFoundedModel salg))
:
  IsCauseInapplicable
    salg
    dl
    (dl.wellFoundedModel salg).nonmembers
    cause
:=
  match isInapplicable with
  | IsInapplicable.blockedContextIns inCins inOutSet =>
    IsCauseInapplicable.blockedContextIns _ inCins inOutSet
  | IsInapplicable.blockedBackgroundIns inBins notPos =>
    let isOut := Out.isComplete _ _ notPos
    IsCauseInapplicable.blockedBackgroundIns _ inBins isOut
  | IsInapplicable.blockedBackgroundOut inBout isDef =>
    let isIns := Ins.isComplete _ _ isDef
    IsCauseInapplicable.blockedBackgroundOut _ inBout isIns


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

def Cause.IsConsistent.Not.isStrong
  (isNotConsistent: ¬ cause.IsConsistent)
  (d: salg.D)
  (expr: Expr sig)
:
  IsStrongCause salg cause d expr
:=
  let ⟨_, inIns, inOut⟩ :=
    isNotConsistent.toEx fun _ tmp => tmp.toAndLR
  fun isSat =>
    let isDef := isSat.backgroundInsHold inIns
    let niPos := isSat.backgroundOutHold inOut
    False.elim (niPos (Set3.defLePos _ isDef))


/-
  The least valuation in the approximation order that strongly
  satisfies the background part of a cause.
-/
def Cause.IsConsistent.leastBackgroundApx
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
def Cause.leastContextApx
  (cause: Cause D)
:
  Valuation D
:=
  fun x => {
    defMem := fun d => ⟨d, x⟩ ∈ cause.contextIns
    posMem := Set.full
    defLePos := fun _ _ => trivial
  }

def Cause.IsConsistent.leastBackgroundApxIsSat
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
  (c: Valuation D)
:
  cause.backgroundOnly.IsStronglySatisfiedBy
    (isConsistent.leastBackgroundApx)
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

def Cause.IsConsistent.leastValsApxAreSat
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
:
  cause.IsStronglySatisfiedBy
    (leastBackgroundApx isConsistent)
    (leastContextApx cause)
:= {
  contextInsHold := id
  backgroundInsHold := id
  backgroundOutHold :=
    Cause.IsStronglySatisfiedBy.backgroundOutHold
      (leastBackgroundApxIsSat isConsistent (leastContextApx cause))
}

def Cause.IsConsistent.leastIsLeApx
  {cause: Cause D}
  (isConsistent: cause.IsConsistent)
  (b: Valuation D)
  (bSat: cause.backgroundOnly.IsStronglySatisfiedBy b b)
:
  isConsistent.leastBackgroundApx ⊑ b
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

def Cause.IsConsistent.leastBackgroundApxUpdateLe
  {cause: Cause D}
  (isCons: cause.IsConsistent)
  (x: Nat)
  (d: D)
  (isSat: (cause.withBound x d).IsStronglySatisfiedBy b c)
:
  isCons.leastBackgroundApx.update x d ⊑ b
:=
  fun xx =>
    if h: xx = x then
      Valuation.update.eqBoundOfEq _ h.symm d ▸ {
        defLe :=
          fun _ dEq => isSat.backgroundInsHold (Or.inr ⟨dEq, h⟩)
        posLe :=
          fun _ isPos =>
            byContradiction fun neq =>
              isSat.backgroundOutHold (Or.inr ⟨neq, h⟩) isPos
      }
    else
      Valuation.update.eqOrig _ (Ne.symm h) _ ▸ {
        defLe :=
          fun _ dIn => isSat.backgroundInsHold (Or.inl ⟨dIn, h⟩)
        posLe :=
          fun _ isPos isOut =>
            isSat.backgroundOutHold (Or.inl ⟨isOut, h⟩) isPos
      }

def Cause.leastContextApxUpdateLeDefMem
  (cause: Cause D)
  (x: Nat)
  (d: D)
  (isSat: (cause.withBound x d).IsStronglySatisfiedBy b c)
  (xx: Nat)
:
  (cause.leastContextApx.update x d xx).defMem ⊆ (c xx).defMem
:=
fun _ inUpdatedLeast =>
  let inDefWith :=
    if h: xx = x then
      let dEq :=
        Valuation.update.inDef.eq (h ▸ inUpdatedLeast)
      Or.inr ⟨dEq, h⟩
    else
      Or.inl ⟨
        Valuation.update.inNeqElim.defMem
          inUpdatedLeast (Ne.symm h),
        h,
      ⟩
  isSat.contextInsHold inDefWith


def Cause.IsStronglySatisfiedBy.backgroundOnly
  {cause: Cause D}
  (isSat: cause.IsStronglySatisfiedBy b c)
  (cNew: Valuation D)
:
  cause.backgroundOnly.IsStronglySatisfiedBy b cNew
:= {
  contextInsHold := nofun
  backgroundInsHold := isSat.backgroundInsHold
  backgroundOutHold := isSat.backgroundOutHold
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

def IsStrongCause.elimVar
  (isCause: IsStrongCause salg cause d (Expr.var x))
  (isConsistent: cause.IsConsistent)
:
  ⟨d, x⟩ ∈ cause.contextIns
:=
  isCause isConsistent.leastValsApxAreSat

def IsStrongCause.notVar
  (isConsistent: cause.IsConsistent)
  (ninCins: ⟨d, x⟩ ∉ cause.contextIns)
:
  ¬ IsStrongCause salg cause d (Expr.var x)
:=
  fun isCause => ninCins (isCause.elimVar isConsistent)

def IsStrongCause.Not.elimVar
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.var x))
:
  ⟨d, x⟩ ∉ cause.contextIns
:=
  fun isIns => isNotCause (IsStrongCause.var isIns)


def IsStrongCause.op
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
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

def IsStrongCause.elimOp
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (isCause: IsStrongCause salg cause d (Expr.op opr argExprs))
  (isConsistent: cause.IsConsistent)
:
  ∃ (argVals: sig.Args opr salg.D),
    d ∈ salg.I opr argVals ∧
    ∀ param (dArg: argVals param),
      IsStrongCause salg cause dArg (argExprs param)
:= ⟨
  fun param =>
    Set3.defMem
      ((argExprs param).interpretation
        salg
        isConsistent.leastBackgroundApx
        cause.leastContextApx),
  isCause isConsistent.leastValsApxAreSat,
  fun param ⟨_, dArgInArgs⟩ b _ isSat =>
    let bLe := isConsistent.leastIsLeApx _ (isSat.backgroundOnly b)
    let cLe := fun _ _ => isSat.contextInsHold
    Expr.interpretation.isMonotonic.apxDefMem
      salg (argExprs param) bLe cLe dArgInArgs,
⟩

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
    
    isNotCause (op argVals argsCauseD allHaveCause)

def IsStrongCause.notOp
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (isConsistent: cause.IsConsistent)
  (allCausesNot:
    ∀ argVals: sig.Args opr salg.D,
      d ∈ salg.I opr argVals →
    ∃ param, ∃ (dArg: argVals param),
      ¬ IsStrongCause salg cause dArg (argExprs param))
:
  ¬ IsStrongCause salg cause d (Expr.op opr argExprs)
:=
  fun isCause =>
    let ⟨argVals, dIn, argsStrong⟩ := isCause.elimOp isConsistent
    let ⟨param, dArg, notStrong⟩ := allCausesNot argVals dIn
    notStrong (argsStrong param dArg)

def IsStrongCause.elimZeroExpr
  (isCause: IsStrongCause pairSalgebra cause d PairExpr.zeroExpr)
  (isConsistent: cause.IsConsistent)
:
  d = Pair.zero
:=
  let ⟨_, dEq, _⟩ := isCause.elimOp isConsistent
  dEq

def IsStrongCause.elimPairExpr
  (isCause:
    IsStrongCause pairSalgebra cause d (PairExpr.pairExpr left rite))
  (isConsistent: cause.IsConsistent)
:
  ∃ (dLeft dRite: Pair),
    d = Pair.pair dLeft dRite ∧
    IsStrongCause pairSalgebra cause dLeft left ∧
    IsStrongCause pairSalgebra cause dRite rite
:=
  let ⟨_, ⟨dLeft, dRite, eq⟩, areStrong⟩ :=
    isCause.elimOp isConsistent
  open ArityTwo in
  ⟨dLeft, dRite, eq, areStrong zth _, areStrong fst _⟩


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

def IsStrongCause.elimUn
  (isCause: IsStrongCause salg cause d (Expr.un left rite))
:
  Or
    (IsStrongCause salg cause d left)
    (IsStrongCause salg cause d rite)
:=
  if h: cause.IsConsistent then
    (isCause h.leastValsApxAreSat).elim
      (fun isDefLeft =>
        Or.inl
          fun isSat =>
            let bLe := h.leastIsLeApx _ (isSat.backgroundOnly _)
            let cLe := fun _ _ => isSat.contextInsHold
            Expr.interpretation.isMonotonic.apxDefMem
              salg left bLe cLe isDefLeft)
      (fun isDefRite =>
        Or.inr
          fun isSat =>
            let bLe := h.leastIsLeApx _ (isSat.backgroundOnly _)
            let cLe := fun _ _ => isSat.contextInsHold
            Expr.interpretation.isMonotonic.apxDefMem
              salg rite bLe cLe isDefRite)
  else
    Or.inl (Cause.IsConsistent.Not.isStrong h d left)

def IsStrongCause.notUn
  (notCauseLeft: ¬ IsStrongCause salg cause d left)
  (notCauseRite: ¬ IsStrongCause salg cause d rite)
:
  ¬ IsStrongCause salg cause d (Expr.un left rite)
:=
  elimUn.contra (Or.elim · notCauseLeft notCauseRite)

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


def IsStrongCause.ir
  (isCauseLeft: IsStrongCause salg cause d left)
  (isCauseRite: IsStrongCause salg cause d rite)
:
  IsStrongCause salg cause d (Expr.ir left rite)
:=
  fun isSat =>
    And.intro (isCauseLeft isSat) (isCauseRite isSat)

def IsStrongCause.elimIr
  (isCause: IsStrongCause salg cause d (Expr.ir left rite))
:
  And
    (IsStrongCause salg cause d left)
    (IsStrongCause salg cause d rite)
:=
  if h: cause.IsConsistent then
    let ⟨isDefLeft, isDefRite⟩ := isCause h.leastValsApxAreSat
    And.intro
      (fun isSat =>
        let bLe := h.leastIsLeApx _ (isSat.backgroundOnly _)
        let cLe := fun _ _ => isSat.contextInsHold
        Expr.interpretation.isMonotonic.apxDefMem
          salg left bLe cLe isDefLeft)
      (fun isSat =>
        let bLe := h.leastIsLeApx _ (isSat.backgroundOnly _)
        let cLe := fun _ _ => isSat.contextInsHold
        Expr.interpretation.isMonotonic.apxDefMem
          salg rite bLe cLe isDefRite)
  else
    And.intro
      (Cause.IsConsistent.Not.isStrong h d left)
      (Cause.IsConsistent.Not.isStrong h d rite)

def IsStrongCause.notIrLeft
  (notCauseLeft: ¬ IsStrongCause salg cause d left)
:
  ¬ IsStrongCause salg cause d (Expr.ir left rite)
:=
  elimIr.contra (fun ⟨left, _⟩ => notCauseLeft left)

def IsStrongCause.notIrRite
  (notCauseRite: ¬ IsStrongCause salg cause d rite)
:
  ¬ IsStrongCause salg cause d (Expr.ir left rite)
:=
  elimIr.contra (fun ⟨_, rite⟩ => notCauseRite rite)

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
  fun isSat => isCauseOut (isSat.backgroundOnly _)

def IsStrongCause.elimNot
  {salg: Salgebra sig}
  {cause: Cause salg.D}
  {d: salg.D}
  
  (isCauseCpl: IsStrongCause salg cause d (Expr.cpl expr))
  (dl: DefList sig)
  (isSat: cause.IsStronglySatisfiedBy
    (dl.wellFoundedModel salg)
    (dl.wellFoundedModel salg))
  (isCauseExpr: IsWeakCause salg cause d expr)
:
  IsCauseInapplicable
    salg
    dl
    (dl.wellFoundedModel salg).nonmembers
    cause
:=
  let insCpl := isCauseCpl isSat
  let notSat isSat := insCpl (isCauseExpr isSat)
  let isInapp := Cause.IsWeaklySatisfiedBy.toIsInapplicable notSat
  isInapp.toIsCauseInapplicable

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
  let b := isConsistent.leastBackgroundApx
  
  cause.backgroundOnly.IsStronglySatisfiedBy b b ∧
  (expr.interpretation salg b b).posMem d
:=
  let isConsistent := IsStrongCause.Not.isConsistent isNotCause
  let ⟨b, isSat, isPos⟩ := IsStrongCause.Not.elimNotEx isNotCause
  let isLeB := isConsistent.leastIsLeApx b isSat
  
  let isLeExpr :=
    Expr.interpretation.isMonotonic.approximation
      salg expr isLeB isLeB
  
  And.intro
    (isConsistent.leastBackgroundApxIsSat _)
    (isLeExpr.posLe isPos)


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

def IsStrongCause.elimIfThen
  {cond}
  (isCause: IsStrongCause salg cause d (Expr.ifThen cond body))
:
  And
    (∃ dC, IsStrongCause salg cause dC cond)
    (IsStrongCause salg cause d body)
:=
  if h: cause.IsConsistent then
    let ⟨⟨dC, isDefCond⟩, isDefBody⟩ := isCause h.leastValsApxAreSat
    And.intro
      ⟨
        dC,
        fun isSat =>
          let bLe := h.leastIsLeApx _ (isSat.backgroundOnly _)
          let cLe := fun _ _ => isSat.contextInsHold
          Expr.interpretation.isMonotonic.apxDefMem
            salg cond bLe cLe isDefCond
      ⟩
      (fun isSat =>
        let bLe := h.leastIsLeApx _ (isSat.backgroundOnly _)
        let cLe := fun _ _ => isSat.contextInsHold
        Expr.interpretation.isMonotonic.apxDefMem
          salg body bLe cLe isDefBody)
  else
    And.intro
      ⟨d, Cause.IsConsistent.Not.isStrong h d cond⟩
      (Cause.IsConsistent.Not.isStrong h d body)

def IsStrongCause.notIfThenCond
  {cond}
  (notCauseCond: ∀ dC, ¬ IsStrongCause salg cause dC cond)
  (d: salg.D)
  (body: Expr _)
:
  ¬ IsStrongCause salg cause d (Expr.ifThen cond body)
:=
  fun isCause =>
    notCauseCond _ isCause.elimIfThen.left.unwrap.property

def IsStrongCause.notIfThenBody
  (notCauseBody: ¬ IsStrongCause salg cause d body)
  (cond: Expr _)
:
  ¬ IsStrongCause salg cause d (Expr.ifThen cond body)
:=
  fun isCause =>
    notCauseBody isCause.elimIfThen.right

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

def IsStrongCause.elimArbUn
  (isCause: IsStrongCause salg cause d (Expr.Un x body))
  (isConsistent: cause.IsConsistent)
:
  ∃ dX, IsStrongCause salg (cause.withBound x dX) d body
:=
  let ⟨dX, isDef⟩ := isCause isConsistent.leastValsApxAreSat
  ⟨
    dX,
    fun isSat =>
      let bLe := isConsistent.leastBackgroundApxUpdateLe x dX isSat
      let cLe := cause.leastContextApxUpdateLeDefMem x dX isSat
      Expr.interpretation.isMonotonic.apxDefMem
        salg body bLe cLe isDef
  ⟩

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
    notCause _ (isCause.elimArbUn isConsistent).unwrap.property

def IsStrongCause.Not.elimArbUn
  (isNotCause: ¬ IsStrongCause salg cause d (Expr.Un x body))
  (dX: salg.D)
:
  ¬ IsStrongCause salg (cause.withBound x dX) d body
:=
  fun isCause => isNotCause isCause.arbUn


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

def IsStrongCause.elimArbIr
  (isCause: IsStrongCause salg cause d (Expr.Ir x body))
  (isConsistent: cause.IsConsistent)
:
  ∀ dX, IsStrongCause salg (cause.withBound x dX) d body
:=
  fun dX {_ _} isSat =>
    let isDef := isCause isConsistent.leastValsApxAreSat dX
    let bLe := isConsistent.leastBackgroundApxUpdateLe x dX isSat
    let cLe := cause.leastContextApxUpdateLeDefMem x dX isSat
    Expr.interpretation.isMonotonic.apxDefMem
      salg body bLe cLe isDef

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
    notCause (isCause.elimArbIr isConsistent dX)

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
