/-
  In this chapter, we define a proof system for the well-founded
  collections, that we prove sound and complete.
  
  The important definitions of this file are `Ins`, `Out`, and
  those contained within them. The rest is used for proving the
  soundness and completeness properties -- if a definition does
  not have a comment, it may be safely considered boilerplate
  and skipped.
-/

import WFC.Ch5_PairSalgebra
import WFC.Appx0_ExprRulesOfInference

-- Some "_" vars are being reported as unused :/
set_option linter.unusedVariables false

/-
  `ValVar` encodes some (usage-specific) relation between a variable
  and an element. For example, it may be used to represent the
  assertion that a certain variable contains a certain element in
  some valuation.
  
  That the variable `x` contains the element `d` may be denoted
  as `d ∈ x`.
-/
structure ValVar (D: Type*) where
  d: D
  x: Nat

def ValVar.eq: d0 = d1 → x0 = x1 → ValVar.mk d0 x0 = ⟨d1, x1⟩
| rfl, rfl => rfl

def ValVar.eqX: @Eq (ValVar D) ⟨d0, x0⟩ ⟨d1, x1⟩ → x0 = x1
| rfl => rfl


/-
  If expressions `a` and `c` contain an element `d`, then the
  expression `a ∩ (b ∪ c)` also contains that element. For this
  reason, we may call `d ∈ a ∧ d ∈ c` a cause of `d ∈ a ∪ (b ∪ c)`.
  
  We encode the causes as sets of `ValVar` instances. A cause
  consists of three such sets:
  - those that need to be present in the context,
  - those that need to be present in the background, and
  - those that need to be *absent* from the background.
-/
structure Cause (D: Type*) where
  contextIns: Set (ValVar D)
  backgroundIns: Set (ValVar D)
  backgroundOut: Set (ValVar D)

def Cause.union (c1 c2: Cause D): Cause D := {
  contextIns := c1.contextIns ∪ c2.contextIns,
  backgroundIns := c1.backgroundIns ∪ c2.backgroundIns,
  backgroundOut := c1.backgroundOut ∪ c2.backgroundOut,
}

def Cause.arbUnion (f: I → Cause D): Cause D := {
  contextIns := ⋃ i, (f i).contextIns,
  backgroundIns := ⋃ i, (f i).backgroundIns,
  backgroundOut := ⋃ i, (f i).backgroundOut,
}

def Cause.except
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

instance (D: Type*): Union (Cause D) := ⟨Cause.union⟩


-- Defines when a cause is satisfied by a pair of valuations.
structure Cause.IsSatisfiedBy
  (cause: Cause D)
  (b c: Valuation D)
:
  Prop
where
  contextInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → (c x).defMem d
  backgroundInsHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → (b x).defMem d
  backgroundOutHold:
    ∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → ¬(b x).posMem d

/-
  `IsCause salg cause d expr` means that for every pair of valuations
  `(b, c)` that satisfies `cause`, `d ∈ expr` holds (with `b` and
  `c` serving as background and context valuations, respectively).
-/
def IsCause
  (salg: Salgebra sig)
  (cause: Cause salg.D)
  (d: salg.D)
  (expr: Expr sig)
:
  Prop
:=
  {b c: Valuation salg.D} →
  cause.IsSatisfiedBy b c →
  (expr.interpretation salg b c).defMem d

def IsCause.ir
  (isCauseLeft: IsCause salg causeLeft d left)
  (isCauseRite: IsCause salg causeRite d rite)
:
  IsCause
    salg (causeLeft ∪ causeRite) d (Expr.ir left rite)
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

def IsCause.arbUn
  (isCauseBody:
    IsCause
      salg
      cause
      d
      body)
  (cinsSat:
    ∀ {dC: salg.D}, cause.contextIns ⟨dC, x⟩ → dC = dX)
  (binsSat:
    ∀ {dC: salg.D}, cause.backgroundIns ⟨dC, x⟩ → dC = dX)
  (boutSat:
    ∀ {dC: salg.D}, cause.backgroundOut ⟨dC, x⟩ → dC ≠ dX)
:
  IsCause salg (cause.except x dX) d (Expr.Un x body)
:=
  fun isSat =>
    ⟨
      dX,
      isCauseBody
        {
          contextInsHold :=
            fun {dd xx} inCins =>
              if h: x = xx then
                Valuation.update.eqBoundOfEq _ h _ ▸
                cinsSat (h.symm ▸ inCins) ▸
                rfl
              else
                let nin eq := (h (ValVar.eqX eq.symm)).elim
                Valuation.update.eqOrig _ h dX ▸
                isSat.contextInsHold ⟨inCins, nin⟩
          backgroundInsHold :=
            fun {dd xx} inBins =>
              if h: x = xx then
                Valuation.update.eqBoundOfEq _ h _ ▸
                binsSat (h.symm ▸ inBins) ▸
                rfl
              else
                let nin eq := (h (ValVar.eqX eq.symm)).elim
                Valuation.update.eqOrig _ h dX ▸
                isSat.backgroundInsHold ⟨inBins, nin⟩
          backgroundOutHold :=
            fun {dd xx} inBout =>
              if h: x = xx then
                Valuation.update.eqBoundOfEq _ h _ ▸
                boutSat (h.symm ▸ inBout)
              else
                let nin := h ∘ Eq.symm ∘ And.right
                Valuation.update.eqOrig _ h dX ▸
                isSat.backgroundOutHold ⟨inBout, nin⟩
        }
    ⟩


structure Cause.RespectsBoundVar
  (cause: Cause D)
  (xBound: Nat)
  (dBound: D)
:
  Prop
where
  cins: ⟨d, xBound⟩ ∈ cause.contextIns → d = dBound
  bins: ⟨d, xBound⟩ ∈ cause.backgroundIns → d = dBound
  bout: ⟨d, xBound⟩ ∈ cause.backgroundOut → d ≠ dBound

inductive Cause.DefiesBoundVar
  (cause: Cause D)
  (xBound: Nat)
  (dBound: D)
:
  Prop

| cins
  (inCins: ⟨d, xBound⟩ ∈ cause.contextIns)
  (dNeq: d ≠ dBound)
| bins
  (inBins: ⟨d, xBound⟩ ∈ cause.backgroundIns)
  (dNeq: d ≠ dBound)
| bout
  (inBout: ⟨d, xBound⟩ ∈ cause.backgroundOut)
  (dEq: d = dBound)

def Cause.DefiesBoundVar.ofNotRespects
  (notRespects: ¬ Cause.RespectsBoundVar cause xBound dBound)
:
  Cause.DefiesBoundVar cause xBound dBound
:=
  if hCi: ∃ d, ⟨d, xBound⟩ ∈ cause.contextIns ∧ d ≠ dBound then
    let ⟨d, ⟨inCins, dNeq⟩⟩ := hCi
    Cause.DefiesBoundVar.cins inCins dNeq
  else if hBi: ∃ d, ⟨d, xBound⟩ ∈ cause.backgroundIns ∧ d ≠ dBound then
    let ⟨d, ⟨inBins, dNeq⟩⟩ := hBi
    Cause.DefiesBoundVar.bins inBins dNeq
  else if hBo: ∃ d, ⟨d, xBound⟩ ∈ cause.backgroundOut ∧ d = dBound then
    let ⟨d, ⟨inBout, dEq⟩⟩ := hBo
    Cause.DefiesBoundVar.bout inBout dEq
  else
    False.elim
      (notRespects {
        cins := fun inCins =>
          byContradiction fun neq => hCi ⟨_, inCins, neq⟩
        bins := fun inBins =>
          byContradiction fun neq => hBi ⟨_, inBins, neq⟩
        bout := fun inBout eq => hBo ⟨_, inBout, eq⟩
      })


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
  {d x} -- For some reason, Lean reverses their order
        -- unless they are explicitly declared.
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

def Cause.IsInapplicable.union
  {causeLeft causeRite: Cause D}
  (isAppLeft: ¬ causeLeft.IsInapplicable outSet b)
  (isAppRite: ¬ causeRite.IsInapplicable outSet b)
:
  ¬ Cause.IsInapplicable (causeLeft ∪ causeRite) outSet b
:=
  open Cause.IsInapplicable in
  fun isInapplicable =>
    isInapplicable.rec
      (fun inCins => inCins.elim
        (fun inCinsL inOutSet =>
          isAppLeft (blockedContextIns inCinsL inOutSet))
        (fun inCinsR inOutSet =>
          isAppRite (blockedContextIns inCinsR inOutSet)))
      (fun inBins => inBins.elim
        (fun inBinsL notPos =>
          isAppLeft (blockedBackgroundIns inBinsL notPos))
        (fun inBinsR notPos =>
          isAppRite (blockedBackgroundIns inBinsR notPos)))
      (fun inBout => inBout.elim
        (fun inBoutL isDef =>
          isAppLeft (blockedBackgroundOut inBoutL isDef))
        (fun inBoutR isDef =>
          isAppRite (blockedBackgroundOut inBoutR isDef)))


def everyCauseInapplicableImpliesDefinitiveNonmember
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (d: salg.D)
  (expr: Expr sig)
  (outSet: Set (ValVar salg.D))
  (isEveryCauseInapplicable:
    {cause: Cause salg.D} →
    IsCause salg cause d expr →
    cause.IsInapplicable outSet b)
  (outSetIsEmpty:
    ∀ {d x}, ⟨d, x⟩ ∈ outSet → ¬ (c x).posMem d)
:
  ¬(expr.interpretation salg b c).posMem d
:=
  match expr with
  | Expr.var x =>
    let cause: Cause salg.D := {
      contextIns := fun ⟨dd, xx⟩ => dd = d ∧ xx = x,
      backgroundIns := Set.empty,
      backgroundOut := Set.empty,
    }
    
    let isCause: IsCause salg cause d (Expr.var x) :=
      fun isSat => isSat.contextInsHold (And.intro rfl rfl)
    
    (isEveryCauseInapplicable isCause).rec
      (fun ⟨eqD, eqX⟩ inOutSet =>
        outSetIsEmpty (eqD ▸ eqX ▸ inOutSet))
      False.elim
      False.elim
  | Expr.op op args =>
    let posMem param :=
      ((args param).interpretation salg b c).posMem
    
    let exApplicables:
      ∀ (param: sig.Params op) (d: posMem param),
      ∃ cause,
        IsCause salg cause d (args param) ∧
        ¬ cause.IsInapplicable outSet b
    :=
      byContradiction fun nall =>
        let ⟨param, ⟨d, dInArg⟩, allCausesInapp⟩ :=
          nall.toEx
            fun _ p =>
              p.toEx fun _ p => p.toAll fun _ => Not.toImplDne
        everyCauseInapplicableImpliesDefinitiveNonmember
          salg b c
          d
          (args param)
          outSet
          (allCausesInapp _)
          outSetIsEmpty
          dInArg
    
    let causes (i: Σ param, posMem param):
      let ⟨param, dInArg⟩ := i
      { cause //
        IsCause salg cause (dInArg) (args param) ∧
        ¬ cause.IsInapplicable outSet b
      }
    :=
      let ⟨param, dInArg⟩ := i
      (exApplicables param dInArg).unwrap
      
    fun isPos =>
      let exApplicable:
        ∃ cause,
          IsCause salg cause d (Expr.op op args) ∧
          ¬ cause.IsInapplicable outSet b
      := ⟨
        Cause.arbUnion (fun i => causes i),
        And.intro
          (fun isSat =>
            let posIsDef param (dPos: posMem param) :=
              let cause := causes ⟨param, dPos⟩
              let isCause := cause.property.left
              isCause {
                contextInsHold :=
                  fun inCins =>
                    isSat.contextInsHold ⟨
                      cause.val.contextIns,
                      And.intro ⟨⟨param, dPos⟩, rfl⟩ inCins,
                    ⟩
                backgroundInsHold :=
                  fun inBins =>
                    isSat.backgroundInsHold ⟨
                      cause.val.backgroundIns,
                      And.intro ⟨⟨param, dPos⟩, rfl⟩ inBins,
                    ⟩
                backgroundOutHold :=
                  fun inBout =>
                    isSat.backgroundOutHold ⟨
                      cause.val.backgroundOut,
                      And.intro ⟨⟨param, dPos⟩, rfl⟩ inBout,
                    ⟩
              }
            let defMem param :=
              ((args param).interpretation salg _ _).defMem        
            salg.isMonotonic op posMem defMem
              (fun param dVal dPos => posIsDef param ⟨dVal, dPos⟩)
              isPos)
          (fun isInapplicable =>
            open Cause.IsInapplicable in
            isInapplicable.rec
              (fun ⟨cins, ⟨⟨i, eq⟩, vvIn⟩⟩ inOutSet =>
                let eq: (causes i).val.contextIns = cins := eq
                (causes i).property.right
                  (blockedContextIns (eq ▸ vvIn) inOutSet))
              (fun ⟨bins, ⟨⟨i, eq⟩, vvIn⟩⟩ notPos =>
                let eq: (causes i).val.backgroundIns = bins := eq
                (causes i).property.right
                  (blockedBackgroundIns (eq ▸ vvIn) notPos))
              (fun ⟨bout, ⟨⟨i, eq⟩, vvIn⟩⟩ isDef =>
                let eq: (causes i).val.backgroundOut = bout := eq
                (causes i).property.right
                  (blockedBackgroundOut (eq ▸ vvIn) isDef)))
      ⟩
      
      let ⟨cause, ⟨isCause, notInapp⟩⟩ := exApplicable
      
      notInapp (isEveryCauseInapplicable isCause)
  | Expr.un left rite =>
    let ihLeft :=
      everyCauseInapplicableImpliesDefinitiveNonmember
        salg b c d left outSet
        (fun isCauseLeft =>
          isEveryCauseInapplicable (Or.inl ∘ isCauseLeft))
        outSetIsEmpty
    
    let ihRite :=
      everyCauseInapplicableImpliesDefinitiveNonmember
        salg b c d rite outSet
        (fun isCauseRite =>
          isEveryCauseInapplicable (Or.inr ∘ isCauseRite))
        outSetIsEmpty
    
    fun inPos => inPos.elim ihLeft ihRite
  | Expr.ir left rite =>
    fun ⟨isPosL, isPosR⟩ =>
      let exApplicableLeft:
        ∃ cause,
          IsCause salg cause d left ∧
          ¬ cause.IsInapplicable outSet b
      :=
        byContradiction fun nex =>
          let allInapp := nex.toAll fun _ => Not.toImplDne
          everyCauseInapplicableImpliesDefinitiveNonmember
            salg b c d left outSet
            (allInapp _)
            outSetIsEmpty
            isPosL
      
      let exApplicableRite:
        ∃ cause,
          IsCause salg cause d rite ∧
          ¬ cause.IsInapplicable outSet b
      :=
        byContradiction fun nex =>
          let allInapp := nex.toAll fun _ => Not.toImplDne
          everyCauseInapplicableImpliesDefinitiveNonmember
            salg b c d rite outSet
            (allInapp _)
            outSetIsEmpty
            isPosR
      
      let exApplicable:
        ∃ cause,
          IsCause salg cause d (Expr.ir left rite) ∧
          ¬ cause.IsInapplicable outSet b
      :=
        let ⟨causeL, ⟨isCauseL, notInappL⟩⟩ := exApplicableLeft
        let ⟨causeR, ⟨isCauseR, notInappR⟩⟩ := exApplicableRite
        
        ⟨
          causeL ∪ causeR,
          And.intro
            (IsCause.ir isCauseL isCauseR)
            (Cause.IsInapplicable.union notInappL notInappR)
        ⟩
      
      let ⟨cause, ⟨isCause, notInapp⟩⟩ := exApplicable
      
      notInapp (isEveryCauseInapplicable isCause)
  | Expr.cpl expr =>
    let exprCauses: Set (Cause salg.D) :=
      fun cause => IsCause salg cause d expr
    
    let cplCauses: Set (Cause salg.D) :=
      fun cause =>
        (∀ ec ∈ exprCauses,
          (∃ vv ∈ ec.contextIns, vv ∈ cause.backgroundOut) ∨
          (∃ vv ∈ ec.backgroundOut, vv ∈ cause.backgroundIns) ∨
          (∃ vv ∈ ec.backgroundIns, vv ∈ cause.backgroundOut))
    
    let areCausesCpl:
      ∀ cause ∈ cplCauses, IsCause salg cause d (expr.cpl)
    :=
      fun cause isCplCause =>
        fun {b c} isSat =>
          let bOutSet: Set (ValVar salg.D) :=
            fun ⟨d, x⟩ => ¬ (b x).posMem d
          
          let isEveryInapp
            {ec: Cause salg.D}
            (isCause: IsCause salg ec d expr)
          :
            ec.IsInapplicable bOutSet b
          :=
            open Cause.IsInapplicable in
            (isCplCause ec isCause).elim
              (fun ⟨vv, ⟨vvCins, vvBout⟩⟩ =>
                let notPos := isSat.backgroundOutHold vvBout
                blockedContextIns vvCins notPos)
              (fun or =>
                or.elim
                  (fun ⟨vv, ⟨vvBout, vvBins⟩⟩ =>
                    let isDef := isSat.backgroundInsHold vvBins
                    blockedBackgroundOut vvBout isDef)
                  (fun ⟨vv, ⟨vvBins, vvBout⟩⟩ =>
                    let notPos := isSat.backgroundOutHold vvBout
                    blockedBackgroundIns vvBins notPos))
          
          everyCauseInapplicableImpliesDefinitiveNonmember
            salg b b d expr bOutSet isEveryInapp id
    
    let areInapplicable:
      ∀ cause ∈ cplCauses, cause.IsInapplicable outSet b
    :=
      fun cause isCplCause =>
        isEveryCauseInapplicable (areCausesCpl cause isCplCause)
    
    let pseudoCplCause: Cause salg.D := {
      contextIns := Set.empty
      backgroundIns :=
        fun ⟨d, x⟩ =>
          ∃ ec ∈ exprCauses,
            ⟨d, x⟩ ∈ ec.backgroundOut ∧ (b x).posMem d
      backgroundOut :=
        fun ⟨d, x⟩ =>
          ∃ ec ∈ exprCauses,
            (⟨d, x⟩ ∈ ec.backgroundIns ∪ ec.contextIns) ∧
            ¬ (b x).defMem d
    }
    
    let notCplCause: pseudoCplCause ∉ cplCauses :=
      fun isCplCause =>
        (areInapplicable pseudoCplCause isCplCause).rec
          False.elim
          (fun inBins notPos =>
            -- This causes a Lean bug:
            -- let ⟨ec, _, _, isPos⟩ := inBins
            let ⟨ec, wtf⟩ := inBins
            False.elim (notPos wtf.right.right))
          (fun inBout isDef =>
            let ⟨ec, wtf⟩ := inBout
            False.elim (wtf.right.right isDef))
    
    let exSatExprCause:
      ∃ cause ∈ exprCauses, cause.IsSatisfiedBy b b
    :=
      notCplCause.toEx
        fun cause nAll =>
          let ⟨isExpr, isSat⟩ :=
            nAll.toEx
              fun isExpr nor =>
                let ⟨notExA, notExB, notExC⟩ := Not.toAnd3 nor
                
                let allCinsDef :=
                  notExA.toAll
                    fun vv nand cins =>
                      ((nand.toImpl cins).toAll
                        fun x nand (isExpr: x ∈ exprCauses) inBout =>
                          ((nand.toImpl isExpr).toImpl inBout).dne)
                        _ isExpr
                
                let allBoutNpos :=
                  notExB.toAll
                    fun vv nand bout =>
                      ((nand.toImpl bout).toAll
                        fun x nand (isExpr: x ∈ exprCauses) =>
                          (nand.toImpl isExpr).toImpl)
                        _ isExpr bout
                
                let allBinsDef :=
                  notExC.toAll
                    fun vv nand bins =>
                      ((nand.toImpl bins).toAll
                        fun x nand (isExpr: x ∈ exprCauses) inBins =>
                          ((nand.toImpl isExpr).toImpl inBins).dne)
                        _ isExpr
                
                {
                  contextInsHold :=
                    fun inCins => allCinsDef _ inCins (Or.inr inCins)
                  backgroundInsHold :=
                    fun inBins => allBinsDef _ inBins (Or.inl inBins)
                  backgroundOutHold := allBoutNpos _
                }
          ⟨isExpr, isSat⟩
    
    let ⟨cause, ⟨isExprCause, isSat⟩⟩ := exSatExprCause.unwrap
    
    Expr.ninwCpl (isExprCause isSat)
  | Expr.ifThen cond body =>
    fun ⟨⟨dC, isPosCond⟩, isPosBody⟩ =>
      let exApplicableCond:
        ∃ cause,
          IsCause salg cause dC cond ∧
          ¬ cause.IsInapplicable outSet b
      :=
        byContradiction fun nex =>
          let allInapp := nex.toAll fun _ => Not.toImplDne
          everyCauseInapplicableImpliesDefinitiveNonmember
            salg b c dC cond outSet
            (allInapp _) outSetIsEmpty isPosCond
      
      let exApplicableBody:
        ∃ cause,
          IsCause salg cause d body ∧
          ¬ cause.IsInapplicable outSet b
      :=
        byContradiction fun nex =>
          let allInapp := nex.toAll fun _ => Not.toImplDne
          everyCauseInapplicableImpliesDefinitiveNonmember
            salg b c d body outSet
            (allInapp _) outSetIsEmpty isPosBody
      
      let exApplicable:
        ∃ cause,
          IsCause salg cause d (Expr.ifThen cond body) ∧
          ¬ cause.IsInapplicable outSet b
      :=
        let ⟨causeCond, ⟨isCauseCond, notInappCond⟩⟩ := exApplicableCond
        let ⟨causeBody, ⟨isCauseBody, notInappBody⟩⟩ := exApplicableBody
        
        ⟨
          causeCond ∪ causeBody,
          And.intro
            (fun isSat =>
              let condIn := isCauseCond {
                contextInsHold := isSat.contextInsHold ∘ Or.inl
                backgroundInsHold := isSat.backgroundInsHold ∘ Or.inl
                backgroundOutHold := isSat.backgroundOutHold ∘ Or.inl
              }
              let bodyIn := isCauseBody {
                contextInsHold := isSat.contextInsHold ∘ Or.inr
                backgroundInsHold := isSat.backgroundInsHold ∘ Or.inr
                backgroundOutHold := isSat.backgroundOutHold ∘ Or.inr
              }
              And.intro ⟨dC, condIn⟩ bodyIn)
            (Cause.IsInapplicable.union notInappCond notInappBody)
        ⟩
      
      let ⟨cause, ⟨isCause, notInapp⟩⟩ := exApplicable
      
      notInapp (isEveryCauseInapplicable isCause)
  | Expr.Un x body =>
    let ih dX :=
      everyCauseInapplicableImpliesDefinitiveNonmember
        salg
        (b.update x dX)
        (c.update x dX)
        d
        body
        (fun vv => (vv.x = x ∧ vv.d ≠ dX) ∨ (vv.x ≠ x ∧ outSet vv))
        (fun {cause} isCauseBody =>
          open Cause.IsInapplicable in
          if h: cause.RespectsBoundVar x dX then
            let isCause:
              IsCause salg (cause.except x dX) d (Expr.Un x body)
            :=
              IsCause.arbUn isCauseBody h.cins h.bins h.bout
            
            (isEveryCauseInapplicable isCause).rec
              (fun {dd xx} inCins inOutSet =>
                let xNeq: xx ≠ x :=
                  fun xEq =>
                    let dEq := h.cins (xEq ▸ inCins.left)
                    inCins.right (ValVar.eq dEq xEq)
                let inModifiedOutSet :=
                  Or.inr (And.intro xNeq inOutSet)
                blockedContextIns inCins.left inModifiedOutSet)
              
              (fun {dd xx} inBins notPos =>
                let xNeq: x ≠ xx :=
                  fun xEq =>
                    let dEq := h.bins (xEq ▸ inBins.left)
                    inBins.right (ValVar.eq dEq xEq.symm)
                let notPosUpdated :=
                  Valuation.update.eqOrig _ xNeq _ ▸ notPos
                blockedBackgroundIns inBins.left notPosUpdated)
              
              (fun {dd xx} inBout isDef =>
                let xNeq: x ≠ xx :=
                  fun xEq =>
                    let dNeq := h.bout (xEq ▸ inBout.left)
                    inBout.right (And.intro dNeq xEq.symm)
                let isDefUpdated :=
                  Valuation.update.eqOrig _ xNeq _ ▸ isDef
                blockedBackgroundOut inBout.left isDefUpdated)
            else
              let defies := Cause.DefiesBoundVar.ofNotRespects h
              
              match defies with
              | Cause.DefiesBoundVar.cins inCins dNeq =>
                blockedContextIns inCins (Or.inl ⟨rfl, dNeq⟩)
              | Cause.DefiesBoundVar.bins inBins dNeq =>
                let nPos :=
                  Valuation.update.eqBound _ x dX ▸ dNeq
                blockedBackgroundIns inBins nPos
              | Cause.DefiesBoundVar.bout inBout dEq =>
                let isDef :=
                  Valuation.update.eqBound _ x dX ▸ dEq
                blockedBackgroundOut inBout isDef)
            (fun inModifiedOutSet =>
          inModifiedOutSet.elim
            (fun ⟨xEq, dNeq⟩ =>
              Valuation.update.eqBoundOfEq c xEq.symm dX ▸
              dNeq)
            (fun ⟨xNeq, inOutSet⟩ =>
              Valuation.update.eqOrig c xNeq.symm dX ▸
              outSetIsEmpty inOutSet))
    
    fun ⟨dX, inPos⟩ => ih dX inPos
  | Expr.Ir x body => sorry


mutual
-- A workaround for this bug, can be deleted when fixed:
-- https://github.com/leanprover/lean4/issues/3242
variable {sig: Signature}

/-
  `Ins salg dl d x` means that `d` is a definitive member of `x`
  in the well-founded model of `dl`.
-/
inductive Ins
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  salg.D → Nat → Prop

| intro:
  (d: salg.D) →
  (x: Nat) →
  IsCause salg cause d (dl.getDef x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.contextIns → Ins salg dl d x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundIns → Ins salg dl d x) →
  (∀ {d x}, ⟨d, x⟩ ∈ cause.backgroundOut → Out salg dl d x) →
  Ins salg dl d x


/-
  A cause is *provably* inapplicable for a given set S of value–
  variable pairs if for some element (d, x) of S, either:
  
  0. (d, x) is in the contextIns of the cause,
  1. (d, x) is in backgroundIns, and provably `d ∉ x`, or
  2. (d, x) is in backgroundOut, and provably `d ∈ x`.
  
  A set of value–variable pairs is called an empty cycle if all
  its elements have only inapplicable causes. Empty cycles formalize
  cyclic definitions like
  
      let A = B
      let B = A
  
  that do not contain any elements in the well-founded model.
  
  This definition differs from `Cause.IsInapplicable` in that it
  is about provability, it is not a semantic notion.
-/
inductive IsCauseInapplicable
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  Set (ValVar salg.D) →
  Cause salg.D →
  Prop

| blockedContextIns
  (cause: Cause salg.D)
  {d x}
  (inContextIns: ⟨d, x⟩ ∈ cause.contextIns)
  (inCycle: ⟨d, x⟩ ∈ cycle)
:
  IsCauseInapplicable salg dl cycle cause

| blockedBackgroundIns
  (cause: Cause salg.D)
  {d x}
  (inBins: ⟨d, x⟩ ∈ cause.backgroundIns)
  (isOut: Out salg dl d x)
:
  IsCauseInapplicable salg dl cycle cause

| blockedBackgroundOut
  (cause: Cause salg.D)
  {d x}
  (inBout: ⟨d, x⟩ ∈ cause.backgroundOut)
  (isIns: Ins salg dl d x)
:
  IsCauseInapplicable salg dl cycle cause


/-
  `Out salg dl d x` means that `d` is a definitive non-member of
  `x` in the well-founded model of `dl`.
-/
inductive Out
  (salg: Salgebra sig)
  (dl: DefList sig)
:
  salg.D → Nat → Prop

| intro:
  (cycle: Set (ValVar salg.D)) →
  (isEmptyCycle:
    ∀ {d x cause},
    ⟨d, x⟩ ∈ cycle →
    IsCause salg cause d (dl.getDef x) →  
    IsCauseInapplicable salg dl cycle cause) →
  ⟨d, x⟩ ∈ cycle →
  Out salg dl d x
end


def emptyCycleIsOut
  (salg: Salgebra sig)
  (dl: DefList sig)
  (cycle: Set (ValVar salg.D))
  (isEmptyCycle:
    ∀ {d x cause},
    ⟨d, x⟩ ∈ cycle →
    IsCause salg cause d (dl.getDef x) →  
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
            (isEmptyCycle isInCycle)
            (ih ⟨n.pred, nPredLt⟩ _))
    ⟨d, x⟩
    inCycle


-- A proof of soundness for `Ins`.
def Ins.isSound
  (ins: Ins salg dl d x)
:
  (dl.wellFoundedModel salg x).defMem d
:=
  -- Cannot use structural recursion, most likely because of
  -- this issue:
  -- https://github.com/leanprover/lean4/issues/4751
  open Cause.IsInapplicable in
  ins.rec
    (motive_1 := fun d x _ => (dl.wellFoundedModel salg x).defMem d)
    (motive_2 := fun cycle cause _ => cause.IsInapplicable cycle (dl.wellFoundedModel salg))
    (motive_3 := fun d x _ => ¬(dl.wellFoundedModel salg x).posMem d)
    (fun _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wellFoundedModel.isModel salg dl ▸
      isCause ⟨ihCins, ihBins, ihBout⟩)
    (fun _ _ _ => Cause.IsInapplicable.blockedContextIns)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundIns ihBins ihBout)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundOut ihBins ihBout)
    (fun cycle _ inCycle ih => emptyCycleIsOut salg dl cycle ih inCycle)

-- A proof of soundness for `Out`.
def Out.isSound
  (out: Out salg dl d x)
:
  ¬(dl.wellFoundedModel salg x).posMem d
:=
  open Cause.IsInapplicable in
  out.rec
    (motive_1 := fun d x _ => (dl.wellFoundedModel salg x).defMem d)
    (motive_2 := fun cycle cause _ => Cause.IsInapplicable cause cycle (dl.wellFoundedModel salg))
    (motive_3 := fun d x _ => ¬(dl.wellFoundedModel salg x).posMem d)
    (fun _ _ isCause _ _ _ ihCins ihBins ihBout =>
      DefList.wellFoundedModel.isModel salg dl ▸
      isCause ⟨ihCins, ihBins, ihBout⟩)
    (fun _ _ _ => Cause.IsInapplicable.blockedContextIns)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundIns ihBins ihBout)
    (fun _ _ _ ihBins _ ihBout => blockedBackgroundOut ihBins ihBout)
    (fun cycle _ inCycle ih => emptyCycleIsOut salg dl cycle ih inCycle)


-- TODO: A proof of completeness for `Ins`.
def Ins.isComplete
  (salg: Salgebra sig)
  (dl: DefList sig)
  (d: salg.D)
  (x: Nat)
  (ins: (dl.wellFoundedModel salg x).defMem d)
:
  Ins salg dl d x
:=
  sorry

-- TODO: A proof of completeness for `Out`.
def Out.isComplete
  (salg: Salgebra sig)
  (dl: DefList sig)
  (d: salg.D)
  (x: Nat)
  (out: ¬(dl.wellFoundedModel salg x).posMem d)
:
  Out salg dl d x
:=
  sorry
