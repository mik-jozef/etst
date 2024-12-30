/-
  This chapter is divided into three sections. The zeroth section
  proves that in the approximation order, the internal definition
  list is less than or equal to its encoding in the external
  definition list, while the first section proves the reverse
  inequality.
  
  In other words, we prove:
  
  0. every member (or non-member) `d` of `x` in the internal
     definition list is also a member (or non-member) of `x` in
     the encoding (section 0),
  1. the same holds in the reverse direction (section 1).
  
  It follows, as shown in the short section 2, that the internal
  definition list is equal to its encoding in the external
  definition list.
  
  The proofs of the zeroth two sections are by structural recursion
  on the proofs of (non-)membership in the respective definition
  lists. (Recall we have a sound and complete proof system for
  WFC. For every `d ∈ x`, there is a "reason" (proof) that `d ∈ x`.
  Informally, the inductive argument shows that for every such
  reason, there is a corresponding reason that `d ∈ x` in the
  encoding, and vice versa.)
-/

import UniSet3.Ch8_S13_TheInternalDefList
import Utils.CauseSatisfiesBoundVars
import Utils.ElimExternal
import Utils.InsInterp
import Utils.IsStrongCause
import Utils.IsWeakCause
import Utils.NopeInterp
import Utils.OutIntro4


noncomputable def optOrdPo :=
  PartialOrder.optionTop Ordinal.instLinearOrder.toPartialOrder

noncomputable def optOrdPreOrd := optOrdPo.toPreorder


namespace Pair
  noncomputable def uniSet3 :=
    uniDefList.theExternalWfm uniDefList.theSet
  
  namespace uniSet3
    open Expr
    open PairExpr
    
    
    def extOfIntCause
      (internalCause: Cause Pair)
      (boundVars: List (ValVar Pair) := [])
    :
      Cause Pair
    := {
      contextIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.contextIns,
            d = (vvI.x, vvI.d) ∧
            IsVarFree boundVars vvI.x
      backgroundIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundIns,
            d = (vvI.x, vvI.d) ∧
            IsVarFree boundVars vvI.x
      backgroundOut :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundOut,
            d = (vvI.x, vvI.d) ∧
            IsVarFree boundVars vvI.x
    }
    
    def extOfIntCauseDistributesUnion
      (causeLeft causeRite: Cause Pair)
      (boundVars: List (ValVar Pair))
    :
      extOfIntCause (causeLeft.union causeRite) boundVars
        =
      Cause.union
        (extOfIntCause causeLeft boundVars)
        (extOfIntCause causeRite boundVars)
    :=
      Cause.eq
        (funext fun _ =>
          propext
            (Iff.intro
              (fun ⟨xEq, vvI, inCinsUnion, dEq⟩ =>
                inCinsUnion.elim
                  (fun inCinsLeft =>
                    Or.inl ⟨xEq, vvI, inCinsLeft, dEq⟩)
                  (fun inCinsRite =>
                    Or.inr ⟨xEq, vvI, inCinsRite, dEq⟩))
              (fun inCinsUnion =>
                inCinsUnion.elim
                  (fun ⟨xEq, vvI, inCinsLeft, dEq⟩ =>
                    ⟨xEq, vvI, Or.inl inCinsLeft, dEq⟩)
                  (fun ⟨xEq, vvI, inCinsRite, dEq⟩ =>
                    ⟨xEq, vvI, Or.inr inCinsRite, dEq⟩))))
        (funext fun _ =>
          propext
            (Iff.intro
              (fun ⟨xEq, vvI, inCinsUnion, dEq⟩ =>
                inCinsUnion.elim
                  (fun inCinsLeft =>
                    Or.inl ⟨xEq, vvI, inCinsLeft, dEq⟩)
                  (fun inCinsRite =>
                    Or.inr ⟨xEq, vvI, inCinsRite, dEq⟩))
              (fun inCinsUnion =>
                inCinsUnion.elim
                  (fun ⟨xEq, vvI, inCinsLeft, dEq⟩ =>
                    ⟨xEq, vvI, Or.inl inCinsLeft, dEq⟩)
                  (fun ⟨xEq, vvI, inCinsRite, dEq⟩ =>
                    ⟨xEq, vvI, Or.inr inCinsRite, dEq⟩))))
        (funext fun _ =>
          propext
            (Iff.intro
              (fun ⟨xEq, vvI, inBinsUnion, dEq⟩ =>
                inBinsUnion.elim
                  (fun inBinsLeft =>
                    Or.inl ⟨xEq, vvI, inBinsLeft, dEq⟩)
                  (fun inBinsRite =>
                    Or.inr ⟨xEq, vvI, inBinsRite, dEq⟩))
              (fun inBinsUnion =>
                inBinsUnion.elim
                  (fun ⟨xEq, vvI, inBinsLeft, dEq⟩ =>
                    ⟨xEq, vvI, Or.inl inBinsLeft, dEq⟩)
                  (fun ⟨xEq, vvI, inBinsRite, dEq⟩ =>
                    ⟨xEq, vvI, Or.inr inBinsRite, dEq⟩))))
    
    def extOfIntCauseArbUn
      (causes: Pair → Cause Pair)
      (boundVars: List (ValVar Pair))
      (x: Nat)
    :
      Cause.IsSubset
        (extOfIntCause
          (Cause.arbUn fun dX => (causes dX).exceptVar x)
          boundVars)
        (Cause.arbUn fun dX =>
          extOfIntCause
            (causes dX)
            ({ d := dX, x := x } :: boundVars))
    := {
      cinsLe :=
        fun _ ⟨xEq, vvI, ⟨dX, inCins⟩, dEq, isFreeTail⟩ =>
          let neq := Ne.symm inCins.right
          let isFree := IsVarFree.ofTail isFreeTail neq dX
          ⟨dX, xEq, vvI, inCins.left, dEq, isFree⟩
      binsLe :=
        fun _ ⟨xEq, vvI, ⟨dX, inBins⟩, dEq, isFreeTail⟩ =>
          let neq := Ne.symm inBins.right
          let isFree := IsVarFree.ofTail isFreeTail neq dX
          ⟨dX, xEq, vvI, inBins.left, dEq, isFree⟩
      boutLe :=
        fun _ ⟨xEq, vvI, ⟨dX, inBout⟩, dEq, isFreeTail⟩ =>
          let neq := Ne.symm inBout.right
          let isFree := IsVarFree.ofTail isFreeTail neq dX
          ⟨dX, xEq, vvI, inBout.left, dEq, isFree⟩
    }
    
    
    def extOfIntExceptLeBoundHead
      (cause: Cause Pair)
      (d: Pair)
      (x: Nat)
    :
      extOfIntCause (cause.exceptVar x) boundVars
        ⊆
      extOfIntCause cause (⟨d, x⟩ :: boundVars)
    := {
      cinsLe :=
        fun _ ⟨xEq, ⟨vv, ⟨inCins, dEq, isFree⟩⟩⟩ =>
          let neq := Ne.symm inCins.right
          ⟨xEq, vv, inCins.left, dEq, isFree.ofTail neq d⟩
      binsLe :=
        fun _ ⟨xEq, ⟨vv, ⟨inBins, dEq, isFree⟩⟩⟩ =>
          let neq := Ne.symm inBins.right
          ⟨xEq, vv, inBins.left, dEq, isFree.ofTail neq d⟩
      boutLe :=
        fun _ ⟨xEq, ⟨vv, ⟨inBout, dEq, isFree⟩⟩⟩ =>
          let neq := Ne.symm inBout.right
          ⟨xEq, vv, inBout.left, dEq, isFree.ofTail neq d⟩
    }
    
    
    inductive extOfIntCycleBare
      (internalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    |
      theSet
        (vvIntIn: vvInt ∈ internalCycle)
      :
        extOfIntCycleBare
          internalCycle
          ⟨(vvInt.x, vvInt.d), uniDefList.theSet⟩
    
    def AllCausesInapp
      (internalCycle: Set (ValVar Pair))
      (boundVars: List (ValVar Pair))
      (expr: Expr pairSignature)
      (d: Pair)
    :
      Prop
    :=
      (internalCause: Cause Pair) →
      internalCause.SatisfiesBoundVars boundVars →
      IsWeakCause pairSalgebra internalCause d expr →
      IsCauseInappExtended
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (extOfIntCycleBare internalCycle)
        (extOfIntCause internalCause boundVars)
    
    inductive extOfIntCycleFull
      (sizeBound: Option Ordinal)
      (internalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    |
      interp
        (boundVars: List (ValVar Pair))
        (expr: Expr)
        (exprSizeIsBound: optOrdPo.lt expr.sizeOf sizeBound)
        (d: Pair)
        (allInapp: AllCausesInapp internalCycle boundVars expr d)
      :
        extOfIntCycleFull sizeBound internalCycle ⟨
          pair
            (boundVarsEncoding boundVars)
            (pair
              (exprToEncoding expr)
              d),
          uniDefList.interpretation
        ⟩
    |
      theSet
        (vvIntIn: vvInt ∈ internalCycle)
      :
        extOfIntCycleFull
          sizeBound
          internalCycle
          ⟨(vvInt.x, vvInt.d), uniDefList.theSet⟩
    
    def extOfIntCycleFull.ofInEmpty
      (inCycle: extOfIntCycleFull sizeBound Set.empty ⟨dExt, xExt⟩)
    :
      And
        (∃ boundVars expr d,
          optOrdPo.lt expr.sizeOf sizeBound ∧
          AllCausesInapp Set.empty boundVars expr d ∧
          Eq
            dExt
            (pair
              (boundVarsEncoding boundVars)
              (pair (exprToEncoding expr) d)))
        (xExt = uniDefList.interpretation)
    :=
      match inCycle with
      | extOfIntCycleFull.interp _ _ sizeIsBound _ allInapp =>
        And.intro ⟨_, _, _, sizeIsBound, allInapp, rfl⟩ rfl
    
    def extOfIntCycleFull.toLargerBound
      (internalCycle: Set (ValVar Pair))
      (boundLe: optOrdPo.le b0 b1)
    :
      extOfIntCycleFull b0 internalCycle
        ⊆
      extOfIntCycleFull b1 internalCycle
    |
      _,
      extOfIntCycleFull.interp
        boundVars expr sizeIsBound d allInapp
    =>
      extOfIntCycleFull.interp
        boundVars
        expr
        (optOrdPo.lte_trans sizeIsBound boundLe)
        d
        allInapp
    |
      _,
      extOfIntCycleFull.theSet inIntCycle
    =>
      extOfIntCycleFull.theSet inIntCycle
    
    def bareLeFull
      (sizeBound: Ordinal)
      (internalCycle: Set (ValVar Pair))
    :
      extOfIntCycleBare internalCycle
        ⊆
      extOfIntCycleFull sizeBound internalCycle
    |
      _, extOfIntCycleBare.theSet inIntCycle =>
        extOfIntCycleFull.theSet inIntCycle
    
    
    def allInappOfIsCauseCpl
      (isInternalCause:
        IsStrongCause pairSalgebra internalCause d expr.cpl)
      (isConsistent: internalCause.IsConsistent)
      (boundVarsSat: internalCause.SatisfiesBoundVars boundVars)
      (binsIns: BinsInsExternal internalCause boundVars)
      (boutOut: BoutOutExternal internalCause boundVars)
    :
      AllCausesInapp Set.empty boundVars expr d
    :=
      fun _cause satBoundVars isCause =>
        let causeInapp :=
          isInternalCause.elimCpl isConsistent isCause
        
        open Cause.IsInapplicable in
        open IsCauseInappExtended in
        match causeInapp with
        | blockedContextIns inCins inBout =>
          let isFree :=
            byContradiction fun notFree =>
              let ⟨_, isBoundTo⟩ :=
                IsVarFree.Not.exBoundTo notFree
              let cinsSat := (satBoundVars isBoundTo).cinsSat
              let boutSat := (boundVarsSat isBoundTo).boutSat
              boutSat _ inBout.dne rfl (cinsSat _ inCins rfl)
          let notBound isBound :=
            isFree.nopeIsBoundTo isBound.unwrap.property
          cinsFailsOut
            ⟨rfl, _, inCins, rfl, isFree⟩
            (boutOut inBout.dne notBound)
        | blockedBackgroundIns inBins inBout =>
          let isFree :=
            byContradiction fun notFree =>
              let ⟨_, isBoundTo⟩ :=
                IsVarFree.Not.exBoundTo notFree
              let binsSat := (satBoundVars isBoundTo).binsSat
              let boutSat := (boundVarsSat isBoundTo).boutSat
              boutSat _ inBout.dne rfl (binsSat _ inBins rfl)
          let notBound isBound :=
            isFree.nopeIsBoundTo isBound.unwrap.property
          binsFails
            ⟨rfl, _, inBins, rfl, isFree⟩
            (boutOut inBout.dne notBound)
        | blockedBackgroundOut inBout inBins =>
          let isFree :=
            byContradiction fun notFree =>
              let ⟨_, isBoundTo⟩ :=
                IsVarFree.Not.exBoundTo notFree
              let binsSat := (boundVarsSat isBoundTo).binsSat
              let boutSat := (satBoundVars isBoundTo).boutSat
              boutSat _ inBout rfl (binsSat _ inBins rfl)
          let notBound isBound :=
            isFree.nopeIsBoundTo isBound.unwrap.property
          boutFails
            ⟨rfl, _, inBout, rfl, isFree⟩
            (binsIns inBins notBound)
    
    def isCauseOfAllInappCpl.cause
      (boundVars: List (ValVar Pair))
    :
      Cause Pair
    := {
      contextIns :=
        fun ⟨dd, xx⟩ =>
          Or
            (IsBoundTo boundVars xx dd)
            (¬ IsBound boundVars xx ∧
            _root_.Ins
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (pair xx dd)
              uniDefList.theSet)
      backgroundIns :=
        fun ⟨dd, xx⟩ =>
          Or
            (IsBoundTo boundVars xx dd)
            (¬ IsBound boundVars xx ∧
            _root_.Ins
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (pair xx dd)
              uniDefList.theSet)
      backgroundOut :=
        fun ⟨dd, xx⟩ =>
          Or
            (∃ dOther,
              dd ≠ dOther ∧
              IsBoundTo boundVars xx dOther)
            (¬ IsBound boundVars xx ∧
            _root_.Out
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (pair xx dd)
              uniDefList.theSet)
    }
    
    def isCauseOfAllInappCpl.causeIsConsistent
      (boundVars: List (ValVar Pair))
    :
      (cause boundVars).IsConsistent
    :=
      fun _ =>
        Or.inrEm fun inBinsDn inBout =>
          match inBout, inBinsDn.dne with
          | Or.inl ⟨_dOther, neq, isBoundOther⟩,
            Or.inl isBound
          =>
            neq (isBound.isUnique isBoundOther)
          |
            Or.inl ⟨dOther, _, isBoundOther⟩,
            Or.inr ⟨notBound, _⟩
          =>
            notBound ⟨dOther, isBoundOther⟩
          |
            Or.inr ⟨notBound, _⟩, Or.inl isBound =>
            notBound ⟨_, isBound⟩
          |
            Or.inr ⟨_, isOut⟩, Or.inr ⟨_, isIns⟩ =>
            isOut.nopeIns isIns
    
    def isCauseOfAllInappCpl.satBoundVars
      (boundVars: List (ValVar Pair))
    :
      (cause boundVars).SatisfiesBoundVars boundVars
    :=
      (fun isBoundTo => {
        cinsSat :=
          fun _ inCins xEq =>
            inCins.elim
              (fun isBound =>
                isBound.isUnique (xEq ▸ isBoundTo))
              (fun ⟨notBound, _⟩ =>
                absurd (xEq ▸ ⟨_, isBoundTo⟩) notBound)
        binsSat :=
          fun _ inBins xEq =>
            inBins.elim
              (fun isBound =>
                isBound.isUnique (xEq ▸ isBoundTo))
              (fun ⟨notBound, _⟩ =>
                absurd (xEq ▸ ⟨_, isBoundTo⟩) notBound)
        boutSat :=
          fun _ inBout xEq dEq =>
            inBout.elim
              (fun ⟨_, neq, isBoundOther⟩ =>
                neq
                  (dEq ▸
                  isBoundTo.isUnique (xEq ▸ isBoundOther)))
              (fun ⟨notBound, _⟩ =>
                notBound ⟨_, xEq ▸ isBoundTo⟩)
      })
    
    def isCauseOfAllInappCpl
      (allInapp:
        AllCausesInapp internalCycle boundVars (Expr.cpl expr) d)
    :
      IsStrongCause
        pairSalgebra
        (isCauseOfAllInappCpl.cause boundVars)
        d
        expr
    :=
      let isConsistent :=
        isCauseOfAllInappCpl.causeIsConsistent boundVars
      let b := isConsistent.leastBackgroundApx
      IsStrongCause.ofLeastBackground
        rfl
        isConsistent
        (byContradiction fun notDef =>
          let isPosCpl:
            Set3.posMem
              (expr.cpl.interpretation pairSalgebra b b)
              d
          :=
            notDef
          let isSatCpl :=
            Cause.IsWeaklySatisfiedBy.ofValPos b b
          let isInapp :=
            allInapp
              (Cause.ofValPos b b).background
              (fun isBoundTo => {
                cinsSat := fun _ nope _ => nope.elim
                binsSat :=
                  fun _ inBins xEq =>
                    let notBout := isSatCpl.backgroundInsHold inBins
                    let otherNotBound :=
                      notBout.toAnd.left.toAll fun _ nand =>
                        nand.toImpl
                    byContradiction fun neq =>
                      otherNotBound _ neq (xEq ▸ isBoundTo)
                boutSat :=
                  fun _ inBout xEq dEq =>
                    let notBins :=
                      isSatCpl.backgroundOutHold inBout
                    let ⟨notBound, _⟩ := notBins.toAnd
                    notBound (xEq ▸ dEq ▸ isBoundTo)
              })
              (IsWeakCause.toEmptyCinsCpl
                (IsWeakCause.ofValPos isPosCpl))
          open IsCauseInappExtended in
          match isInapp with
          | cinsFailsCycle ⟨_, ⟨_, nope, _, _⟩⟩ _ => nope
          | cinsFailsOut ⟨_, ⟨_, nope, _, _⟩⟩ _ => nope
          | binsFails ⟨xEq, ⟨vv, inBins, dEq, isFree⟩⟩ isOut =>
            let dEq: _ = pair vv.x vv.d := dEq
            isSatCpl.backgroundInsHold
              inBins
              (Or.inr ⟨isFree.nopeIsBound, xEq ▸ dEq ▸ isOut⟩)
          | boutFails ⟨xEq, ⟨vv, inBout, dEq, isFree⟩⟩ isIns =>
            let dEq: _ = pair vv.x vv.d := dEq
            isSatCpl.backgroundOutHold
              inBout
              (Or.inr ⟨isFree.nopeIsBound, xEq ▸ dEq ▸ isIns⟩))
    
    
    def inappExtBoundVar
      {sizeBound: Ordinal}
      (allInapp: AllCausesInapp internalCycle boundVars (var x) d)
      (inw:
        externalCause.contextIns ⟨
          pair
            (boundVarsEncoding boundVars)
            (pair (fromNat x) d),
          uniDefList.getBound,
        ⟩)
    :
      IsCauseInappExtended
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (extOfIntCycleFull sizeBound internalCycle)
        externalCause
    :=
      let out :=
        Out.isComplete _ _ fun inw =>
        let isBoundTo := Inw.toIsBoundTo inw
        let isInapp :=
          allInapp
            (Cause.var x d)
            (Cause.boundVarSat isBoundTo)
            (fun isSat => isSat.contextInsHold ⟨rfl, rfl⟩)
        open IsCauseInappExtended in
        match isInapp with
        | cinsFailsCycle inCins _ =>
          let ⟨_, ⟨_, ⟨dEq, xEq⟩, _, isFree⟩⟩ := inCins
          isFree.nopeIsBoundTo (dEq ▸ xEq ▸ isBoundTo)
        | cinsFailsOut inCins _ =>
          let ⟨_, ⟨_, ⟨dEq, xEq⟩, _, isFree⟩⟩ := inCins
          isFree.nopeIsBoundTo (dEq ▸ xEq ▸ isBoundTo)
        | binsFails inBins _ =>
          let ⟨_, ⟨_, nope, _, _⟩⟩ := inBins
          nope.elim
        | boutFails inBout _ =>
          let ⟨_, ⟨_, nope, _, _⟩⟩ := inBout
          nope.elim
    IsCauseInappExtended.cinsFailsOut inw out
    
    def inappExtFreeVar
      {sizeBound: Ordinal}
      (allInapp: AllCausesInapp internalCycle boundVars (var x) d)
      (inw:
        externalCause.contextIns ⟨
          (pair (fromNat x) d),
          uniDefList.theSet,
        ⟩)
      (notBound:
        ¬ ∃ d,
          ¬ externalCause.backgroundOut ⟨
            (pair
              (boundVarsEncoding boundVars)
              (pair (fromNat x) d)),
            uniDefList.getBound
          ⟩)
    :
      IsCauseInappExtended
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (extOfIntCycleFull sizeBound internalCycle)
        externalCause
    :=
      open IsCauseInappExtended in
      if h: IsBound boundVars x then
        let ⟨d, isBoundTo⟩ := h
        boutFails
          (notBound.toAll (fun _ => Not.dne) d)
          (Ins.isComplete _ _ (insGetBound isBoundTo))
      else
        let isInapp :=
          allInapp
            (Cause.var x d)
            (Cause.freeVarSat h)
            (fun isSat => isSat.contextInsHold ⟨rfl, rfl⟩)
        match isInapp with
        | cinsFailsCycle
          ⟨eqX, vv, ⟨eqVvD, eqVvX⟩, eq, _⟩ inCycle
        =>
          let eq: _ = (fromNat vv.x).pair vv.d := eq
          cinsFailsCycle
            inw
            (bareLeFull
              sizeBound
              internalCycle
              (eqX ▸ eqVvD ▸ eqVvX ▸ eq ▸ inCycle))
        | cinsFailsOut
          ⟨eqX, vv, ⟨eqVvD, eqVvX⟩, eq, _⟩ out
        =>
          let eq: _ = (fromNat vv.x).pair vv.d := eq
          cinsFailsOut inw (eqX ▸ eqVvD ▸ eqVvX ▸ eq ▸ out)
        | binsFails ⟨_, _, nope, _, _⟩ _ => nope.elim
        | boutFails ⟨_, _, nope, _, _⟩ _ => nope.elim
    
    
    mutual
    def isCauseToInsInterp
      (isInternalCause:
        IsStrongCause pairSalgebra internalCause d expr)
      (boundVars: List (ValVar Pair))
      (boundVarsSat: internalCause.SatisfiesBoundVars boundVars)
      (cinsIns: CinsInsExternal internalCause boundVars)
      (binsIns: BinsInsExternal internalCause boundVars)
      (boutOut: BoutOutExternal internalCause boundVars)
    :
      InsInterp boundVars d expr
    :=
      let isConsistent: internalCause.IsConsistent :=
        fun vv =>
          if hI:
            vv ∈ internalCause.backgroundIns ∧
            vv ∈ internalCause.backgroundOut
          then
            if hB: IsBound boundVars vv.x then
              let ⟨_d, isBoundTo⟩ := hB
              let boundVarSat := boundVarsSat isBoundTo
              boundVarSat.ninBinsBout vv.d
            else
              False.elim
                ((boutOut hI.right hB).isSound
                  (binsIns hI.left hB).isSound.toPos)
          else
            hI.toOr
      
      match expr with
      | var _ =>
        InsInterp.var
          isInternalCause
          isConsistent
          boundVars
          boundVarsSat
          cinsIns
      | op pairSignature.Op.zero _ =>
        InsInterp.exprZero isInternalCause isConsistent
      | op pairSignature.Op.pair args =>
        let ⟨_dLeft, _dRite, eq, isStrongLeft, isStrongRite⟩ :=
          isInternalCause.elimPairExpr isConsistent
      
        have:
          (args ArityTwo.zth).sizeOf
            <
          (@op pairSignature pairSignature.Op.pair args).sizeOf
        :=
          Order.lt_succ_of_le (Ordinal.le_iSup _ ArityTwo.zth)
        
        let ihL := isCauseToInsInterp
          isStrongLeft boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        have:
          (args ArityTwo.fst).sizeOf
            <
          (@op pairSignature pairSignature.Op.pair args).sizeOf
        :=
          Order.lt_succ_of_le (Ordinal.le_iSup _ ArityTwo.fst)
        
        let ihR := isCauseToInsInterp
          isStrongRite boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        eq ▸ InsInterp.exprPair ihL ihR
      | un left rite =>
        isInternalCause.elimUn.elim
          (fun isCauseLeft =>
            have: left.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
              Order.lt_succ_of_le (le_max_left _ _)
            
            let ih := isCauseToInsInterp
              isCauseLeft boundVars boundVarsSat
              cinsIns binsIns boutOut
            
            InsInterp.exprUnLeft ih)
          (fun isCauseRite =>
            have: rite.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
              Order.lt_succ_of_le (le_max_right _ _)
            
            let ih := isCauseToInsInterp
              isCauseRite boundVars boundVarsSat
              cinsIns binsIns boutOut
            
            InsInterp.exprUnRite ih)
      | ir left rite =>
        have: left.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_left _ _)
        have: rite.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_right _ _)
        
        let ⟨isCauseLeft, isCauseRite⟩ := isInternalCause.elimIr
        
        let ihL := isCauseToInsInterp
          isCauseLeft boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihR := isCauseToInsInterp
          isCauseRite boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        InsInterp.exprIr ihL ihR
      | cpl expr =>
        let allInapp :=
          allInappOfIsCauseCpl
            isInternalCause isConsistent boundVarsSat
            binsIns boutOut
        let out :=
          Out.intro4
            (extOfIntCycleFull expr.sizeOf.succ Set.empty)
            (fun inCycle cause isCause =>
              let ⟨
                ⟨bvC, eC, dC, sizeIsBound, allInapp, dEq⟩,
                xEq
              ⟩ :=
                inCycle.ofInEmpty
              let isInapp :=
                inappExtOfAllInappInt allInapp (xEq ▸ dEq ▸ isCause)
              isInapp.toSuperCycle
                (extOfIntCycleFull.toLargerBound
                  _ (@le_of_lt _ optOrdPreOrd _ _ sizeIsBound)))
            (extOfIntCycleFull.interp
              boundVars expr (Ordinal.lt_succ _) d allInapp)
        InsInterp.exprCpl (Out.isSound out)
      | ifThen cond body =>
        have: cond.sizeOf < max cond.sizeOf body.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_left _ _)
        have: body.sizeOf < max cond.sizeOf body.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_right _ _)
        
        let ⟨⟨_dC, isCauseCond⟩, isCauseBody⟩ :=
          isInternalCause.elimIfThen
        
        let ihCond := isCauseToInsInterp
          isCauseCond boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihBody := isCauseToInsInterp
          isCauseBody boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        InsInterp.exprIfThen ihCond ihBody
      | arbUn x body =>
        have: body.sizeOf < body.sizeOf + 1 :=
          Order.lt_succ_of_le (le_refl _)
        
        let ⟨dX, isCauseWith⟩ :=
          isInternalCause.elimArbUn isConsistent
        
        let ih :=
          isCauseToInsInterp
            isCauseWith
            (⟨dX, x⟩ :: boundVars)
            boundVarsSat.satWithBound
            (fun inCinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              cinsIns
                (Cause.inCinsOfInWithAndNotBound inCinsWith xNeq)
                (IsBound.Not.notBoundTail notBound))
            (fun inBinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              binsIns
                (Cause.inBinsOfInWithAndNotBound inBinsWith xNeq)
                (IsBound.Not.notBoundTail notBound))
            (fun inBoutWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              boutOut
                (Cause.inBoutOfInWithAndNotBound inBoutWith xNeq)
                (IsBound.Not.notBoundTail notBound))
        
        InsInterp.arbUn dX ih
      | arbIr x body =>
        have: body.sizeOf < body.sizeOf + 1 :=
          Order.lt_succ_of_le (le_refl _)
        
        let isCauseWith := isInternalCause.elimArbIr isConsistent
        
        InsInterp.arbIr fun dX =>
          isCauseToInsInterp
            (isCauseWith dX)
            (⟨dX, x⟩ :: boundVars)
            boundVarsSat.satWithBound
            (fun inCinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              cinsIns
                (Cause.inCinsOfInWithAndNotBound inCinsWith xNeq)
                (IsBound.Not.notBoundTail notBound))
            (fun inBinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              binsIns
                (Cause.inBinsOfInWithAndNotBound inBinsWith xNeq)
                (IsBound.Not.notBoundTail notBound))
            (fun inBoutWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              boutOut
                (Cause.inBoutOfInWithAndNotBound inBoutWith xNeq)
                (IsBound.Not.notBoundTail notBound))
    termination_by expr.sizeOf
    
    
    def inappExtOfAllInappInt
      (allInapp: AllCausesInapp internalCycle boundVars expr d)
      (isCause:
        IsWeakCause
          pairSalgebra
          externalCause
          (pair
            (boundVarsEncoding boundVars)
            (pair
              (exprToEncoding expr)
              d))
          (uniDefList.theExternalDefList.getDef
            uniDefList.interpretation))
    :
      IsCauseInappExtended
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (extOfIntCycleFull expr.sizeOf internalCycle)
        externalCause
    :=
      match expr with
      | var x =>
        let boundOrFree :=
          isCause.hurrDurrElimGreat elimPosExternalVar
        boundOrFree.elim
          (inappExtBoundVar allInapp)
          (fun ⟨inw, notBound⟩ =>
            inappExtFreeVar allInapp inw notBound)
      |
        op pairSignature.Op.zero _ =>
        let dEqZero := isCause.hurrDurrElim elimPosExternalZero
        let isInapp :=
          allInapp
            (Cause.empty)
            (Cause.emptySat boundVars)
            (dEqZero ▸ fun _ => rfl)
        isInapp.toSuper
          (bareLeFull _ internalCycle)
          {
            cinsLe := nofun
            binsLe := nofun
            boutLe := nofun
          }
      |
        op pairSignature.Op.pair args =>
        let ⟨dL, dR, dEq, inCinsLeft, inCinsRite⟩ :=
          isCause.hurrDurrElim elimPosExternalPair
        
        let left := args ArityTwo.zth
        let rite := args ArityTwo.fst
        
        let isLeL:
          left.sizeOf
            <
          iSup (fun param => (args param).sizeOf) + 1
        :=
          Order.lt_succ_of_le (Ordinal.le_iSup _ ArityTwo.zth)
        
        let isLeR:
          rite.sizeOf
            <
          iSup (fun param => (args param).sizeOf) + 1
        :=
          Order.lt_succ_of_le (Ordinal.le_iSup _ ArityTwo.fst)
        
        if hL:
          AllCausesInapp internalCycle boundVars left dL
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsLeft
            (extOfIntCycleFull.interp boundVars left isLeL dL hL)
        else if hR:
          AllCausesInapp internalCycle boundVars rite dR
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsRite
            (extOfIntCycleFull.interp boundVars rite isLeR dR hR)
        else
          let ⟨causeL, satBoundsL, isCauseL, isAppL⟩ :=
            hL.toEx fun _ p => p.implToAnd2 fun p => p.implToAnd
          let ⟨causeR, satBoundsR, isCauseR, isAppR⟩ :=
            hR.toEx fun _ p => p.implToAnd2 fun p => p.implToAnd
          
          let isInappUnion :=
            extOfIntCauseDistributesUnion causeL causeR boundVars ▸
            allInapp
              (causeL.union causeR)
              (satBoundsL.union satBoundsR)
              (fun isSat =>
                let dlPos := isCauseL {
                  contextInsHold :=
                    isSat.contextInsHold ∘ Or.inl
                  backgroundInsHold :=
                    isSat.backgroundInsHold ∘ Or.inl
                  backgroundOutHold :=
                    isSat.backgroundOutHold ∘ Or.inl
                }
                let drPos := isCauseR {
                  contextInsHold :=
                    isSat.contextInsHold ∘ Or.inr
                  backgroundInsHold :=
                    isSat.backgroundInsHold ∘ Or.inr
                  backgroundOutHold :=
                    isSat.backgroundOutHold ∘ Or.inr
                }
                ⟨⟨dL, dlPos⟩, ⟨dR, drPos⟩, dEq⟩)
          False.elim
            (IsCauseInappExtended.Not.union
              isAppL isAppR isInappUnion)
      |
        un left rite =>
        let inCinsLeftOrRite :=
          isCause.hurrDurrElim elimPosExternalUn
        
        inCinsLeftOrRite.elim
          (fun inCinsLeft =>
            let isLe: left.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
              Order.lt_succ_of_le (le_max_left _ _)
            
            let allInappLeft cause satBoundVars isCause :=
              allInapp cause satBoundVars (isCause.unLeft _)
            
            IsCauseInappExtended.cinsFailsCycle
              inCinsLeft
              (extOfIntCycleFull.interp
                boundVars left isLe d allInappLeft))
          (fun inCinsRite =>
            let isLe: rite.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
              Order.lt_succ_of_le (le_max_right _ _)
            
            let allInappRite cause satBoundVars isCause :=
              allInapp cause satBoundVars (isCause.unRite _)
            
            IsCauseInappExtended.cinsFailsCycle
              inCinsRite
              (extOfIntCycleFull.interp
                boundVars rite isLe d allInappRite))
      |
        ir left rite =>
        let isLeL: left.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_left _ _)
        let isLeR: rite.sizeOf < max left.sizeOf rite.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_right _ _)
        
        let ⟨inCinsLeft, inCinsRite⟩ :=
          isCause.hurrDurrElim elimPosExternalIr
        
        if hL:
          AllCausesInapp internalCycle boundVars left d
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsLeft
            (extOfIntCycleFull.interp boundVars left isLeL d hL)
        else if hR:
          AllCausesInapp internalCycle boundVars rite d
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsRite
            (extOfIntCycleFull.interp boundVars rite isLeR d hR)
        else
          let ⟨causeL, satBoundsL, isCauseL, isAppL⟩ :=
            hL.toEx fun _ p => p.implToAnd2 fun p => p.implToAnd
          let ⟨causeR, satBoundsR, isCauseR, isAppR⟩ :=
            hR.toEx fun _ p => p.implToAnd2 fun p => p.implToAnd
          
          let isInappUnion :=
            extOfIntCauseDistributesUnion causeL causeR boundVars ▸
            allInapp
              (causeL.union causeR)
              (satBoundsL.union satBoundsR)
              (isCauseL.union isCauseR)
          False.elim
            (IsCauseInappExtended.Not.union
              isAppL isAppR isInappUnion)
      |
        cpl expr =>
        have: expr.sizeOf < expr.sizeOf + 1 :=
          Order.lt_succ_of_le (le_refl _)
        
        let inBout :=
          (isCause.hurrDurrElimGreat elimPosExternalCpl).dne
        
        IsCauseInappExtended.boutFails
          inBout
          (isCauseToInsInterp
            (isCauseOfAllInappCpl allInapp)
            boundVars
            (isCauseOfAllInappCpl.satBoundVars boundVars)
            (fun inCins notBound =>
              inCins.elim
                (fun isBound =>
                  False.elim (notBound ⟨_, isBound⟩))
                (fun ⟨_, isIns⟩ => isIns))
            (fun inBins notBound =>
              inBins.elim
                (fun isBound =>
                  False.elim (notBound ⟨_, isBound⟩))
                (fun ⟨_, isIns⟩ => isIns))
            (fun inBout notBound =>
              inBout.elim
                (fun ⟨_, _, isBound⟩ =>
                  False.elim (notBound ⟨_, isBound⟩))
                (fun ⟨_, isOut⟩ => isOut)))
      |
        ifThen cond body =>
        let isLeC: cond.sizeOf < max cond.sizeOf body.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_left _ _)
        let isLeB: body.sizeOf < max cond.sizeOf body.sizeOf + 1 :=
          Order.lt_succ_of_le (le_max_right _ _)
        
        let ⟨⟨dC, inCinsCond⟩, inCinsBody⟩ :=
          isCause.hurrDurrElim elimPosExternalIfThen
        
        if hC:
          AllCausesInapp internalCycle boundVars cond dC
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsCond
            (extOfIntCycleFull.interp boundVars cond isLeC dC hC)
        else if hB:
          AllCausesInapp internalCycle boundVars body d
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsBody
            (extOfIntCycleFull.interp boundVars body isLeB d hB)
        else
          let ⟨causeCond, satBoundsCond, isCauseCond, isAppCond⟩ :=
            hC.toEx fun _ p => p.implToAnd2 fun p => p.implToAnd
          let ⟨causeBody, satBoundsBody, isCauseBody, isAppBody⟩ :=
            hB.toEx fun _ p => p.implToAnd2 fun p => p.implToAnd
          
          let isInappUnion :=
            extOfIntCauseDistributesUnion causeCond causeBody boundVars ▸
            allInapp
              (causeCond.union causeBody)
              (satBoundsCond.union satBoundsBody)
              (fun isSat =>
                let dcPos := isCauseCond {
                  contextInsHold :=
                    isSat.contextInsHold ∘ Or.inl
                  backgroundInsHold :=
                    isSat.backgroundInsHold ∘ Or.inl
                  backgroundOutHold :=
                    isSat.backgroundOutHold ∘ Or.inl
                }
                let dbPos := isCauseBody {
                  contextInsHold :=
                    isSat.contextInsHold ∘ Or.inr
                  backgroundInsHold :=
                    isSat.backgroundInsHold ∘ Or.inr
                  backgroundOutHold :=
                    isSat.backgroundOutHold ∘ Or.inr
                }
                ⟨⟨dC, dcPos⟩, dbPos⟩)
          False.elim
            (IsCauseInappExtended.Not.union
              isAppCond isAppBody isInappUnion)
      |
        arbUn x body =>
        let isLe: body.sizeOf < body.sizeOf + 1 :=
          Ordinal.lt_succ body.sizeOf
        let ⟨dX, inCins⟩ :=
          isCause.hurrDurrElim elimPosExternalArbUn
        let allInapp cause satBoundVars isCause:
          IsCauseInappExtended
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (extOfIntCycleBare internalCycle)
            (extOfIntCause
              cause
              (⟨dX, x⟩ :: boundVars))
        :=
          let causeSatBound := satBoundVars IsBoundTo.InHead
          let causeLeWith := causeSatBound.leWithBound
          let whyIsTypeInferenceBroken:
            IsWeakCause pairSalgebra (cause.withBound x dX) d body
          :=
            isCause.toSuperCause causeLeWith
          let isInapp :=
            allInapp
              (cause.exceptVar x)
              satBoundVars.exceptHeadSatTail
              whyIsTypeInferenceBroken.arbUn
          isInapp.toSuperCause
            (extOfIntExceptLeBoundHead cause dX x)
        IsCauseInappExtended.cinsFailsCycle
          inCins
          (extOfIntCycleFull.interp
            (⟨dX, x⟩ :: boundVars) body isLe d allInapp)
      |
        arbIr x body =>
        let isLe: body.sizeOf < body.sizeOf + 1 :=
          Ordinal.lt_succ body.sizeOf
        
        let inCins := isCause.hurrDurrElim elimPosExternalArbIr
        
        if h:
          ∃ dB,
            AllCausesInapp
              internalCycle (⟨dB, x⟩ :: boundVars) body d
        then
          let ⟨dB, allInapp⟩ := h
          IsCauseInappExtended.cinsFailsCycle
            (inCins dB)
            (extOfIntCycleFull.interp
              (⟨dB, x⟩ :: boundVars)
              body
              isLe
              d
              allInapp)
        else
          let allApplicable :=
            h.toAll fun _ p =>
              (p.toEx fun _ p =>
                p.implToAnd2 fun p =>
                  p.implToAnd).unwrap
          let isLe :=
            extOfIntCauseArbUn
              (fun dX => allApplicable dX)
              boundVars
              x
          let isInappArbUn :=
            allInapp
              (Cause.arbUn fun dX =>
                (allApplicable dX).val.exceptVar x)
              (Cause.SatisfiesBoundVars.arbUn
                (fun dX => allApplicable dX)
                x
                (fun dX => (allApplicable dX).property.left))
              (IsWeakCause.arbUnOf
                (salg := pairSalgebra)
                (causes := fun dX => (allApplicable dX).val)
                (fun dX =>
                  let satBoundVars :=
                    (allApplicable dX).property.left
                  let causeSatBound := satBoundVars IsBoundTo.InHead
                  let causeLeWith := causeSatBound.leWithBound
                  let whyIsTypeInferenceBroken :=
                    @IsWeakCause.toSuperCause
                      pairSignature
                      pairSalgebra
                      (allApplicable dX).val
                      d
                      body
                      ((allApplicable dX).val.withBound x dX)
                      (allApplicable dX).property.right.left
                      causeLeWith
                  whyIsTypeInferenceBroken))
          False.elim
            (IsCauseInappExtended.Not.arbUn
              (fun (dX: pairSalgebra.D) =>
                (allApplicable dX).property.right.right)
              (isInappArbUn.toSuperCause isLe))
    termination_by expr.sizeOf
    end
    
    def inEmptyCycleInternalToIsEmptyCycleExternal
      (internalCycleIsEmpty:
        ∀ {d x},
          ⟨d, x⟩ ∈ internalCycle →
          (internalCause: Cause Pair) →
          IsWeakCause
            pairSalgebra
            internalCause
            d
            (theInternalDefList.getDef x) →
          IsCauseInapplicable
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (extOfIntCycleBare internalCycle)
            (extOfIntCause internalCause))
      
      (inCycle:
        extOfIntCycleFull Option.none internalCycle ⟨dExt, xExt⟩)
      (externalCause: Cause Pair)
      (isCauseExternal:
        IsWeakCause
          pairSalgebra
          externalCause
          dExt
          (uniDefList.theExternalDefList.getDef xExt))
    :
      IsCauseInappExtended
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (extOfIntCycleFull Option.none internalCycle)
        externalCause
    :=
      open IsCauseInappExtended in
      byContradiction fun isApp =>
        match inCycle with
        | extOfIntCycleFull.interp _ _ sizeBound d allCausesInapp =>
          let isInapp :=
            inappExtOfAllInappInt allCausesInapp isCauseExternal
          isApp (isInapp.toSuperCycle
            (extOfIntCycleFull.toLargerBound internalCycle sizeBound))
        | @extOfIntCycleFull.theSet _ _ ⟨dInt, xInt⟩ inIntCycle =>
          -- A Lean bug, this breaks def equality:
          -- let ⟨xthDefEnc, isDlExpr⟩ :=
          let xthExpr := IsTheDefListExprPair.getNthExpr xInt
          
          let notXthNins
            p
            (neq: p ≠ xthExpr.exprEnc)
            (inCins:
              ⟨pair xInt p, uniDefList.theDefList⟩
                ∈
              externalCause.contextIns)
          :
            False
          :=
            let out := Out.isComplete _ _ fun isPos =>
              let isDlExprP: IsTheDefListExprPair _ _ := show
                IsTheDefListExpr (pair (fromNat xInt) p)
              from
                Inw.toIsTheDefListExpr isPos
              neq (isDlExprP.isUnique xthExpr.isNth)
            isApp (cinsFailsOut inCins out)
          
          let interpInCins :=
            isCauseExternal.hurrDurrElim
              (R := externalCause.contextIns ⟨
                pair zero (pair xthExpr.exprEnc dInt),
                uniDefList.interpretation,
              ⟩)
              fun inw =>
                let ⟨_xEnc, ⟨_inwNatXEnc, inw⟩⟩ := inwUnDomElim inw
                let ⟨inwL, inwR⟩ := inwPairElim inw
                let xEncEqX := inwBoundElim inwL
                let ⟨expr, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim inwR
                let inwDl := inwCallElimBound inwArg rfl nat502Neq500
                let exprEq: expr = xthExpr.exprEnc :=
                  byContradiction fun neq =>
                    notXthNins _ neq (xEncEqX ▸ inwDl)
                let ⟨_z, inw, inwZero⟩ := inwCallExprElim inwFn
                let zEq := inwZeroElim inwZero
                zEq ▸ exprEq ▸ inw
          
          let inCycleExt :=
            exprToEncoding.isInverse xthExpr.isNth.isExpr ▸
            extOfIntCycleFull.interp
              []
              xthExpr.exprEnc.encodingToExpr
              trivial
              dInt
              (fun internalCause _ isCause =>
                let isInapp :=
                  internalCycleIsEmpty
                    inIntCycle
                    internalCause
                    (theInternalDefList.eqExpr xInt ▸
                    isCause)
                isInapp.toExtended)
          
          isApp (cinsFailsCycle interpInCins inCycleExt)
    
    
    def insTheSetOfInterp
      (ins: InsInterp [] d (theInternalDefList.getDef x))
    :
      Ins
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (pair (fromNat x) d)
        uniDefList.theSet
    :=
      let isXth := (IsTheDefListExprPair.getNthExpr x).isNth
      Ins.isComplete _ _
        (insWfmDefToIns
          (insUnDom
            (insNatEncoding
              (fromNat.isNatEncoding x))
            (insPair
              insBound
              (insCallExpr
                (insCallExpr
                  ins.isSound
                  insZero)
                (insCallExpr
                  (insTheDefListExpr
                    (theInternalDefList.eqEnc x ▸ isXth))
                  (insFree
                    (insFree
                      insBound
                      nat501Neq500)
                    nat502Neq500))))))
    
    def isCauseInternalToInsExternal
      (isCauseInternal:
        IsStrongCause
          pairSalgebra
          internalCause
          d
          (theInternalDefList.getDef x))
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.contextIns →
          Ins
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (binsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.backgroundIns →
          Ins
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.backgroundOut →
          Out
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
    :
      Ins
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      insTheSetOfInterp
        (isCauseToInsInterp
          isCauseInternal
          []
          nofun
          (fun inCins _ => cinsIns inCins)
          (fun inBins _ => binsIns inBins)
          (fun inBout _ => boutOut inBout))
    
    def inEmptyCycleInternalToOutExternal
      {x: Nat}
      (inCycle: ⟨d, x⟩ ∈ internalCycle)
      (isEmptyCycle:
        ∀ {d x},
          ⟨d, x⟩ ∈ internalCycle →
          (internalCause: Cause Pair) →
          IsWeakCause
            pairSalgebra
            internalCause
            d
            (theInternalDefList.getDef x) →
          IsCauseInapplicable
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (extOfIntCycleBare internalCycle)
            (extOfIntCause internalCause))
    :
      Out
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      Out.intro4
        (extOfIntCycleFull Option.none internalCycle)
        (inEmptyCycleInternalToIsEmptyCycleExternal
          isEmptyCycle)
        (extOfIntCycleFull.theSet inCycle)
    
    
    def insInternalToInsExternal
      (ins: Ins pairSalgebra theInternalDefList d x)
    :
      Ins
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      -- Cannot use structural recursion on mutual inductives :(
      open IsCauseInapplicable in
      ins.rec
        (motive_1 :=
          fun d x _ =>
            Ins
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseInapplicable
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (extOfIntCycleBare cycle)
              (extOfIntCause cause))
        (motive_3 :=
          fun d x _ =>
            Out
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (fun _ _ _ isCause _ _ _ =>
          isCauseInternalToInsExternal isCause)
        (fun
          -- TODO try removing after this issue is fixed:
          -- https://github.com/leanprover/lean4/issues/5925
          {_: Set (ValVar pairSalgebra.D)}
          cause _ _ inCins inCycle
        =>
          blockedContextIns
            (salg := pairSalgebra)
            (extOfIntCause cause)
            (And.intro rfl ⟨_, inCins, rfl, nofun⟩)
            (extOfIntCycleBare.theSet inCycle))
        (fun cause _ _ inBins _ ihOut =>
          blockedBackgroundIns
            (salg := pairSalgebra)
            (extOfIntCause cause)
            (And.intro rfl ⟨_, inBins, rfl, nofun⟩)
            ihOut)
        (fun cause _ _ inBout _ ihIns =>
          blockedBackgroundOut
            (salg := pairSalgebra)
            (extOfIntCause cause)
            (And.intro rfl ⟨_, inBout, rfl, nofun⟩)
            ihIns)
        (fun _ _ => inEmptyCycleInternalToOutExternal)
    
    def outInternalToOutExternal
      (out: Out pairSalgebra theInternalDefList d x)
    :
      Out
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (Pair.pair (fromNat x) d)
        uniDefList.theSet
    :=
      -- Cannot use structural recursion on mutual inductives :(
      open IsCauseInapplicable in
      out.rec
        (motive_1 :=
          fun d x _ =>
            Ins
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseInapplicable
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (extOfIntCycleBare cycle)
              (extOfIntCause cause))
        (motive_3 :=
          fun d x _ =>
            Out
              pairSalgebra
              uniDefList.theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (fun _ _ _ isCause _ _ _ =>
          isCauseInternalToInsExternal isCause)
        (fun
          -- TODO try removing after this issue is fixed:
          -- https://github.com/leanprover/lean4/issues/5925
          {_: Set (ValVar pairSalgebra.D)}
          cause _ _ inCins inCycle
        =>
          blockedContextIns
            (salg := pairSalgebra)
            (extOfIntCause cause)
            (And.intro rfl ⟨_, inCins, rfl, nofun⟩)
            (extOfIntCycleBare.theSet inCycle))
        (fun cause _ _ inBins _ ihOut =>
          blockedBackgroundIns
            (salg := pairSalgebra)
            (extOfIntCause cause)
            (And.intro rfl ⟨_, inBins, rfl, nofun⟩)
            ihOut)
        (fun cause _ _ inBout _ ihIns =>
          blockedBackgroundOut
            (extOfIntCause cause)
            (show
              _ ∈ (extOfIntCause _).backgroundOut
            from
              And.intro rfl ⟨_, inBout, rfl, nofun⟩)
            ihIns)
        (fun _ _ => inEmptyCycleInternalToOutExternal)
    
    
    def theInternalWfmEncoding.isGeWfm:
      theInternalWfm ⊑ uniDefList.theInternalWfmEncoding
    :=
      fun _ => {
        defLe :=
          fun _ insValInternal =>
            let ins := Ins.isComplete _ _ insValInternal
            (insInternalToInsExternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraAB
              fun outValInternal =>
                let out := Out.isComplete _ _ outValInternal
                (outInternalToOutExternal out).isSound
      }
    
  end uniSet3
end Pair
