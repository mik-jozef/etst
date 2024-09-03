/-
  `Pair.uniSet3.isUniversal` is the main result of this volume.
  It states that any definable triset of pairs is in a sense
  "contained" in the triset `uniSet3`. See chapter 7 for more
  info.
-/

import UniSet3.Ch10_S00_TheInternalDefList


namespace Pair
  namespace uniSet3
    def theExternalDefList := uniDefList.theExternalDefList
    
    
    def theInternalValuation.interpretationsEqual
      (x: Nat)
    :
      Set3.pairCallJust uniSet3 (fromNat x)
        =
      Expr.interpretation
        pairSalgebra
        theInternalValuation
        theInternalValuation
        (encodingToExpr (IsTheDefListExprPair.getNthExpr x).expr)
    :=
      Set3.ord.standard.le_antisymm _ _ ⟨
        fun _ => inDefNthOfInsTheSet,
        fun _ => inPosNthOfInwTheSet,
      ⟩ ⟨
        fun _ => insTheSetOfInDefNth,
        fun _ => inwTheSetOfInPosNth,
      ⟩
    
    
    def interpretationsEqual
      (b c: Valuation Pair)
      -- TODO extra conditions will be necessary
    :
      (Expr.interpretation
        pairSalgebra
        (internalOfExternal b)
        (internalOfExternal c)
        (theInternalDefList.getDef x)).defMem d
        =
      (Expr.interpretation
        pairSalgebra
        b
        c
        (theExternalDefList.getDef uniDefList.theSet)
      ).defMem ((fromNat x).pair d)
    :=
      sorry
    
    
    inductive IsExternalCausePart
      (internalPart: Set (ValVar Pair))
      (isIns: Prop)
      (vv: ValVar Pair)
    :
      Prop
    | TheSetIsOk
      (xEq: vv.x = uniDefList.theSet)
      (matchesInternalPart:
        ∃ vvI ∈ internalPart, vv.d = (vvI.x, vvI.d))
    
    def externalOfInternalCause
      (internalCause: Cause Pair)
    :
      Cause Pair
    :=
      let ic := internalCause
      {
        contextIns := IsExternalCausePart ic.contextIns True
        backgroundIns := IsExternalCausePart ic.backgroundIns True
        backgroundOut := IsExternalCausePart ic.backgroundOut False
      }
    
    /-
      A part of the external cause that's just the contents
      of `theSet`.
    -/
    def theSetOfInternalCause
      (internalCause: Cause Pair)
    :
      Cause Pair
    := {
      contextIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.contextIns,
            d = (vvI.x, vvI.d)
      backgroundIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundIns,
            d = (vvI.x, vvI.d)
      backgroundOut :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundOut,
            d = (vvI.x, vvI.d)
    }
    
    def internalOfExternalCause
      (externalCause: Cause Pair)
    :
      Cause Pair
    := {
      contextIns :=
        fun ⟨d, x⟩ =>
          externalCause.contextIns
            ⟨Pair.pair x d, uniDefList.theSet⟩
      backgroundIns :=
        fun ⟨d, x⟩ =>
          externalCause.backgroundIns
            ⟨Pair.pair x d, uniDefList.theSet⟩
      backgroundOut :=
        fun ⟨d, x⟩ =>
          externalCause.backgroundOut
            ⟨Pair.pair x d, uniDefList.theSet⟩
    }
    
    def eqAsdf
      (cause: Cause Pair)
    :
      (theSetOfInternalCause (internalOfExternalCause cause))
        =
      cause
    :=
      sorry
    
    def externalOfInternalCycle
      (internalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    :=
      fun vv =>
        vv.x = uniDefList.theSet ∧
        ∃ vvI ∈ internalCycle, vv.d = (vvI.x, vvI.d)
      
    
    /-
      For a value `d` that is provably in the internal definition
      `x`, `(x, d)` is provably in the external definition `theSet`.
      
      We proceed by induction on the structure of the proof, and
      this is the inductive step for `Ins`. The last three arguments
      are the inductive hypotheses.
    -/
    def isCauseInternalToInsExternal
      (isCauseInternal:
        IsStrongCause
          pairSalgebra
          cause
          d
          (theInternalDefList.getDef x))
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ cause.contextIns →
          Ins
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (binsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ cause.backgroundIns →
          Ins
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ cause.backgroundOut →
          Out
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
    :
      Ins
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      let isCauseExternal:
        IsStrongCause
          pairSalgebra
          (externalOfInternalCause cause)
          (Pair.pair x d)
          (theExternalDefList.getDef uniDefList.theSet)
      :=
        fun {b c} isSat =>
          let isDefInternal:
            Set3.defMem
              ((theInternalDefList.getDef x).interpretation
                pairSalgebra
                (internalOfExternal b)
                (internalOfExternal c))
              d
          :=
            open IsExternalCausePart in
            isCauseInternal {
              contextInsHold :=
                fun {dd xx} inCins =>
                  isSat.contextInsHold
                    (TheSetIsOk rfl ⟨⟨dd, xx⟩, inCins, rfl⟩)
              backgroundInsHold :=
                fun {dd xx} inBins =>
                  isSat.backgroundInsHold
                    (TheSetIsOk rfl ⟨⟨dd, xx⟩, inBins, rfl⟩)
              backgroundOutHold :=
                fun {dd xx} inBout =>
                  isSat.backgroundOutHold
                    (TheSetIsOk rfl ⟨⟨dd, xx⟩, inBout, rfl⟩)
            }
          sorry
      
      Ins.intro
        _
        _
        (externalOfInternalCause cause)
        isCauseExternal
        (fun {dd xx} ⟨xEq, ⟨vv, lr⟩⟩ =>
          -- TODO try destructuring right in function head
          -- when this is a part of a stable Lean release:
          -- https://github.com/leanprover/lean4/issues/3242
          let ⟨inCinsInternal, dEq⟩ := lr
          
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          cinsIns inCinsInternal)
        (fun {dd xx} ⟨xEq, ⟨vv, lr⟩⟩ =>
          let ⟨inBinsInternal, dEq⟩ := lr
          
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          binsIns inBinsInternal)
        (fun {dd xx} ⟨xEq, ⟨vv, lr⟩⟩ =>
          let ⟨inBoutInternal, dEq⟩ := lr
          
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          boutOut inBoutInternal)
    
    /-
      For a value that is provably out of the internal definition
      `x`, `(x, d)` is provably out of the external definition
      `theSet`.
      
      We proceed by induction on the structure of the proof, and
      this is the inductive step for `Out`. TODO this description
      is likely wrong.
    -/
    def inEmptyCycleInternalToOutExternal
      {internalCycle: Set (ValVar Pair)}
      {d: Pair}
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
            theExternalDefList.toDefList
            (externalOfInternalCycle internalCycle)
            (theSetOfInternalCause internalCause))
    :
      Out
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      Out.intro
        (externalOfInternalCycle internalCycle)
        (fun
          {dd xx}
          ⟨xEq, vvI, inCycle, dEq⟩
          externalCause
          isCauseExternal
        =>
          let isCauseExternal:
            IsWeakCause
              pairSalgebra
              externalCause
              (Pair.pair vvI.x vvI.d)
              (theExternalDefList.getDef uniDefList.theSet)
          := by
            rw [xEq.symm]
            rw [show Pair.pair vvI.x vvI.d = dd from dEq.symm]
            exact isCauseExternal
          
          let isCauseInternal:
            IsWeakCause
              pairSalgebra
              (internalOfExternalCause externalCause)
              vvI.d
              (theInternalDefList.getDef vvI.x)
          :=
            fun {b c} isSat =>
              let isDefExternal:
                Set3.posMem
                  (Expr.interpretation
                    pairSalgebra
                    (externalOfInternal b)
                    (externalOfInternal c)
                    (theExternalDefList.getDef uniDefList.theSet))
                  (Pair.pair vvI.x vvI.d)
              :=
                isCauseExternal {
                  contextInsHold :=
                    fun inCins =>
                      let age :=
                        isSat.contextInsHold
                          inCins
                      sorry
                  backgroundInsHold := sorry
                  backgroundOutHold := sorry
                }
              sorry
          
          let asdf :=
            isEmptyCycle
              inCycle
              (internalOfExternalCause externalCause)
              isCauseInternal
          sorry)
        ⟨rfl, _, inCycle, rfl⟩
    
    /-
      This function invokes the induction principle whose inductive
      steps are `isCauseInternalToInsExternal` and
      `inEmptyCycleInternalToOutExternal`. (`IsCauseInapplicable`
      is handled here as well.)
    -/
    def insInternalToInsExternal
      (ins: Ins pairSalgebra theInternalDefList d x)
    :
      Ins
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      -- Cannot use structural recursion on mutual inductives :(
      open IsCauseInapplicable in
      open IsExternalCausePart in
      ins.rec
        (motive_1 :=
          fun d x _ =>
            Ins
              pairSalgebra
              theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseInapplicable
              pairSalgebra
              theExternalDefList.toDefList
              (externalOfInternalCycle cycle)
              (theSetOfInternalCause cause))
        (motive_3 :=
          fun d x _ =>
            Out
              pairSalgebra
              theExternalDefList.toDefList
              (Pair.pair x d)
              uniDefList.theSet)
        (fun _ _ _ isCause _ _ _ =>
          isCauseInternalToInsExternal isCause)
        (fun cause _ _ inCins inCycle =>
          blockedContextIns
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).contextIns
            from
              And.intro rfl ⟨_, inCins, rfl⟩)
            (show _ ∈ externalOfInternalCycle _ from
              ⟨rfl, _, inCycle, rfl⟩))
        (fun cause _ _ inBins _ ihOut =>
          blockedBackgroundIns
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).backgroundIns
            from
              And.intro rfl ⟨_, inBins, rfl⟩)
            ihOut)
        (fun cause _ _ inBout _ ihIns =>
          blockedBackgroundOut
            (theSetOfInternalCause cause)
            (show
              _ ∈ (theSetOfInternalCause _).backgroundOut
            from
              And.intro rfl ⟨_, inBout, rfl⟩)
            ihIns)
        (fun _ _ => inEmptyCycleInternalToOutExternal)
    
    def outInternalToOutExternal
      (out: Out pairSalgebra theInternalDefList d x)
    :
      ¬ d ∈ (theInternalValuation x).posMem
    :=
      sorry
    
    
    def theInternalValuation.isGeWfm:
      theInternalWfm ⊑ theInternalValuation
    :=
      fun _ => {
        defLe :=
          fun _ insValExternal =>
            let ins := Ins.isComplete _ _ insValExternal
            (insInternalToInsExternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraDne
              fun outValExternal =>
                let out := Out.isComplete _ _ outValExternal
                outInternalToOutExternal out
      }
    
    def theInternalValuation.isLeWfm:
      theInternalValuation ⊑ theInternalWfm
    :=
      fun x =>
        sorry
    
    def theInternalValuation.eqWfm:
      theInternalValuation = theInternalWfm
    :=
      (Valuation.ord.approximation Pair).le_antisymm
        _ _ isLeWfm isGeWfm
    
    def isUniversal
      (s3: Set3 Pair)
      (isDef: pairSalgebra.IsDefinable s3)
    :
      ∃ x: Nat, uniSet3.pairCallJust (fromNat x) = s3
    :=
      let ⟨x, s3EqWfm⟩ := theInternalDefList.hasAllDefinable s3 isDef
      
      ⟨
        x,
        s3EqWfm ▸ theInternalValuation.eqWfm ▸ rfl
      ⟩
    
  end uniSet3
end Pair
