/-
  `Pair.uniSet3.isUniversal` is the main result of this volume.
  It states that any definable triset of pairs is in a sense
  "contained" in the triset `uniSet3`. See chapter 7 for more
  info.
  
  TODO summarize informally the proof strategy here.
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
    
    
    /-
      Converts an internal cause to the corresponding external
      cause. The external cause also includes requirements that
      are necessary for the interpretation (ie. the definition
      number 34 in `theExternalDefList`) to work correctly in the
      external valuation.
    -/
    inductive IsInExternalCause
      (internalCause: Set (ValVar Pair))
      (isIns: Prop)
      (vv: ValVar Pair)
    :
      Prop
    
    -- TODO:
    -- 0  - NatIsOk
    -- 33 - GetBoundIsOk
    -- 7  - ExprEncodingIsOk
    -- 32 - TheDefListIsOk
    
    | TheSetIsOk
      (xEq: vv.x = uniDefList.theSet)
      (matchesInternalPart:
        ∃ vvI ∈ internalCause, vv.d = (vvI.x, vvI.d))
    
    
    def externalOfInternalCause
      (internalCause: Cause Pair)
    :
      Cause Pair
    :=
      let ic := internalCause
      {
        contextIns := IsInExternalCause ic.contextIns True
        backgroundIns := IsInExternalCause ic.backgroundIns True
        backgroundOut := IsInExternalCause ic.backgroundOut False
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
    
    
    def externalOfInternalCycle
      (internalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    :=
      fun vv =>
        vv.x = uniDefList.theSet ∧
        ∃ vvI ∈ internalCycle, vv.d = (vvI.x, vvI.d)
    
    def internalOfExternalCycle
      (externalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    :=
      fun ⟨d, x⟩ =>
        externalCycle ⟨Pair.pair x d, uniDefList.theSet⟩
    
    
    def causeExtIntExtSubset
      (externalCause: Cause Pair)
    :
      (theSetOfInternalCause (internalOfExternalCause externalCause))
        ⊆
      externalCause
    :=
      {
        cinsLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inCins, dEq⟩⟩⟩ =>
            xEq ▸ dEq ▸ inCins
        binsLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inBins, dEq⟩⟩⟩ =>
            xEq ▸ dEq ▸ inBins
        boutLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inBout, dEq⟩⟩⟩ =>
            xEq ▸ dEq ▸ inBout
      }
    
    
    def isStrongExtOfInt
      (isCauseInternal:
        IsStrongCause
          pairSalgebra
          cause
          d
          (theInternalDefList.getDef x))
    :
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
          open IsInExternalCause in
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
        -- TODO it remains to prove that, assuming `b` and `c`
        -- satisfy the constraints of `IsInExternalCause`,
        -- the valuation's definite members are equal.
        sorry
    
    def isWeakIntOrInappExtOfExt
      (inCycle: ⟨d, x⟩ ∈ internalCycle)
      (isCauseExternal:
        IsWeakCause
          pairSalgebra
          externalCause
          (Pair.pair (fromNat x) d)
          (theExternalDefList.getDef uniDefList.theSet))
    :
      Or
        (IsWeakCause
          pairSalgebra
          (internalOfExternalCause externalCause)
          d
          (theInternalDefList.getDef x))
        (IsCauseInapplicable
          pairSalgebra
          theExternalDefList.toDefList
          -- TODO should the external cycle be defined also
          -- in terms of the external cause?
          (externalOfInternalCycle internalCycle)
          externalCause)
    :=
      -- TODO if external cause is compatible with external wfm,
      -- then weak else inapplicable
      if
        hCins:
          ∃ vv ∈ externalCause.contextIns,
            vv.d ∉ (uniDefList.theExternalWfm vv.x).defMem
      then
        let ⟨⟨d, x⟩, inCins, ninDef⟩ := hCins
        
        Or.inr
          (IsCauseInapplicable.blockedContextIns
            externalCause
            inCins
            sorry)
      else
        let asdf:
          IsWeakCause
            pairSalgebra
            (internalOfExternalCause externalCause)
            d
            (theInternalDefList.getDef x)
        :=
          fun {b c} isSat =>
            let isDefExternal:
              Set3.posMem
                (Expr.interpretation
                  pairSalgebra
                  (externalOfInternal b)
                  (externalOfInternal c)
                  (theExternalDefList.getDef uniDefList.theSet))
                (Pair.pair x d)
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
        sorry
    
    
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
          internalCause
          d
          (theInternalDefList.getDef x))
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.contextIns →
          Ins
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (binsIns:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.backgroundIns →
          Ins
            pairSalgebra
            theExternalDefList.toDefList
            (Pair.pair x d)
            uniDefList.theSet)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨d, x⟩ ∈ internalCause.backgroundOut →
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
          (externalOfInternalCause internalCause)
          (Pair.pair x d)
          (theExternalDefList.getDef uniDefList.theSet)
      :=
        isStrongExtOfInt isCauseInternal
      
      Ins.intro
        _
        _
        (externalOfInternalCause internalCause)
        isCauseExternal
        (fun {dd xx} ⟨xEq, ⟨_, ⟨inCinsInternal, dEq⟩⟩⟩ =>
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          cinsIns inCinsInternal)
        (fun {dd xx} ⟨xEq, ⟨_, ⟨inBinsInternal, dEq⟩⟩⟩ =>
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          binsIns inBinsInternal)
        (fun {dd xx} ⟨xEq, ⟨_, ⟨inBoutInternal, dEq⟩⟩⟩ =>
          (show xx = _ from xEq) ▸
          (show dd = _ from dEq) ▸
          boutOut inBoutInternal)
    
    def isCauseExternalToInsInternal
      (isCauseExternal:
        IsStrongCause
          pairSalgebra
          externalCause
          (Pair.pair (fromNat x) d)
          (theExternalDefList.getDef uniDefList.theSet))
      (cinsIns:
        ∀ {d} {x: Nat},
          ⟨Pair.pair x d, uniDefList.theSet⟩
            ∈ externalCause.contextIns →
          Ins pairSalgebra theInternalDefList d x)
      (binsIns:
        ∀ {d} {x: Nat},
          ⟨Pair.pair x d, uniDefList.theSet⟩
            ∈ externalCause.backgroundIns →
          Ins pairSalgebra theInternalDefList d x)
      (boutOut:
        ∀ {d} {x: Nat},
          ⟨Pair.pair x d, uniDefList.theSet⟩
            ∈ externalCause.backgroundOut →
          Out pairSalgebra theInternalDefList d x)
    :
      Ins pairSalgebra theInternalDefList d x
    :=
      sorry
    
    
    /-
      For a value `d` that is provably out of the internal definition
      `x`, the pair `(x, d)` is provably out of `theSet`.
      
      We proceed by induction on the structure of the proof, and
      this is the inductive step for `Out`. The induction hypothesis
      is incorporated into the parameter `isEmptyCycle`.
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
          
          (isWeakIntOrInappExtOfExt inCycle isCauseExternal).elim
            (fun isCauseInternal =>
              let isInapp :=
                isEmptyCycle
                  inCycle
                  (internalOfExternalCause externalCause)
                  isCauseInternal
              
              isInapp.toSuperCause
                (causeExtIntExtSubset externalCause))
            id)
        ⟨rfl, _, inCycle, rfl⟩
    
    def inEmptyCycleExternalToOutInternal
      {externalCycle: Set (ValVar Pair)}
      {d: Pair}
      {x: Nat}
      (inCycle: ⟨Pair.pair x d, uniDefList.theSet⟩ ∈ externalCycle)
      (isEmptyCycle:
        ∀ {d x},
          ⟨Pair.pair x d, uniDefList.theSet⟩ ∈ externalCycle →
          (externalCause: Cause Pair) →
          IsWeakCause
            pairSalgebra
            externalCause
            (Pair.pair x d)
            (theExternalDefList.getDef uniDefList.theSet) →
          IsCauseInapplicable
            pairSalgebra
            theInternalDefList
            (internalOfExternalCycle externalCycle)
            (internalOfExternalCause externalCause))
    :
      Out
        pairSalgebra
        theInternalDefList
        d
        x
    :=
      sorry
    
    
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
      open IsInExternalCause in
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
      Out
        pairSalgebra
        theExternalDefList.toDefList
        (Pair.pair (fromNat x) d)
        uniDefList.theSet
    :=
      -- Cannot use structural recursion on mutual inductives :(
      open IsCauseInapplicable in
      open IsInExternalCause in
      out.rec
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
    
    
    def insExternalToInsInternal
      (ins:
        Ins
          pairSalgebra
          theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Ins pairSalgebra theInternalDefList d x
    :=
      open IsCauseInapplicable in
      ins.rec
        (motive_1 :=
          fun d x _ =>
            x = uniDefList.theSet →
            (xInt: Nat) →
            (dInt: Pair) →
            d = Pair.pair xInt dInt →
            Ins pairSalgebra theInternalDefList dInt xInt)
        (motive_2 :=
          fun cycle cause _ =>
            IsCauseInapplicable
              pairSalgebra
              theInternalDefList
              (internalOfExternalCycle cycle)
              (internalOfExternalCause cause))
        (motive_3 :=
          fun d x _ =>
            x = uniDefList.theSet →
            (xInt: Nat) →
            (dInt: Pair) →
            d = Pair.pair xInt dInt →
            Out pairSalgebra theInternalDefList dInt xInt)
        (fun _ _ _ isCause _ _ _
          cinsIns binsIns boutOut
          xEq xInt dInt dEq
        =>
          isCauseExternalToInsInternal
            (xEq ▸ dEq ▸ isCause)
            (cinsIns · rfl _ _ rfl)
            (binsIns · rfl _ _ rfl)
            (boutOut · rfl _ _ rfl))
        (fun cause _ _ inCins inCycle =>
          blockedContextIns
            (internalOfExternalCause cause)
            sorry
            sorry)
        sorry
        sorry
        (fun cycle _ inCycle isEmptyCycle xEq _ _ dEq =>
          inEmptyCycleExternalToOutInternal
            (xEq ▸ dEq ▸ inCycle)
            isEmptyCycle)
        rfl
        x
        d
        rfl
    
    def outExternalToOutInternal
      (out:
        Out
          pairSalgebra
          theExternalDefList.toDefList
          (Pair.pair (fromNat x) d)
          uniDefList.theSet)
    :
      Out pairSalgebra theInternalDefList d x
    :=
      sorry -- TODO out.rec, like above
    
    
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
                (outInternalToOutExternal out).isSound
      }
    
    def theInternalValuation.isLeWfm:
      theInternalValuation ⊑ theInternalWfm
    :=
      fun _ => {
        defLe :=
          fun _ insValInternal =>
            let ins := Ins.isComplete _ _ insValInternal
            (insExternalToInsInternal ins).isSound
        posLe :=
          fun _ =>
            Function.contraDne
              fun outValInternal =>
                let out := Out.isComplete _ _ outValInternal
                (outExternalToOutInternal out).isSound
      }
    
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
    
    -- TODO an explicit proof that `uniSet3` is definable?
    
    -- TODO roadmap to publishing:
    -- 0. finish this volume
    -- 1. clean up the `HM` folder
    -- 2. remove the pdf from the repo (it's ok if it stays
    --    in history despite how embarassing it is)
    -- 3. and make it public :tada:
    
  end uniSet3
end Pair
