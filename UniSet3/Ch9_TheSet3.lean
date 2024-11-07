/-
  This whole chapter is dedicated to proving that the interpretation
  as defined in the external definition list works as intended.
  
  The four main results,
  
      `inDefNthOfInsTheSet` \,,
      `inPosNthOfInwTheSet` \,,
      `insTheSetOfInDefNth` \,, and
      `inwTheSetOfInPosNth` \,,
  
  are used in Chapter 10 to prove
  
      `uniSet3.isModelOfInternalDefList` \,.
  
  TODO rewrite the chapter description
  
  TODO go through the chapter and make sure there is no unused code.
-/

import UniSet3.Ch8_S13_TheInternalDefList
import Utils.CauseSatisfiesBoundVars
import Utils.ElimExternal
import Utils.InsInterp
import Utils.IsStrongCause
import Utils.IsWeakCause
import Utils.NopeInterp
import Utils.OutIntro4


namespace Pair
  noncomputable def uniSet3 :=
    uniDefList.theExternalWfm uniDefList.theSet
  
  namespace uniSet3
    open Expr
    open PairExpr
    
    
    def IsBound.Not.notBoundHeadNotEq
      (notBound: ¬ IsBound (⟨dB, xB⟩ :: boundVars) x)
    :
      x ≠ xB
    :=
      fun xEq =>
        notBound ⟨
          dB,
          xEq ▸
          IsGetBound.InHead
            (fromNat.isNatEncoding x)
            dB
            (boundVarsEncoding boundVars)
        ⟩
    
    def IsBound.Not.notBoundTail
      (notBound: ¬ IsBound (⟨dB, xB⟩ :: boundVars) x)
      (xNeq: x ≠ xB)
    :
      ¬ IsBound boundVars x
    :=
      let encNeq := fromNat.injNeq xNeq.symm
      fun ⟨d, isGetBound⟩ =>
        notBound ⟨d, IsGetBound.InTail isGetBound dB encNeq⟩
    
    
    def externalOfInternalCause
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
            IsVarFree vvI.x boundVars
      backgroundIns :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundIns,
            d = (vvI.x, vvI.d) ∧
            IsVarFree vvI.x boundVars
      backgroundOut :=
        fun ⟨d, x⟩ =>
          x = uniDefList.theSet ∧
          ∃ vvI ∈ internalCause.backgroundOut,
            d = (vvI.x, vvI.d) ∧
            IsVarFree vvI.x boundVars
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
    
    def causeExtIntExtSubset
      (externalCause: Cause Pair)
    :
      (externalOfInternalCause
        (internalOfExternalCause externalCause))
        ⊆
      externalCause
    :=
      {
        cinsLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inCins, dEq, _⟩⟩⟩ =>
            xEq ▸ dEq ▸ inCins
        binsLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inBins, dEq, _⟩⟩⟩ =>
            xEq ▸ dEq ▸ inBins
        boutLe :=
          fun ⟨_, _⟩ ⟨xEq, ⟨_, ⟨inBout, dEq, _⟩⟩⟩ =>
            xEq ▸ dEq ▸ inBout
      }
    
    def extOfIntCauseDistributesUnion
      (causeLeft causeRite: Cause Pair)
      (boundVars: List (ValVar Pair))
    :
      externalOfInternalCause (causeLeft.union causeRite) boundVars
        =
      Cause.union
        (externalOfInternalCause causeLeft boundVars)
        (externalOfInternalCause causeRite boundVars)
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
      -- externalOfInternalCause
      --   (Cause.arbUn causes)
      --   boundVars
      --   =
      -- Cause.arbUn
      --   (fun dX =>
      --     externalOfInternalCause
      --       (causes dX)
      --       (⟨dX, x⟩ :: boundVars))
      Cause.IsSubset
        (externalOfInternalCause
          (Cause.arbUn fun dX => (causes dX).exceptX x)
          boundVars)
        (Cause.arbUn fun dX =>
          externalOfInternalCause
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
      externalOfInternalCause (cause.exceptX x) boundVars
        ⊆
      externalOfInternalCause cause (⟨d, x⟩ :: boundVars)
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
      -- TODO maybe can be removed if presence in cause is enough
      -- (boundVars: List (ValVar Pair) := [])
    :
      Set (ValVar Pair)
    |
      theSet
        (vvIntIn: vvInt ∈ internalCycle)
        -- (isVarFree: IsVarFree vvInt.x boundVars)
      :
        extOfIntCycleBare
          internalCycle
          -- boundVars
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
        (externalOfInternalCause internalCause boundVars)
    
    inductive extOfIntCycleFull
      (internalCycle: Set (ValVar Pair))
    :
      Set (ValVar Pair)
    |
      interp
        (boundVars: List (ValVar Pair))
        (expr: Expr)
        (d: Pair)
        (allInapp: AllCausesInapp internalCycle boundVars expr d)
      :
        extOfIntCycleFull internalCycle ⟨
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
          internalCycle
          ⟨(vvInt.x, vvInt.d), uniDefList.theSet⟩
    
    def bareLeFull
      (internalCycle: Set (ValVar Pair))
    :
      extOfIntCycleBare internalCycle
        ⊆
      extOfIntCycleFull internalCycle
    |
      _, extOfIntCycleBare.theSet inIntCycle =>
        extOfIntCycleFull.theSet inIntCycle
    
    
    def OutInterp
      (boundVars: List (ValVar Pair))
      (d: Pair)
      (expr: Expr)
    :=
      Out
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (InterpEnc boundVars expr d)
        uniDefList.interpretation
    
    
    def inappExtBoundVar
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
        (extOfIntCycleFull internalCycle)
        externalCause
    :=
      let out :=
        Out.isComplete _ _ fun inw =>
        let isGetBound := Inw.toIsGetBound inw
        let isCause :=
          @Cause.minBoundVarsWeakCause
            x d boundVars isGetBound
        let isInapp :=
          allInapp
            (Cause.minBoundVars boundVars)
            (Cause.minBoundVarsSat boundVars)
            isCause
        open IsCauseInappExtended in
        match isInapp with
        | cinsFailsCycle inCins _ =>
          let ⟨_, ⟨_, isBound, _, isFree⟩⟩ := inCins
          isFree.nopeGetBound isBound
        | cinsFailsOut inCins _ =>
          let ⟨_, ⟨_, isBound, _, isFree⟩⟩ := inCins
          isFree.nopeGetBound isBound
        | binsFails inBins _ =>
          let ⟨_, ⟨_, isBound, _, isFree⟩⟩ := inBins
          isFree.nopeGetBound isBound
        | boutFails inBout _ =>
          let ⟨_, ⟨_, isBound, _, isFree⟩⟩ := inBout
          let ⟨_, _, isBoundOther⟩ := isBound
          isFree.nopeGetBound isBoundOther
    IsCauseInappExtended.cinsFailsOut inw out
    
    def inappExtFreeVar
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
        (extOfIntCycleFull internalCycle)
        externalCause
    :=
      open IsCauseInappExtended in
      if h:
        ∃ d, IsGetBound (boundVarsEncoding boundVars) x d
      then
        let ⟨d, isGetBound⟩ := h
        boutFails
          (notBound.toAll (fun _ => Not.dne) d )
          (Ins.isComplete _ _ (insGetBound isGetBound))
      else
        let isInapp :=
          allInapp
            (Cause.minBvAndVar boundVars x d)
            (Cause.minBvAndVarSat boundVars h d)
            (Cause.minBvAndVarWeakCause boundVars x d)
        match isInapp with
        | cinsFailsCycle ⟨eqX, vv, inCins, eq, isFree⟩ inCycle =>
          let eq: _ = (fromNat vv.x).pair vv.d := eq
          let ⟨eqVvD, eqVvX⟩ := Cause.inVarOfIsFree inCins isFree
          cinsFailsCycle
            inw
            (bareLeFull
              internalCycle
              (eqX ▸ eqVvD ▸ eqVvX ▸ eq ▸ inCycle))
        | cinsFailsOut ⟨eqX, vv, inCins, eq, isFree⟩ out =>
          let eq: _ = (fromNat vv.x).pair vv.d := eq
          let ⟨eqVvD, eqVvX⟩ := Cause.inVarOfIsFree inCins isFree
          cinsFailsOut inw (eqX ▸ eqVvD ▸ eqVvX ▸ eq ▸ out)
        | binsFails ⟨_, _, inBins, _, isFree⟩ _ =>
          Cause.minBvAndVarBinsNopeFree inBins isFree
        | boutFails ⟨_, _, inBout, _, isFree⟩ _ =>
          Cause.minBvAndVarBoutNopeFree inBout isFree
    
    
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
              let ⟨_d, isGetBound⟩ := hB
              let boundVarSat := boundVarsSat rfl isGetBound
              boundVarSat.ninBinsBout vv.d
            else
              False.elim
                ((boutOut hI.right hB).isSound
                  (Set3.defLePos _ (binsIns hI.left hB).isSound))
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
      | op pairSignature.Op.pair _ =>
        let ⟨_dLeft, _dRite, eq, isStrongLeft, isStrongRite⟩ :=
          isInternalCause.elimPairExpr isConsistent
      
        let ihL := isCauseToInsInterp
          isStrongLeft boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihR := isCauseToInsInterp
          isStrongRite boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        eq ▸ InsInterp.exprPair ihL ihR
      | un _ _ =>
        isInternalCause.elimUn.elim
          (fun isCauseLeft =>
            let ih := isCauseToInsInterp
              isCauseLeft boundVars boundVarsSat
              cinsIns binsIns boutOut
            
            InsInterp.exprUnLeft ih)
          (fun isCauseRite =>
            let ih := isCauseToInsInterp
              isCauseRite boundVars boundVarsSat
              cinsIns binsIns boutOut
            
            InsInterp.exprUnRite ih)
      | ir _ _ =>
        let ⟨isCauseLeft, isCauseRite⟩ := isInternalCause.elimIr
        
        let ihL := isCauseToInsInterp
          isCauseLeft boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihR := isCauseToInsInterp
          isCauseRite boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        InsInterp.exprIr ihL ihR
      | cpl _ =>
        -- let asdf := isInternalCause.elimCpl theInternalDefList
        -- InsInterp.exprCpl isInternalCause
        -- let asdf := inappExtOfAllInappInt
        sorry
      | ifThen _ _ =>
        let ⟨⟨_dC, isCauseCond⟩, isCauseBody⟩ :=
          isInternalCause.elimIfThen
        
        let ihCond := isCauseToInsInterp
          isCauseCond boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        let ihBody := isCauseToInsInterp
          isCauseBody boundVars boundVarsSat
          cinsIns binsIns boutOut
        
        InsInterp.exprIfThen ihCond ihBody
      | Un x _body =>
        let ⟨dX, isCauseWith⟩ :=
          isInternalCause.elimArbUn isConsistent
        
        let ih :=
          isCauseToInsInterp
            isCauseWith
            (⟨dX, x⟩ :: boundVars)
            boundVarsSat.withBoundSat
            (fun inCinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              cinsIns
                (Cause.inCinsOfInWithAndNotBound inCinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              binsIns
                (Cause.inBinsOfInWithAndNotBound inBinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBoutWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              boutOut
                (Cause.inBoutOfInWithAndNotBound inBoutWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
        
        InsInterp.arbUn dX ih
      | Ir x _body =>
        let isCauseWith := isInternalCause.elimArbIr isConsistent
        
        InsInterp.arbIr fun dX =>
          isCauseToInsInterp
            (isCauseWith dX)
            (⟨dX, x⟩ :: boundVars)
            boundVarsSat.withBoundSat
            (fun inCinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              cinsIns
                (Cause.inCinsOfInWithAndNotBound inCinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBinsWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              binsIns
                (Cause.inBinsOfInWithAndNotBound inBinsWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
            (fun inBoutWith notBound =>
              let xNeq := IsBound.Not.notBoundHeadNotEq notBound
              boutOut
                (Cause.inBoutOfInWithAndNotBound inBoutWith xNeq)
                (IsBound.Not.notBoundTail notBound xNeq))
    
    
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
        (extOfIntCycleFull internalCycle)
        externalCause
    :=
      match expr with
      | var x =>
        let boundOrFree :=
          isCause.hurrDurrElimGreat elimExternalVar
        boundOrFree.elim
          (inappExtBoundVar allInapp)
          (fun ⟨inw, notBound⟩ =>
            inappExtFreeVar allInapp inw notBound)
      |
        op pairSignature.Op.zero _ => sorry
      |
        op pairSignature.Op.pair _ => sorry
      |
        un left rite =>
        let inCinsLeftOrRite :=
          isCause.hurrDurrElim elimExternalUn
        
        inCinsLeftOrRite.elim
          (fun inCinsLeft =>
            let allInappLeft cause satBoundVars isCause :=
              allInapp cause satBoundVars (isCause.unLeft _)
            
            IsCauseInappExtended.cinsFailsCycle
              inCinsLeft
              (extOfIntCycleFull.interp
                boundVars left d allInappLeft))
          (fun inCinsRite =>
            let allInappRite cause satBoundVars isCause :=
              allInapp cause satBoundVars (isCause.unRite _)
            
            IsCauseInappExtended.cinsFailsCycle
              inCinsRite
              (extOfIntCycleFull.interp
                boundVars rite d allInappRite))
      |
        ir left rite =>
        let ⟨inCinsLeft, inCinsRite⟩ :=
          isCause.hurrDurrElim elimExternalIr
        
        if hL:
          AllCausesInapp internalCycle boundVars left d
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsLeft
            (extOfIntCycleFull.interp boundVars left d hL)
        else if hR:
          AllCausesInapp internalCycle boundVars rite d
        then
          IsCauseInappExtended.cinsFailsCycle
            inCinsRite
            (extOfIntCycleFull.interp boundVars rite d hR)
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
        let inBout :=
          (isCause.hurrDurrElimGreat elimExternalCpl).dne
        IsCauseInappExtended.boutFails
          inBout
          sorry
          -- (isCauseToInsInterp
          --   sorry
          --   boundVars
          --   sorry
          --   sorry
          --   sorry
          --   sorry)
      |
        ifThen _ _ => sorry
      |
        Un x body =>
        let ⟨dX, inCins⟩ :=
          isCause.hurrDurrElim elimExternalArbUn
        let allInapp cause satBoundVars isCause:
          IsCauseInappExtended
            pairSalgebra
            uniDefList.theExternalDefList.toDefList
            (extOfIntCycleBare internalCycle)
            (externalOfInternalCause
              cause
              (⟨dX, x⟩ :: boundVars))
        :=
          let isGetBound :=
            IsGetBound.InHead (fromNat.isNatEncoding x) dX _
          let causeSatBound := satBoundVars rfl isGetBound
          let causeLeWith := causeSatBound.leWithBound
          let whyIsTypeInferenceBroken:
            IsWeakCause pairSalgebra (cause.withBound x dX) d body
          :=
            isCause.toSuperCause causeLeWith
          let isInapp :=
            allInapp
              (cause.exceptX x)
              satBoundVars.satTailExceptHead
              whyIsTypeInferenceBroken.arbUn
          isInapp.toSuperCause
            (extOfIntExceptLeBoundHead cause dX x)
        IsCauseInappExtended.cinsFailsCycle
          inCins
          (extOfIntCycleFull.interp
            (⟨dX, x⟩ :: boundVars) body d allInapp)
      |
        Ir x body =>
          let inCins := isCause.hurrDurrElim elimExternalArbIr
        
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
                (allApplicable dX).val.exceptX x)
              (Cause.SatisfiesBoundVars.arbUn
                (fun dX => allApplicable dX)
                x
                (fun dX => (allApplicable dX).property.left))
              (@IsWeakCause.arbUnOf
                pairSignature
                pairSalgebra
                x
                d
                body
                (fun dX => (allApplicable dX).val)
                (fun dX =>
                  let satBoundVars :=
                    (allApplicable dX).property.left
                  let isGetBound :=
                    IsGetBound.InHead (fromNat.isNatEncoding x) dX _
                  let causeSatBound := satBoundVars rfl isGetBound
                  let causeLeWith := causeSatBound.leWithBound
                  let whyIsTypeInferenceBroken:
                    IsWeakCause
                      pairSalgebra
                      ((allApplicable dX).val.withBound x dX) d body
                  :=
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
            (externalOfInternalCause internalCause))
      
      (inCycle:
        ⟨dExt, xExt⟩ ∈ extOfIntCycleFull internalCycle)
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
        (extOfIntCycleFull internalCycle)
        externalCause
    :=
      open IsCauseInappExtended in
      byContradiction fun isApp =>
        match inCycle with
        | extOfIntCycleFull.interp _ _ d allCausesInapp =>
          isApp (inappExtOfAllInappInt allCausesInapp isCauseExternal)
        | @extOfIntCycleFull.theSet _ ⟨dInt, xInt⟩ inIntCycle =>
          -- A Lean bug, this breaks def equality:
          -- let ⟨xthDefEnc, isDlExpr⟩ :=
          let xthExpr := IsTheDefListExprPair.getNthExpr xInt
          
          let notXthNins
            p
            (neq: p ≠ xthExpr.expr)
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
              (P := externalCause.contextIns ⟨
                pair zero (pair xthExpr.expr dInt),
                uniDefList.interpretation,
              ⟩)
              fun inw =>
                let ⟨_xEnc, ⟨_inwNatXEnc, inw⟩⟩ := inwUnDomElim inw
                let ⟨inwL, inwR⟩ := inwPairElim inw
                let xEncEqX := inwBoundElim inwL
                let ⟨expr, ⟨inwFn, inwArg⟩⟩ := inwCallExprElim inwR
                let inwDl := inwCallElimBound inwArg rfl nat502Neq500
                let exprEq: expr = xthExpr.expr :=
                  byContradiction fun neq =>
                    notXthNins _ neq (xEncEqX ▸ inwDl)
                let ⟨_z, inw, inwZero⟩ := inwCallExprElim inwFn
                let zEq := inwZeroElim inwZero
                zEq ▸ exprEq ▸ inw
          
          let inCycleExt :=
            exprToEncoding.isInverse xthExpr.isNth.isExpr ▸
            extOfIntCycleFull.interp
              []
              xthExpr.expr.encodingToExpr
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
            (externalOfInternalCause internalCause))
    :
      Out
        pairSalgebra
        uniDefList.theExternalDefList.toDefList
        (Pair.pair x d)
        uniDefList.theSet
    :=
      Out.intro4
        (extOfIntCycleFull internalCycle)
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
              (externalOfInternalCause cause))
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
          cause dd xx inCins inCycle
        =>
          blockedContextIns
            (externalOfInternalCause cause)
            (show
              ⟨pair (fromNat xx) dd, uniDefList.theSet⟩
                ∈
              (externalOfInternalCause cause).contextIns
            from
              And.intro rfl ⟨_, inCins, rfl, nofun⟩)
            (extOfIntCycleBare.theSet inCycle))
        (fun cause dd xx inBins _ ihOut =>
          blockedBackgroundIns
            (externalOfInternalCause cause)
            (show
              ⟨pair (fromNat xx) dd, uniDefList.theSet⟩
                ∈
              (externalOfInternalCause cause).backgroundIns
            from
              And.intro rfl ⟨_, inBins, rfl, nofun⟩)
            ihOut)
        (fun cause dd xx inBout _ ihIns =>
          blockedBackgroundOut
            (externalOfInternalCause cause)
            (show
              ⟨pair (fromNat xx) dd, uniDefList.theSet⟩
                ∈
              (externalOfInternalCause cause).backgroundOut
            from
              And.intro rfl ⟨_, inBout, rfl, nofun⟩)
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
              (externalOfInternalCause cause))
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
            (externalOfInternalCause cause)
            (show
              _ ∈ (externalOfInternalCause _).contextIns
            from
              And.intro rfl ⟨_, inCins, rfl, nofun⟩)
            (extOfIntCycleBare.theSet inCycle))
        (fun cause _ _ inBins _ ihOut =>
          blockedBackgroundIns
            (externalOfInternalCause cause)
            (show
              _ ∈ (externalOfInternalCause _).backgroundIns
            from
              And.intro rfl ⟨_, inBins, rfl, nofun⟩)
            ihOut)
        (fun cause _ _ inBout _ ihIns =>
          blockedBackgroundOut
            (externalOfInternalCause cause)
            (show
              _ ∈ (externalOfInternalCause _).backgroundOut
            from
              And.intro rfl ⟨_, inBout, rfl, nofun⟩)
            ihIns)
        (fun _ _ => inEmptyCycleInternalToOutExternal)
    
  end uniSet3
end Pair
