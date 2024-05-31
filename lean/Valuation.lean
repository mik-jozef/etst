import Set3
import Pointwise


def Valuation D := Nat → Set3 D

namespace Valuation
  def empty: Valuation D := fun _ => Set3.empty
  
  def undetermined: Valuation D := fun _ => Set3.undetermined
  
  
  instance ord.approximation (D: Type u):
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ord.approximation D)
  
  instance ord.standard (D: Type u)
  :
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ord.standard D)
  
  instance Set3.sqle (D: Type u): SqLE (Valuation D) where
    le := (ord.approximation D).le
  
  instance Set3.sqlt (D: Type u): SqLT (Valuation D) where
    lt := (ord.approximation D).lt
  
  
  def empty.isLeast: iIsLeast (ord.standard D).le Set.full empty := {
    isMember := trivial
    isLeMember :=
      (fun _val _valInFull _x => Set3.LeStd.intro
        (fun _t tInEmpty => False.elim tInEmpty)
        (fun _t tInEmpty => False.elim tInEmpty))
  }
  
  def undetermined.isLeast:
    iIsLeast (ord.approximation D).le Set.full undetermined
  := {
    isMember := trivial
    isLeMember :=
      (fun _val _valInFull _x => Set3.LeApx.intro
        (fun _t tInUndet => False.elim tInUndet)
        (fun _t _tInUndet => trivial))
  }
  
  noncomputable def ord.standard.sup
    {D: Type u}
    (ch: Chain (standard D))
  :
    Supremum (standard D) ch
  :=
    ch.pointwiseSup (Set3.ord.standard.isChainComplete D)
  
  noncomputable def ord.approximation.sup
    (ch: Chain (approximation D))
  :
    Supremum (approximation D) ch
  :=
    ch.pointwiseSup (Set3.ord.approximation.isChainComplete D)
  
  
  def ord.standard.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ord.standard D)
  := {
    supExists := fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  def ord.approximation.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ord.approximation D)
  := {
    supExists := fun ch => ⟨(sup ch).val, (sup ch).property⟩
  }
  
  
  def ord.standard.sup.emptyChain
    (ch: Chain (standard D))
    (chEmpty: ch.IsEmpty)
    (chSup: Supremum (standard D) ch)
  :
    chSup.val = Valuation.empty
  :=
    iIsLeast.isUnique
      (standard D)
      (Chain.sup.empty.isLeast ch chEmpty chSup)
      empty.isLeast
  
  def ord.approximation.sup.emptyChain
    (ch: Chain (approximation D))
    (chEmpty: ch.IsEmpty)
    (chSup: Supremum (approximation D) ch)
  :
    chSup.val = Valuation.undetermined
  :=
    iIsLeast.isUnique
      (approximation D)
      (Chain.sup.empty.isLeast ch chEmpty chSup)
      undetermined.isLeast
  
  
  def update
    (val: Valuation D)
    (x: Nat)
    (d: D)
  :
    Valuation D
  :=
    fun v =>
      if v = x then
        Set3.just d
      else
        val v
  
  def update.eqBound
    (val: Valuation D)
    (x: Nat)
    (d: D)
  :
    val.update x d x = Set3.just d
  :=
    by unfold update; exact if_pos rfl
  
  def update.eqBoundOfEq
    (val: Valuation D)
    {xBound xReq: Nat}
    (xEq: xBound = xReq)
    (d: D)
  :
    val.update xBound d xReq = Set3.just d
  :=
    xEq ▸ update.eqBound val xReq d
  
  def update.eqOrig
    (val: Valuation D)
    {xBound xReq: Nat}
    (xNeq: xBound ≠ xReq)
    (d: D)
  :
    val.update xBound d xReq = val xReq
  :=
    by unfold update; exact if_neg xNeq.symm
  
  def update.inEq.defMem
    (val: Valuation D)
    (x: Nat)
    (d: D)
  :
    (val.update x d x).defMem d
  :=
    eqBound val x d ▸ rfl
  
  def update.inEq.posMem
    (val: Valuation D)
    (x: Nat)
    (d: D)
  :
    (val.update x d x).posMem d
  :=
    eqBound val x d ▸ rfl
  
  def update.inDef.eq
    (inUpdated: (update val x dBound x).defMem d)
  :
    d = dBound
  :=
    let eq:
      Set.just dBound d
        =
      (update val x dBound x).defMem d
    :=
      by unfold update; rw [if_pos rfl]; unfold Set3.just; exact rfl
    
    show Set.just dBound d from eq ▸ inUpdated
  
  def update.inPos.eq
    (inUpdated: (update val x dBound x).posMem d)
  :
    d = dBound
  :=
    let eq:
      Set.just dBound d
        =
      (update val x dBound x).posMem d
    :=
      by unfold update; rw [if_pos rfl]; unfold Set3.just; exact rfl
    
    show Set.just dBound d from eq ▸ inUpdated
  
  def update.inNeq.defMem
    (val: Valuation D)
    {xBound xReq: Nat}
    (xNeq: xBound ≠ xReq)
    {d: D}
    (dIn: d ∈ (val xReq).defMem)
  :
    (val.update xBound dBound xReq).defMem d
  :=
    by unfold Valuation.update; rw [if_neg xNeq.symm]; exact dIn

  def update.inNeq.posMem
    (val: Valuation D)
    {xBound xReq: Nat}
    (xNeq: xBound ≠ xReq)
    {d: D}
    (dIn: d ∈ (val xReq).posMem)
  :
    (val.update xBound dBound xReq).posMem d
  :=
    by unfold Valuation.update; rw [if_neg xNeq.symm]; exact dIn
  
  def update.inNeqElim.defMem
    {val: Valuation D}
    (inBound: (val.update xBound dBound xReq).defMem d)
    (neq: xBound ≠ xReq)
  :
    (val xReq).defMem d
  :=
    let eq:
      (val.update xBound dBound xReq).defMem d
        =
      (val xReq).defMem d
    :=
      by unfold update; rw [if_neg neq.symm]
    
    eq ▸ inBound
  
  def update.inNeqElim.posMem
    {val: Valuation D}
    (inBound: (val.update xBound dBound xReq).posMem d)
    (neq: xBound ≠ xReq)
  :
    (val xReq).posMem d
  :=
    let eq:
      (val.update xBound dBound xReq).posMem d
        =
      (val xReq).posMem d
    :=
      by unfold update; rw [if_neg neq.symm]
    
    eq ▸ inBound
  
  
  def update.isMonotonic.standard
    (val0 val1: Valuation D)
    (le: val0 ≤ val1)
    (x: Nat)
    (d: D)
  :
    val0.update x d ≤ val1.update x d
  :=
    fun xx =>
      if h: xx = x then
        Set3.LeStd.intro
          (fun _ ddIn =>
            let val0Eq: val0.update x d xx = Set3.just d := dif_pos h
            let val1Eq: val1.update x d xx = Set3.just d := dif_pos h
            
            let valEq: val0.update x d xx = val1.update x d xx :=
              val0Eq.trans val1Eq.symm
            
            valEq ▸ ddIn)
          -- This function is identical to the above, but has a different type.
          -- is there an easy way not to repeat oneself?
          (fun _ ddIn =>
            let val0Eq: val0.update x d xx = Set3.just d := dif_pos h
            let val1Eq: val1.update x d xx = Set3.just d := dif_pos h
            
            let valEq: val0.update x d xx = val1.update x d xx :=
              val0Eq.trans val1Eq.symm
            
            valEq ▸ ddIn)
      else
        let val0Eq: val0.update x d xx = val0 xx := dif_neg h
        let val1Eq: val1.update x d xx = val1 xx := dif_neg h
        
        Set3.LeStd.intro
          (fun _dd ddIn => val1Eq ▸ (le xx).defLe (val0Eq ▸ ddIn))
          (fun _dd ddIn => val1Eq ▸ (le xx).posLe (val0Eq ▸ ddIn))
  
  def update.isMonotonic.approximation
    (val0 val1: Valuation D)
    (le: val0 ⊑ val1)
    (x: Nat)
    (d: D)
  :
    val0.update x d ⊑ val1.update x d
  :=
    fun xx =>
      if h: xx = x then
        Set3.LeApx.intro
          (fun _ ddIn =>
            let val0Eq: val0.update x d xx = Set3.just d := dif_pos h
            let val1Eq: val1.update x d xx = Set3.just d := dif_pos h
            
            let valEq: val0.update x d xx = val1.update x d xx :=
              val0Eq.trans val1Eq.symm
            
            valEq ▸ ddIn)
          -- This function is identical to the above, but has a different type.
          -- is there an easy way not to repeat oneself?
          (fun _ ddIn =>
            let val0Eq: val0.update x d xx = Set3.just d := dif_pos h
            let val1Eq: val1.update x d xx = Set3.just d := dif_pos h
            
            let valEq: val0.update x d xx = val1.update x d xx :=
              val0Eq.trans val1Eq.symm
            
            valEq ▸ ddIn)
      else
        let val0Eq: val0.update x d xx = val0 xx := dif_neg h
        let val1Eq: val1.update x d xx = val1 xx := dif_neg h
        
        Set3.LeApx.intro
          (fun _dd ddIn => val1Eq ▸ (le xx).defLe (val0Eq ▸ ddIn))
          (fun _dd ddIn => val0Eq ▸ (le xx).posLe (val1Eq ▸ ddIn))
  
  def ord.standard.inSet.inSup.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {valuation: set}
    {x: Nat}
    (dInS: d ∈ (valuation.val x).defMem)
  :
    d ∈ (sup.val x).defMem
  :=
    (sup.property.isMember _ x).defLe dInS
  
  def ord.standard.inSet.inSup.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {valuation: set}
    {x: Nat}
    (dInS: d ∈ (valuation.val x).posMem)
  :
    d ∈ (sup.val x).posMem
  :=
    (sup.property.isMember _ x).posLe dInS
  
  def ord.standard.ninSet.ninSup.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    {d: D}
    (allNin: ∀ (s: ↑set), d ∉ (s.val x).defMem)
  :
    d ∉ (sup.val x).defMem
  :=
    let supAt := Set.pointwiseSup.supAt sup x
    let withoutDAtX := Set3.withoutDef (sup.val x) d
    
    let dIsUB: IsUpperBound _ (set.pointwiseAt x) withoutDAtX :=
      fun triset =>
        let valOfTriset := triset.property.unwrap
        
        Set3.LeStd.intro
          (fun dd ddIn =>
            if h: dd = d then
              False.elim
                (allNin valOfTriset (valOfTriset.property ▸ h ▸ ddIn))
            else
              Set3.without.DefMem.intro
                (ord.standard.inSet.inSup.defMem
                  sup (valOfTriset.property ▸ ddIn))
                h)
          (fun _dd ddIn => ord.standard.inSet.inSup.posMem
            sup (valOfTriset.property ▸ ddIn))
    
    let supAtLe := supAt.leUB dIsUB
    
    let ninSupAt: d ∉ supAt.val.defMem :=
      fun dIn =>
        let dInWithoutD := supAtLe.defLe dIn
        dInWithoutD.neq rfl
    
    (Set.pointwiseSup.eqAt sup supAt) ▸ ninSupAt
  
  
  def ord.standard.inSup.inSomeSet.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    (dInSup: d ∈ (sup.val x).defMem)
  :
    ∃ valuation: set, d ∈ (valuation.val x).defMem
  :=
    byContradiction fun nex =>
      let allNin: ∀ v: set, d ∉ (v.val x).defMem :=
        nex.toAll fun _ => id
      
      let dNinSup := ninSet.ninSup.defMem sup allNin
      
      dNinSup dInSup
  
  def ord.standard.ninSet.ninSup.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    {d: D}
    (allNin: ∀ (s: set), d ∉ (s.val x).posMem)
  :
    d ∉ (sup.val x).posMem
  :=
    let withoutDAtX := Set3.without (sup.val x) d
    let withoutD xx :=
      if xx = x then withoutDAtX else sup.val xx
    
    fun dIn =>
      let supWithoutDAtX:
        Supremum (standard D) set
      := ⟨
        withoutD,
        {
          isMember := fun s3 xx =>
            let s3Le := sup.property.isMember s3 xx
            
            if h: xx = x then
              let eq: withoutD xx = withoutDAtX := if_pos h
              eq ▸ Set3.LeStd.intro
                (fun dd ddIn =>
                  Set3.without.DefMem.intro
                    (show dd ∈ (sup.val x).defMem from
                      h ▸ s3Le.defLe ddIn)
                    fun dEq => allNin s3
                      (h ▸ dEq ▸ ((s3.val xx).defLePos ddIn)))
                (fun dd ddIn =>
                  Set3.without.PosMem.intro
                    (show dd ∈ (sup.val x).posMem from
                      h ▸ s3Le.posLe ddIn)
                    (fun dEq => allNin s3 (h ▸ dEq ▸ ddIn)))
            else
              let eq: withoutD xx = sup.val xx := if_neg h
              
              eq ▸ s3Le
          isLeMember :=
            fun _v vIsUB =>
              let withoutDLe: withoutD ≤ sup.val :=
                fun xx =>
                  if h: xx = x then
                    let eq: withoutD xx = withoutDAtX := if_pos h
                    eq ▸ h ▸ Set3.without.leStd _
                  else
                    let eq: withoutD xx = sup.val xx := if_neg h
                    eq ▸ Preorder.le_refl _
              
              withoutDLe.trans (sup.property.isLeMember vIsUB)
        }
      ⟩
      
      let dNin: d ∉ (supWithoutDAtX.val x).posMem :=
        let eq: supWithoutDAtX.val x = withoutDAtX := if_pos rfl
        eq ▸ Set3.without.ninPos (sup.val x) d
      
      dNin ((Supremum.eq sup supWithoutDAtX) ▸ dIn)
  
  def ord.standard.inSup.inSomeSet.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    (dInSup: d ∈ (sup.val x).posMem)
  :
    ∃ valuation: set, d ∈ (valuation.val x).posMem
  :=
    byContradiction fun nex =>
      let allNin: ∀ v: set, d ∉ (v.val x).posMem :=
        nex.toAll fun _ => id
      
      let dNinSup := ninSet.ninSup.posMem sup allNin
      
      dNinSup dInSup
  
  def ord.approximation.ninSet.ninSup.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    {d: D}
    (allNin: ∀ (s: ↑set), d ∉ (s.val x).defMem)
  :
    d ∉ (sup.val x).defMem
  :=
    let withoutDAtX := Set3.withoutDef (sup.val x) d
    let withoutD: Valuation D := fun xx =>
      if xx = x then withoutDAtX else sup.val xx
    
    fun dIn =>
      let supWithoutDAtX:
        Supremum (approximation D) set
      := ⟨
        withoutD,
        {
          isMember := fun s3 xx =>
            let s3Le := sup.property.isMember s3 xx
            
            if h: xx = x then
              let eq: withoutD xx = withoutDAtX := if_pos h
              eq ▸ Set3.LeApx.intro
                (fun dd ddIn =>
                  Set3.without.DefMem.intro
                    (show dd ∈ (sup.val x).defMem from
                      h ▸ s3Le.defLe ddIn)
                    fun dEq => allNin s3 (h ▸ dEq ▸ ddIn))
                (fun _dd ddIn =>
                  let inPosX := (sup.property.isMember s3 x).posLe ddIn
                  h ▸ inPosX)
            else
              let eq: withoutD xx = sup.val xx := if_neg h
              
              eq ▸ s3Le
          isLeMember :=
            fun _v vIsUB =>
              let withoutDLe: withoutD ⊑ sup.val :=
                fun xx =>
                  if h: xx = x then
                    let eq: withoutD xx = withoutDAtX := if_pos h
                    eq ▸ h ▸ Set3.withoutDef.leApx _
                  else
                    let eq: withoutD xx = sup.val xx := if_neg h
                    eq ▸ @Preorder.le_refl _ (approximation D).toPreorder _ _
              
              @le_trans _ (approximation D).toPreorder
                _ _ _ withoutDLe (sup.property.isLeMember vIsUB)
        }
      ⟩
      
      let dNin: d ∉ (supWithoutDAtX.val x).defMem :=
        let eq: supWithoutDAtX.val x = withoutDAtX := if_pos rfl
        eq ▸ Set3.withoutDef.ninDef (sup.val x) d
      
      dNin ((Supremum.eq sup supWithoutDAtX) ▸ dIn)
  
  def ord.approximation.inSup.inSomeSet.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    {d: D}
    (dInSup: d ∈ (sup.val x).defMem)
  :
    ∃ valuation: set, d ∈ (valuation.val x).defMem
  :=
    byContradiction fun nex =>
      let allNin: ∀ v: set, d ∉ (v.val x).defMem :=
        nex.toAll fun _ => id
      
      let dNinSup := ninSet.ninSup.defMem sup allNin
      
      dNinSup dInSup
  
  def ord.approximation.ninSet.ninSup.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {valuation: set}
    {x: Nat}
    {d: D}
    (dNinS: d ∉ (valuation.val x).posMem)
  :
    d ∉ (sup.val x).posMem
  :=
    let supLePos := (sup.property.isMember valuation x).posLe
    
    fun dIn => dNinS (supLePos dIn)
  
  def ord.approximation.inSup.inAllSets.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    {d: D}
    (dInSup: d ∈ (sup.val x).posMem)
  :
    ∀ valuation: set, d ∈ (valuation.val x).posMem
  :=
    byContradiction fun nall =>
      let exNin: ∃ v: set, d ∉ (v.val x).posMem :=
        nall.toEx fun _ => id
      
      let dNinSup := ninSet.ninSup.posMem sup exNin.unwrap.property
      
      dNinSup dInSup
  
end Valuation
