/-
  Contains utility definitions related to valuatinos.
-/

import WFC.Ch2_Valuation

namespace Valuation
  
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
  
  
  def ord.standard.allNinSet.ninSup.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    {d: D}
    (allNin: ∀ (s: set), d ∉ (s.val x).defMem)
  :
    d ∉ (sup.val x).defMem
  :=
    let supAt := Set.pointwiseSup.supAt sup x
    let withoutDAtX := Set3.withoutDef (sup.val x) d
    
    let dIsUB:
      IsUpperBound
        (Set3.ord.standard D)
        (set.pointwiseAt x)
        withoutDAtX
    :=
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
  
  def ord.standard.allNinSet.ninSup.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    {d: D}
    (allNin: ∀ (s: set), d ∉ (s.val x).posMem)
  :
    d ∉ (sup.val x).posMem
  :=
    let supAt := Set.pointwiseSup.supAt sup x
    let withoutDAtX := Set3.without (sup.val x) d
    
    let dIsUB:
      IsUpperBound
        (Set3.ord.standard D)
        (set.pointwiseAt x)
        withoutDAtX
    :=
      fun triset =>
        let valOfTriset := triset.property.unwrap
        
        Set3.LeStd.intro
          (fun dd ddIn =>
            if h: dd = d then
              False.elim
                (allNin
                  valOfTriset
                  (valOfTriset.property ▸ h ▸ Set3.defLePos _ ddIn))
            else
              Set3.without.DefMem.intro
                (ord.standard.inSet.inSup.defMem
                  sup (valOfTriset.property ▸ ddIn))
                h)
          (fun dd ddIn =>
            if h: dd = d then
              False.elim
                (allNin
                  valOfTriset
                  (valOfTriset.property ▸ h ▸ ddIn))
            else
              Set3.without.PosMem.intro
                (ord.standard.inSet.inSup.posMem
                  sup (valOfTriset.property ▸ ddIn))
                h)
    
    let supAtLe := supAt.leUB dIsUB
    
    let ninSupAt: d ∉ supAt.val.posMem :=
      fun dIn =>
        let dInWithoutD := supAtLe.posLe dIn
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
      
      let dNinSup := allNinSet.ninSup.defMem sup allNin
      
      dNinSup dInSup
  
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
      
      let dNinSup := allNinSet.ninSup.posMem sup allNin
      
      dNinSup dInSup
  
  def ord.standard.ninSup.allNinSet.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    (dInSup: d ∉ (sup.val x).defMem)
  :
    ∀ valuation: set, d ∉ (valuation.val x).defMem
  :=
    byContradiction fun nall =>
      let ⟨_, dIn⟩ := nall.toEx fun _ => Not.dne
      
      dInSup (ord.standard.inSet.inSup.defMem sup dIn)
  
  def ord.standard.ninSup.allNinSet.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (standard D) set)
    {x: Nat}
    (dInSup: d ∉ (sup.val x).posMem)
  :
    ∀ valuation: set, d ∉ (valuation.val x).posMem
  :=
    byContradiction fun nall =>
      let ⟨_, dIn⟩ := nall.toEx fun _ => Not.dne
      
      dInSup (ord.standard.inSet.inSup.posMem sup dIn)
  
  
  def ord.approximation.inSet.inSup.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {valuation: set}
    {x: Nat}
    (dInS: d ∈ (valuation.val x).defMem)
  :
    d ∈ (sup.val x).defMem
  :=
    (sup.property.isMember _ x).defLe dInS
  
  def ord.approximation.allInSet.inSup.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    (allIn: ∀ (v: set), d ∈ (v.val x).posMem)
  :
    d ∈ (sup.val x).posMem
  :=
    Set3.ord.approximation.allInSet.inSup.posMem
      (Set.pointwiseSup.supAt sup x)
      (fun (sAt: set.pointwiseAt x) =>
        let ⟨s, sAtEq⟩ := sAt.property.unwrap
        sAtEq.symm ▸ allIn s)
  
  
  def ord.approximation.allNinSet.ninSup.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    {d: D}
    (allNin: ∀ (s: set), d ∉ (s.val x).defMem)
  :
    d ∉ (sup.val x).defMem
  :=
    Set3.ord.approximation.allNinSet.ninSup.defMem
      (Set.pointwiseSup.supAt sup x)
      (fun (sAt: set.pointwiseAt x) =>
        let ⟨s, sAtEq⟩ := sAt.property.unwrap
        sAtEq.symm ▸ allNin s)
  
  def ord.approximation.ninSet.ninSup.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {valuation: set}
    {x: Nat}
    (dNinS: d ∉ (valuation.val x).posMem)
  :
    d ∉ (sup.val x).posMem
  :=
    let supLePos := (sup.property.isMember valuation x).posLe
    
    fun dIn => dNinS (supLePos dIn)
  
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
      
      let dNinSup := allNinSet.ninSup.defMem sup allNin
      
      dNinSup dInSup
  
  def ord.approximation.inSup.allInSet.posMem
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
  
  def ord.approximation.ninSup.allNinSet.defMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    (dNinSup: d ∉ (sup.val x).defMem)
  :
    ∀ valuation: set, d ∉ (valuation.val x).defMem
  :=
    byContradiction fun nall =>
      let ⟨_, dIn⟩ := nall.toEx fun _ => Not.dne
      
      dNinSup (ord.approximation.inSet.inSup.defMem sup dIn)
  
  def ord.approximation.ninSup.ninSomeSet.posMem
    {set: Set (Valuation D)}
    (sup: Supremum (approximation D) set)
    {x: Nat}
    (dNinSup: d ∉ (sup.val x).posMem)
  :
    ∃ v: set, d ∉ (v.val x).posMem
  :=
    byContradiction fun nex =>
      let allIn: ∀ v: set, d ∈ (v.val x).posMem :=
        nex.toAll fun _ => Not.dne
      
      dNinSup (ord.approximation.allInSet.inSup.posMem sup allIn)
  
end Valuation
