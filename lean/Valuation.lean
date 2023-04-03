import Set3
import PartialOrder
import Pointwise

open Classical


@[reducible] def Valuation (Var: Type) (D: Type) := Sum Var Nat → Set3 D

namespace Valuation
  def empty: Valuation Var D := fun _ => Set3.empty
  
  def undetermined: Valuation Var D := fun _ => Set3.undetermined
  
  
  instance ord.standard (Var: Type) (D: Type)
  :
    PartialOrder (Valuation Var D)
  :=
    PartialOrder.pointwise (Sum Var Nat) (Set3.ord.standard D)
  
  instance ord.standard.st (Var: Type) (D: Type)
  :
    PartialOrderSt (Valuation Var D)
  where
    le        := (ord.standard Var D).le
    refl      := (ord.standard Var D).refl
    antisymm  := (ord.standard Var D).antisymm
    trans     := (ord.standard Var D).trans
    ltToLeNeq := (ord.standard Var D).ltToLeNeq
    leNeqToLt := (ord.standard Var D).leNeqToLt
  
  
  instance ord.approximation (Var: Type) (D: Type)
  :
    PartialOrder (Valuation Var D)
  :=
    PartialOrder.pointwise (Sum Var Nat) (Set3.ord.approximation D)
  
  instance ord.approximation.sq (Var: Type) (D: Type)
  :
    PartialOrderSq (Valuation Var D)
  where
    le        := (ord.approximation Var D).le
    refl      := (ord.approximation Var D).refl
    antisymm  := (ord.approximation Var D).antisymm
    trans     := (ord.approximation Var D).trans
    ltToLeNeq := (ord.approximation Var D).ltToLeNeq
    leNeqToLt := (ord.approximation Var D).leNeqToLt
  
  
  def empty.isLeast: isLeast (ord.standard Var D) Set.full empty :=
    And.intro trivial
      (fun _val _valInFull _x => And.intro
        (fun _t tInEmpty => False.elim tInEmpty)
        (fun _t tInEmpty => False.elim tInEmpty))
  
  def undetermined.isLeast:
    isLeast (ord.approximation Var D) Set.full undetermined
  :=
    And.intro trivial
      (fun _val _valInFull _x => And.intro
        (fun _t tInUndet => False.elim tInUndet)
        (fun _t _tInUndet => trivial))
  
  
  noncomputable def ord.standard.sup
    (ch: Chain (standard Var D))
  :
    Supremum (standard Var D) ch.val
  :=
    pointwiseSup
      (Set3.ord.standard D)
      (Set3.ord.standard.isChainComplete D)
      ch
  
  noncomputable def ord.approximation.sup
    (ch: Chain (approximation Var D))
  :
    Supremum (approximation Var D) ch.val
  :=
    pointwiseSup
      (Set3.ord.approximation D)
      (Set3.ord.approximation.isChainComplete D)
      ch
  
  
  def ord.standard.isChainComplete (Var: Type) (D: Type)
  :
    isChainComplete (Valuation.ord.standard Var D)
  :=
    fun ch => ⟨(sup ch).val, (sup ch).property⟩

  def ord.approximation.isChainComplete (Var: Type) (D: Type)
  :
    isChainComplete (Valuation.ord.approximation Var D)
  :=
    fun ch => ⟨(sup ch).val, (sup ch).property⟩
  
  
  def ord.standard.sup.emptyChain
    (ch: Chain (standard Var D))
    (chEmpty: ch.isEmpty)
    (chSup: Supremum (standard Var D) ch.val)
  :
    chSup.val = Valuation.empty
  :=
    isLeast.unique
      (standard Var D)
      Set.full
      chSup.val
      Valuation.empty
      (Chain.sup.empty.isLeast _ ch chEmpty chSup)
      empty.isLeast
  
  def ord.approximation.sup.emptyChain
    (ch: Chain (approximation Var D))
    (chEmpty: ch.isEmpty)
    (chSup: Supremum (approximation Var D) ch.val)
  :
    chSup.val = Valuation.undetermined
  :=
    isLeast.unique
      (approximation Var D)
      Set.full
      chSup.val
      Valuation.undetermined
      (Chain.sup.empty.isLeast _ ch chEmpty chSup)
      undetermined.isLeast
  
  
  noncomputable def update
    (val: Valuation Var D)
    (x: Sum Var Nat)
    (d: D)
  :
    Valuation Var D
  :=
    fun v =>
      if v = x then
        Set3.just d
      else
        val v
  
  def update.isMonotonic.standard
    (val0 val1: Valuation Var D)
    (le: val0 ≤ val1)
    (x: Sum Var Nat)
    (d: D)
  :
    val0.update x d ≤ val1.update x d
  :=
    fun xx =>
      if h: xx = x then
        And.intro
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
        
        And.intro
          (fun dd ddIn => val1Eq ▸ (le xx).left dd (val0Eq ▸ ddIn))
          (fun dd ddIn => val1Eq ▸ (le xx).right dd (val0Eq ▸ ddIn))
  
  def update.isMonotonic.approximation
    (val0 val1: Valuation Var D)
    (le: val0 ⊑ val1)
    (x: Sum Var Nat)
    (d: D)
  :
    val0.update x d ⊑ val1.update x d
  :=
    fun xx =>
      if h: xx = x then
        -- TODO move to a separate function and use it in .standard too.
        And.intro
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
        
        And.intro
          (fun dd ddIn => val1Eq ▸ (le xx).left dd (val0Eq ▸ ddIn))
          (fun dd ddIn => val0Eq ▸ (le xx).right dd (val1Eq ▸ ddIn))
  
  def ord.standard.inChain.inSup.defMem
    (ch: Chain (standard Var D))
    (s: ↑ch.val)
    (dInS: d ∈ (s.val x).defMem)
  :
    d ∈ ((ch.sup (standard Var D) cc).val x).defMem
  :=
    let atCh := pointwiseSup.atChain (Set3.ord.standard D) ch x
    
    let supAtCh := atCh.sup
      (Set3.ord.standard D)
      (Set3.ord.standard.isChainComplete D)
    
    let supEq := pointwiseSup.eqAt
      (Set3.ord.standard D)
      (Set3.ord.standard.isChainComplete D)
      ch x
    
    let sAtCh: ↑atCh.val := ⟨s.val x,
      pointwiseSup.inCh.atChain (Set3.ord.standard D) ch rfl⟩
    
    let dInSupAtCh: d ∈ supAtCh.val.defMem :=
      Set3.ord.standard.inChain.inSup.defMem atCh sAtCh d dInS
    
    supEq ▸ dInSupAtCh
  
  def ord.standard.ninChain.ninSup.defMem
    (ch: Chain (ord.standard Var D))
    (x: Sum Var Nat)
    (d: D)
    (allNin: ∀ (s: ↑ch.val), d ∉ (s.val x).defMem)
  :
    d ∉ (
      (ch.sup (ord.standard Var D) (ord.standard.isChainComplete Var D)).val x
    ).defMem
  :=
    fun din =>
      let atCh := pointwiseSup.atChain (Set3.ord.standard D) ch x
      
      let supAtCh := atCh.sup
        (Set3.ord.standard D)
        (Set3.ord.standard.isChainComplete D)
      
      let supEq := pointwiseSup.eqAt
        (Set3.ord.standard D)
        (Set3.ord.standard.isChainComplete D)
        ch x
      
      let allNinAt (s: ↑atCh.val) (dInS: d ∈ s.val.defMem) :=
        let val := choiceEx s.property
        let nin := allNin val
        nin (val.property ▸ dInS)
      
      let dInSupAtCh: d ∈ supAtCh.val.defMem := supEq ▸ din
      let dNinSupAtCh: d ∉ supAtCh.val.defMem :=
        Set3.ord.standard.ninChain.ninSup.defMem atCh d allNinAt
      
      dNinSupAtCh dInSupAtCh
  
  def ord.standard.ninChain.ninSup.posMem
    (ch: Chain (ord.standard Var D))
    (x: Sum Var Nat)
    (d: D)
    (allNin: ∀ (s: ↑ch.val), d ∉ (s.val x).posMem)
  :
    d ∉ (
      (ch.sup (ord.standard Var D) (ord.standard.isChainComplete Var D)).val x
    ).posMem
  :=
    fun din =>
      let atCh := pointwiseSup.atChain (Set3.ord.standard D) ch x
      
      let supAtCh := atCh.sup
        (Set3.ord.standard D)
        (Set3.ord.standard.isChainComplete D)
      
      let supEq := pointwiseSup.eqAt
        (Set3.ord.standard D)
        (Set3.ord.standard.isChainComplete D)
        ch x
      
      let allNinAt (s: ↑atCh.val) (dInS: d ∈ s.val.posMem) :=
        let val := choiceEx s.property
        let nin := allNin val
        nin (val.property ▸ dInS)
      
      let dInSupAtCh: d ∈ supAtCh.val.posMem := supEq ▸ din
      let dNinSupAtCh: d ∉ supAtCh.val.posMem :=
        Set3.ord.standard.ninChain.ninSup.posMem atCh d allNinAt
      
      dNinSupAtCh dInSupAtCh
  
  def ord.approximation.ninChain.ninSup.defMem
    (ch: Chain (ord.approximation Var D))
    (x: Sum Var Nat)
    (d: D)
    (allNin: ∀ (s: ↑ch.val), d ∉ (s.val x).defMem)
  :
    d ∉ (
      (ch.sup (ord.approximation Var D)
        (ord.approximation.isChainComplete Var D)).val x
    ).defMem
  :=
    fun din =>
      let atCh := pointwiseSup.atChain (Set3.ord.approximation D) ch x
      
      let supAtCh := atCh.sup
        (Set3.ord.approximation D)
        (Set3.ord.approximation.isChainComplete D)
      
      let supEq := pointwiseSup.eqAt
        (Set3.ord.approximation D)
        (Set3.ord.approximation.isChainComplete D)
        ch x
      
      let allNinAt (s: ↑atCh.val) (dInS: d ∈ s.val.defMem) :=
        let val := choiceEx s.property
        let nin := allNin val
        nin (val.property ▸ dInS)
      
      let dInSupAtCh: d ∈ supAtCh.val.defMem := supEq ▸ din
      let dNinSupAtCh: d ∉ supAtCh.val.defMem :=
        Set3.ord.approximation.ninChain.ninSup.defMem atCh d allNinAt
      
      dNinSupAtCh dInSupAtCh
  
  def ord.approximation.ninChain.ninSup.posMem
    (ch: Chain (ord.approximation Var D))
    (s: ↑ch.val)
    (dNin: d ∉ (s.val x).posMem)
  :
    d ∉ (
      (ch.sup (ord.approximation Var D)
        (ord.approximation.isChainComplete Var D)).val x
    ).posMem
  :=
    fun din =>
      let atCh := pointwiseSup.atChain (Set3.ord.approximation D) ch x
      
      let sAtX: ↑atCh.val := ⟨s.val x, ⟨s, rfl⟩⟩
      
      let supAtCh := atCh.sup
        (Set3.ord.approximation D)
        (Set3.ord.approximation.isChainComplete D)
      
      let supEq := pointwiseSup.eqAt
        (Set3.ord.approximation D)
        (Set3.ord.approximation.isChainComplete D)
        ch x
      
      let dInSupAtCh: d ∈ supAtCh.val.posMem := supEq ▸ din
      let dNinSupAtCh: d ∉ supAtCh.val.posMem :=
        Set3.ord.approximation.ninChain.ninSup.posMem atCh sAtX d dNin
      
      dNinSupAtCh dInSupAtCh
  
end Valuation
