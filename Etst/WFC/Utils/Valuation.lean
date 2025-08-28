import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.Set3

namespace Etst


namespace Valuation
  instance: Inhabited (Valuation D) := ⟨Valuation.undetermined⟩

  def update_eq_bound
    (val: Valuation D)
    (x: Nat)
    (d: D)
  :
    val.update x d x = Set3.just d
  :=
    if_pos rfl
  
  def update_eq_bound_of_eq
    {val: Valuation D}
    {xBound xReq: Nat}
    (xEq: xBound = xReq)
    {d: D}
  :
    val.update xBound d xReq = Set3.just d
  :=
    xEq ▸ update_eq_bound val xReq d
  
  def update_eq_orig
    {val: Valuation D}
    {xBound xReq: Nat}
    (xNeq: xBound ≠ xReq)
    {d: D}
  :
    val.update xBound d xReq = val xReq
  :=
    if_neg xNeq.symm
  
  
  def update_mono_std_defMem
    {val0 val1: Valuation D}
    (le: (x: Nat) → (val0 x).defMem ≤ (val1 x).defMem)
    (xU: Nat)
    (d: D)
    (x: Nat)
  :
    (val0.update xU d x).defMem ≤ (val1.update xU d x).defMem
  :=
    fun _ ddIn =>
      if h: xU = x then
        update_eq_bound_of_eq h ▸
        update_eq_bound_of_eq h ▸
        ddIn
      else
        let inVal0 := update_eq_orig (val := val0) h ▸ ddIn
        update_eq_orig h ▸ le x inVal0

  def update_mono_std_posMem
    {val0 val1: Valuation D}
    (le: (x: Nat) → (val0 x).posMem ≤ (val1 x).posMem)
    (xU: Nat)
    (d: D)
    (x: Nat)
  :
    (val0.update xU d x).posMem ≤ (val1.update xU d x).posMem
  :=
    fun _ ddIn =>
      if h: xU = x then
        update_eq_bound_of_eq h ▸
        update_eq_bound_of_eq h ▸
        ddIn
      else
        let inVal0 := update_eq_orig (val := val0) h ▸ ddIn
        update_eq_orig h ▸ le x inVal0

  def update_mono_std
    {val0 val1: Valuation D}
    (le: val0 ≤ val1)
    (xU: Nat)
    (d: D)
  :
    val0.update xU d ≤ val1.update xU d
  :=
    fun x => {
      defLe := update_mono_std_defMem (fun x => (le x).defLe) xU d x
      posLe := update_mono_std_posMem (fun x => (le x).posLe) xU d x
    }
  
  
  def update_mono_apx_defMem
    {val0 val1: Valuation D}
    (le: (x: Nat) → (val0 x).defMem ≤ (val1 x).defMem)
    (xU: Nat)
    (d: D)
    (x: Nat)
  :
    (val0.update xU d x).defMem ≤ (val1.update xU d x).defMem
  :=
    fun _ ddIn =>
      if h: xU = x then
        update_eq_bound_of_eq h ▸
        update_eq_bound_of_eq h ▸
        ddIn
      else
        let inVal0 := update_eq_orig (val := val0) h ▸ ddIn
        update_eq_orig h ▸ le x inVal0
  
  def update_mono_apx_posMem
    {val0 val1: Valuation D}
    (le: (x: Nat) → (val0 x).posMem ≤ (val1 x).posMem)
    (xU: Nat)
    (d: D)
    (x: Nat)
  :
    (val0.update xU d x).posMem ≤ (val1.update xU d x).posMem
  :=
    fun _ ddIn =>
      if h: xU = x then
        update_eq_bound_of_eq h ▸
        update_eq_bound_of_eq h ▸
        ddIn
      else
        let inVal0 := update_eq_orig (val := val0) h ▸ ddIn
        update_eq_orig h ▸ le x inVal0

  def update_mono_apx
    {val0 val1: Valuation D}
    (le: val0 ⊑ val1)
    (x: Nat)
    (d: D)
  :
    val0.update x d ⊑ val1.update x d
  :=
    fun xx => {
      defLe := update_mono_apx_defMem (fun x => (le x).defLe) x d xx
      posLe := update_mono_apx_posMem (fun x => (le x).posLe) x d xx
    }
  
  
  def ordStdLattice D: CompleteLattice (Valuation D) :=
    CompleteLattice.pointwise Nat (Set3.ordStdLattice D)
  
  
  def ordStd.in_some_set_of_in_sup_defMem
    {set: Set (Valuation D)}
    (isLub: IsLUB set lub)
    (dInSup: d ∈ (lub x).defMem)
  :
    ∃ v ∈ set, d ∈ (v x).defMem
  :=
    let isLubAt := PartialOrder.isLUB_pointwise_isLUB isLub x
    let ⟨s3, ⟨v, vInSet, (vxEq: v x = s3)⟩, dInS3⟩ :=
      Set3.ordStd.in_some_set_of_in_sup_defMem isLubAt dInSup
    ⟨v, vInSet, vxEq ▸ dInS3⟩

  def ordStd.in_some_set_of_in_sup_posMem
    {set: Set (Valuation D)}
    (isLub: IsLUB set lub)
    (dInSup: d ∈ (lub x).posMem)
  :
    ∃ v ∈ set, d ∈ (v x).posMem
  :=
    let isLubAt := PartialOrder.isLUB_pointwise_isLUB isLub x
    let ⟨s3, ⟨v, vInSet, (vxEq: v x = s3)⟩, dInS3⟩ :=
      Set3.ordStd.in_some_set_of_in_sup_posMem isLubAt dInSup
    ⟨v, vInSet, vxEq ▸ dInS3⟩

end Valuation
