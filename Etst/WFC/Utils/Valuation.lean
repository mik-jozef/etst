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
    (eq: x = y)
    {d: D}
  :
    val.update x d y = Set3.just d
  :=
    eq ▸ update_eq_bound val y d
  
  def update_eq_orig
    {val: Valuation D}
    (neq: x ≠ y)
    {d: D}
  :
    val.update x d y = val y
  :=
    if_neg neq.symm
  
  
  def in_update_bound_defMem
    {val: Valuation D}
    (eq: x = y)
    {d: D}
  :
    (val.update x d y).defMem d
  :=
    update_eq_bound_of_eq eq ▸ rfl
  
  def in_update_bound_posMem
    {val: Valuation D}
    (eq: x = y)
    {d: D}
  :
    (val.update x d y).posMem d
  :=
    update_eq_bound_of_eq eq ▸ rfl
  
  def in_update_free_defMem
    {val: Valuation D}
    (neq: x ≠ y)
    (eqAt: (val y).defMem d)
  :
    (val.update x dBound y).defMem d
  :=
    update_eq_orig neq ▸ eqAt
  
  def in_update_free_posMem
    {val: Valuation D}
    (neq: x ≠ y)
    (eqAt: (val y).posMem d)
  :
    (val.update x dBound y).posMem d
  :=
    update_eq_orig neq ▸ eqAt
  
  
  def eq_of_in_update_bound_defMem
    (inUpdated: (update val x dBound x).defMem d)
  :
    d = dBound
  := by
    rw [update_eq_bound val x dBound] at inUpdated
    exact inUpdated
  
  def eq_of_in_update_bound_posMem
    (inUpdated: (update val x dBound x).posMem d)
  :
    d = dBound
  := by
    rw [update_eq_bound val x dBound] at inUpdated
    exact inUpdated
  
  
  def in_orig_of_neq_defMem
    (inUpdated: (update val x dBound y).defMem d)
    (neq: x ≠ y)
  :
    (val y).defMem d
  :=
    (update_eq_orig (val := val) neq) ▸ inUpdated
  
  def in_orig_of_neq_posMem
    (inUpdated: (update val x dBound y).posMem d)
    (neq: x ≠ y)
  :
    (val y).posMem d
  :=
    (update_eq_orig (val := val) neq) ▸ inUpdated
  
  
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
  
  
  def ordStd.in_set_in_sup_defMem
    {set: Set (Valuation D)}
    (isLub: IsLUB set lub)
  :
    (∃ v ∈ set, d ∈ (v x).defMem) ↔ d ∈ (lub x).defMem
  :=
    let isLubAt := PartialOrder.isLUB_pointwise_isLUB isLub x
    Iff.intro
      (fun ⟨v, vInSet, dInV⟩ =>
        (Set3.ordStd.in_set_in_sup_defMem isLubAt).mp ⟨
            v x,
          ⟨v, vInSet, rfl⟩,
          dInV,
        ⟩)
      (fun dInSup =>
        let ⟨_s3, ⟨v, vInSet, (vxEq: v x = _s3)⟩, dInS3⟩ :=
          (Set3.ordStd.in_set_in_sup_defMem isLubAt).mpr dInSup
        ⟨v, vInSet, vxEq ▸ dInS3⟩)
  
  def ordStd.in_set_in_sup_posMem
    {set: Set (Valuation D)}
    (isLub: IsLUB set lub)
  :
    (∃ v ∈ set, d ∈ (v x).posMem) ↔ d ∈ (lub x).posMem
  :=
    let isLubAt := PartialOrder.isLUB_pointwise_isLUB isLub x
    Iff.intro
      (fun ⟨v, vInSet, dInV⟩ =>
        (Set3.ordStd.in_set_in_sup_posMem isLubAt).mp ⟨
          v x,
          ⟨v, vInSet, rfl⟩,
          dInV,
        ⟩)
      (fun dInSup =>
        let ⟨_s3, ⟨v, vInSet, (vxEq: v x = _s3)⟩, dInS3⟩ :=
          (Set3.ordStd.in_set_in_sup_posMem isLubAt).mpr dInSup
        ⟨v, vInSet, vxEq ▸ dInS3⟩)
  
  
  def ordApx.in_set_in_sup_defMem
    {set: Set (Valuation D)}
    (isLub: IsLUB set lub)
  :
    (∃ v ∈ set, d ∈ (v x).defMem) ↔ d ∈ (lub x).defMem
  :=
    let isLubAt := PartialOrder.isLUB_pointwise_isLUB isLub x
    Iff.intro
      (fun ⟨v, vInSet, dInV⟩ =>
        (Set3.ordApx.in_set_in_sup_defMem isLubAt).mp ⟨
          v x,
          ⟨v, vInSet, rfl⟩,
          dInV,
        ⟩)
      (fun dInSup =>
        let ⟨_s3, ⟨v, vInSet, (vxEq: v x = _s3)⟩, dInS3⟩ :=
          (Set3.ordApx.in_set_in_sup_defMem isLubAt).mpr dInSup
        ⟨v, vInSet, vxEq ▸ dInS3⟩)

  def ordApx.in_set_in_sup_posMem
    {set: Set (Valuation D)}
    (isLub: IsLUB set lub)
  :
    (∀ v ∈ set, d ∈ (v x).posMem) ↔ d ∈ (lub x).posMem
  :=
    let isLubAt := PartialOrder.isLUB_pointwise_isLUB isLub x
    Iff.intro
      (fun inAllSets =>
        let allIn _s3 s3In :=
          let ⟨v, vIn, (vxEq: v x = _s3)⟩ := s3In
          vxEq ▸ inAllSets v vIn
        (Set3.ordApx.in_set_in_sup_posMem isLubAt).mp allIn)
      (fun dInSup v vIn =>
        let inAllSets :=
          (Set3.ordApx.in_set_in_sup_posMem isLubAt).mpr dInSup
        inAllSets (v x) ⟨v, vIn, rfl⟩)
  
  
  -- The (definite) nonmembers of a valuation.
  def nonmembers
    (v: Valuation D)
  :
    Set (ValVar D)
  :=
    fun ⟨d, x⟩ => ¬ (v x).posMem d
  
  -- The possible nonmembers of a valuation.
  def posNonmembers
    (v: Valuation D)
  :
    Set (ValVar D)
  :=
    fun ⟨d, x⟩ => ¬ (v x).defMem d
  
  -- The (definite) members of a valuation.
  def members
    (v: Valuation D)
  :
    Set (ValVar D)
  :=
    fun ⟨d, x⟩ => (v x).defMem d
  
  -- The possible members of a valuation.
  def posMembers
    (v: Valuation D)
  :
    Set (ValVar D)
  :=
    fun ⟨d, x⟩ => (v x).posMem d
  
end Valuation
