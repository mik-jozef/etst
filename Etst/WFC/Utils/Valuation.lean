import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.Set3

namespace Etst

universe u
variable {D: Type u}
variable {lub: Valuation D}
variable {d: D}
variable {x: Nat}


namespace Valuation
  instance: Inhabited (Valuation D) := ⟨Valuation.undetermined⟩
  
  def LaneLe (v0 v1: Valuation D): Option Set3.Lane → Prop
  | .none => v0 ≤ v1
  | .some .defLane => ∀ x: Nat, (v0 x).defMem ⊆ (v1 x).defMem
  | .some .posLane => ∀ x: Nat, (v0 x).posMem ⊆ (v1 x).posMem
  
  
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
  
  
  -- The definite nonmembers of a valuation.
  def defNonMembers
    (v: Valuation D)
  :
    Nat → Set D
  :=
    compl ∘ Set3.posMem ∘ v
  
  -- The possible nonmembers of a valuation.
  def posNonMembers
    (v: Valuation D)
  :
    Nat → Set D
  :=
    compl ∘ Set3.defMem ∘ v
  
  -- The definite members of a valuation.
  def defMembers
    (v: Valuation D)
  :
    Nat → Set D
  :=
    Set3.defMem ∘ v
  
  -- The possible members of a valuation.
  def posMembers
    (v: Valuation D)
  :
    Nat → Set D
  :=
    Set3.posMem ∘ v
  
end Valuation
