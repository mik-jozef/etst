import Utils.Ordinal


structure Tuple (T: Type u) where
  length: Ordinal
  elements: ↑length → T

instance: Membership T (Tuple T) where
  mem := fun (t: T) (tuple: Tuple T) => ∃ n: ↑tuple.length, tuple.elements n = t

instance Tuple.coe: Coe (Tuple T) (Set T) where
  coe tuple := fun t: T => t ∈ tuple

namespace Tuple
  def empty: Tuple T := {
    length := 0
    elements := fun n => False.elim (Ordinal.not_lt_zero n n.property)
  }
  
  def Len (T: Type u) (length: Ordinal) := { t: Tuple T // t.length = length }
  
  def zeroth (tuple: Tuple T) (hasZeroth: 0 < tuple.length): T :=
    tuple.elements ⟨0, hasZeroth⟩
  
  -- Dear world, please, index things right.
  def first (tuple: Tuple T) (hasFirst: 1 < tuple.length): T :=
    tuple.elements ⟨1, hasFirst⟩
  
  noncomputable def last
    (tuple: Tuple T)
    (notLimit: ¬ tuple.length.IsActualLimit)
  :
    T
  :=
    let i := Ordinal.pred tuple.length
    
    tuple.elements ⟨i, Ordinal.predLtOfNotLimit notLimit⟩
  
end Tuple
