/-
  Defines PartialOrder and PartialOrderSq, along with notation
  for the latter.
-/

-- The square less-equal relation: `x ⊑ y`.
class SqLE (α : Type u) where
  le : α → α → Prop

-- The square less-equal relation: `x ⊏ y`.
class SqLT (α : Type u) where
  lt : α → α → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt

class PartialOrder (T: Type) extends LE T, LT T where
  refl (t: T): t ≤ t
  antisymm (a b: T): a ≤ b  →  b ≤ a  →  a = b
  trans (a b c: T): a ≤ b  →  b ≤ c  →  a ≤ c
  
  lt (a b: T) := a ≤ b  ∧  ¬ a = b
  ltIffLeNotEq (a b: T): a < b  ↔  a ≤ b ∧ ¬ a = b

-- Can I combine PartialOrder with PartialOrderSq into one definition?
class PartialOrderSq (T: Type) extends SqLE T, SqLT T where
  refl (t: T): t ⊑ t
  antisymm (a b: T): a ⊑ b  →  b ⊑ a  →  a = b
  trans (a b c: T): a ⊑ b  →  b ⊑ c  →  a ⊑ c
  
  lt (a b: T) := a ⊑ b  ∧  ¬ a = b
  ltIffLeNotEq (a b: T): a ⊏ b  ↔  a ⊑ b ∧ ¬ a = b
