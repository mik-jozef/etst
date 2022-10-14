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

notation:50 lhs:51 " ≰ " rhs:51 => ¬ LE.le lhs rhs
notation:50 lhs:51 " ≮ " rhs:51 => ¬ LT.lt lhs rhs

class PartialOrder (T: Type) extends LE T, LT T where
  refl (t: T): t ≤ t
  antisymm (a b: T): a ≤ b  →  b ≤ a  →  a = b
  trans (a b c: T): a ≤ b  →  b ≤ c  →  a ≤ c
  
  lt (a b: T) := a ≤ b  ∧  ¬ a = b
  ltIffLeNotEq (a b: T): a < b  ↔  a ≤ b ∧ ¬ a = b

namespace PartialOrder
  def irefl [PartialOrder T] (a: T): a ≮ a :=
    fun aa: a < a => ((ltIffLeNotEq a a).mp aa).right rfl
  
  def antisymmLt [PartialOrder T] (a b: T): a < b  →  b < a  →  a = b :=
    fun ab ba =>
      antisymm a b
        ((ltIffLeNotEq a b).mp ab).left
        ((ltIffLeNotEq b a).mp ba).left
  
  def transLt [PartialOrder T] (a b c: T): a < b  →  b < c  →  a < c :=
    fun ab bc =>
      let aLeC: a ≤ c :=
        (trans a b c
          ((ltIffLeNotEq a b).mp ab).left
          ((ltIffLeNotEq b c).mp bc).left)
      let aNeqC: a ≠ c :=
        fun eqAC =>
          let cb: c < b := eqAC ▸ ab
          let eqCB: c = b := antisymmLt c b cb bc
          let cc: c < c := eqCB ▸ cb
          ((ltIffLeNotEq c c).mp cc).right rfl
      (ltIffLeNotEq a c).mpr (And.intro aLeC aNeqC)
end PartialOrder


-- Can I combine PartialOrder with PartialOrderSq into one definition?
class PartialOrderSq (T: Type) extends SqLE T, SqLT T where
  refl (t: T): t ⊑ t
  antisymm (a b: T): a ⊑ b  →  b ⊑ a  →  a = b
  trans (a b c: T): a ⊑ b  →  b ⊑ c  →  a ⊑ c
  
  lt (a b: T) := a ⊑ b  ∧  ¬ a = b
  ltIffLeNotEq (a b: T): a ⊏ b  ↔  a ⊑ b ∧ ¬ a = b

namespace PartialOrderSq
  def irefl [PartialOrderSq T] (a: T): ¬ SqLT.lt a a :=
    fun aa: a ⊏ a => ((ltIffLeNotEq a a).mp aa).right rfl
  
  def antisymmLt [PartialOrderSq T] (a b: T): a ⊏ b  →  b ⊏ a  →  a = b :=
    fun ab ba =>
      antisymm a b
        ((ltIffLeNotEq a b).mp ab).left
        ((ltIffLeNotEq b a).mp ba).left
  
  def transLt [PartialOrderSq T] (a b c: T): a ⊏ b  →  b ⊏ c  →  a ⊏ c :=
    fun ab bc =>
      let aLeC: a ⊑ c :=
        (trans a b c
          ((ltIffLeNotEq a b).mp ab).left
          ((ltIffLeNotEq b c).mp bc).left)
      let aNeqC: a ≠ c :=
        fun eqAC =>
          let cb: c ⊏ b := eqAC ▸ ab
          let eqCB: c = b := antisymmLt c b cb bc
          let cc: c ⊏ c := eqCB ▸ cb
          ((ltIffLeNotEq c c).mp cc).right rfl
      (ltIffLeNotEq a c).mpr (And.intro aLeC aNeqC)
end PartialOrderSq
