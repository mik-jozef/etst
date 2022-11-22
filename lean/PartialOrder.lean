/-
  Defines PartialOrder and PartialOrderSq, along with notation
  for the latter.
-/

open Classical

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
  
  ltToLeNeq {a b: T}: a < b → a ≤ b ∧ ¬ a = b
  leNeqToLt {a b: T}: a ≤ b ∧ ¬ a = b → a < b

namespace PartialOrder
  def irefl [PartialOrder T] (a: T): a ≮ a :=
    fun aa: a < a => (ltToLeNeq aa).right rfl
  
  def antisymmLt [PartialOrder T] (a b: T): a < b  →  b < a  →  a = b :=
    fun ab ba =>
      antisymm a b
        (ltToLeNeq ab).left
        (ltToLeNeq ba).left
  
  def transLt [PartialOrder T] (a b c: T): a < b  →  b < c  →  a < c :=
    fun ab bc =>
      let aLeC: a ≤ c :=
        (trans a b c
          (ltToLeNeq ab).left
          (ltToLeNeq bc).left)
      let aNeqC: a ≠ c :=
        fun eqAC =>
          let cb: c < b := eqAC ▸ ab
          let eqCB: c = b := antisymmLt c b cb bc
          let cc: c < c := eqCB ▸ cb
          (ltToLeNeq cc).right rfl
      leNeqToLt (And.intro aLeC aNeqC)
  
  def leToLtOrEq [PartialOrder T] {a b: T} (ab: a ≤ b): a < b ∨ a = b :=
    if h: a = b then
          Or.inr h
        else
          Or.inl (leNeqToLt (And.intro ab h))
  
  def ltOrEqToLe [PartialOrder T] {a b: T} (ab: a < b ∨ a = b): a ≤ b :=
      ab.elim
        (fun lt => (ltToLeNeq lt).left)
        (fun eq => eq ▸ (refl a))
  
  
  @[reducible] def Option.le (_: PartialOrder T): Option T → Option T → Prop
    | none, none => True
    | none, some _ => False
    | some _, none => True
    | some t0, some t1 => t0 ≤ t1
  
  instance option (ord: PartialOrder T): PartialOrder (Option T) where
    le := Option.le ord
    
    refl
      | none => trivial
      | some t => ord.refl t
    
    antisymm
      | none, none, _, _ => rfl
      | none, some _, nope, _ => False.elim nope
      | some _, none, _, nope => False.elim nope
      | some a, some b, ab, ba => congr rfl (ord.antisymm a b ab ba)
    
    trans
      | none, _, none, _, _ => trivial
      | some _, _, none, _, _ => trivial
      | none, none, some _, _, nope => False.elim nope
      | none, some _, some _, nope, _ => False.elim nope
      | some a, some b, some c, ab, bc => ord.trans a b c ab bc
    
    lt := fun (a b) => Option.le ord a b  ∧  ¬ a = b
    ltToLeNeq := id
    leNeqToLt := id
  
  def option.noneGe [ord: PartialOrder T] (t: Option T): ord.option.le t none :=
    -- TODO: your theorem prover shouldn't need a switch.
    match t with
      | none => trivial
      | some _ => trivial
  
  def option.lt.toOpt [ord: PartialOrder T] {t0 t1: T} (lt: t0 < t1):
    ord.option.lt t0 t1
  :=
    let and := ord.ltToLeNeq lt
    And.intro and.left (fun n => Option.noConfusion n and.right)
  
  def option.lt.fromOpt [ord: PartialOrder T] {t0 t1: T} (lt: ord.option.lt t0 t1):
    t0 < t1
  :=
    let le: ord.option.le t0 t1 ∧ some t0 ≠ some t1 :=
      ord.option.ltToLeNeq lt
    let le: t0 ≤ t1 ∧ t0 ≠ t1 :=
      And.intro le.left (fun eq => le.right (congr rfl eq))
    ord.leNeqToLt le
end PartialOrder


-- Can I combine PartialOrder with PartialOrderSq into one definition?
class PartialOrderSq (T: Type) extends SqLE T, SqLT T where
  refl (t: T): t ⊑ t
  antisymm (a b: T): a ⊑ b  →  b ⊑ a  →  a = b
  trans (a b c: T): a ⊑ b  →  b ⊑ c  →  a ⊑ c
  
  lt (a b: T) := a ⊑ b  ∧  ¬ a = b
  ltToLeNeq {a b: T}: a ⊏ b  →  a ⊑ b ∧ ¬ a = b
  leNeqToLt {a b: T}: a ⊑ b ∧ ¬ a = b  →  a ⊏ b

namespace PartialOrderSq
  def irefl [PartialOrderSq T] (a: T): ¬ SqLT.lt a a :=
    fun aa: a ⊏ a => (ltToLeNeq aa).right rfl
  
  def antisymmLt [PartialOrderSq T] (a b: T): a ⊏ b  →  b ⊏ a  →  a = b :=
    fun ab ba =>
      antisymm a b
        (ltToLeNeq ab).left
        (ltToLeNeq ba).left
  
  def transLt [PartialOrderSq T] (a b c: T): a ⊏ b  →  b ⊏ c  →  a ⊏ c :=
    fun ab bc =>
      let aLeC: a ⊑ c :=
        (trans a b c
          (ltToLeNeq ab).left
          (ltToLeNeq bc).left)
      let aNeqC: a ≠ c :=
        fun eqAC =>
          let cb: c ⊏ b := eqAC ▸ ab
          let eqCB: c = b := antisymmLt c b cb bc
          let cc: c ⊏ c := eqCB ▸ cb
          (ltToLeNeq cc).right rfl
      leNeqToLt (And.intro aLeC aNeqC)
end PartialOrderSq
