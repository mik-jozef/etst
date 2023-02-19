/-
  Defines PartialOrder and PartialOrderSq, along with notation
  for the latter.
-/

open Classical

notation:50 lhs:51 " ≰ " rhs:51 => ¬ LE.le lhs rhs
notation:50 lhs:51 " ≮ " rhs:51 => ¬ LT.lt lhs rhs

class PartialOrder (T: Type) where
  le : T → T → Prop
  refl (t: T): le t t
  antisymm (a b: T): le a b  →  le b a  →  a = b
  trans (a b c: T): le a b  →  le b c  →  le a c
  
  lt (a b: T) := le a b  ∧  ¬ a = b
  
  ltToLeNeq {a b: T}: lt a b → le a b ∧ ¬ a = b
  leNeqToLt {a b: T}: le a b ∧ ¬ a = b → lt a b

infix:50 " .≤ " => PartialOrder.le
infix:50 " .< " => PartialOrder.lt

namespace PartialOrder
  def irefl [PartialOrder T] (a: T): ¬ lt a a :=
    fun aa: lt a a => (ltToLeNeq aa).right rfl
  
  def antisymmLt [PartialOrder T] (a b: T): lt a b  →  lt b a  →  a = b :=
    fun ab ba =>
      antisymm a b
        (ltToLeNeq ab).left
        (ltToLeNeq ba).left
  
  def antisymmLt.p {p: Prop} [PartialOrder T] {a b: T}: lt a b  →  lt b a  →  p :=
    fun ab ba =>
      let eqAB := antisymmLt a b ab ba
      False.elim (irefl a (eqAB ▸ ab))
  
  def transLt [PartialOrder T] (a b c: T): lt a b  →  lt b c  →  lt a c :=
    fun ab bc =>
      let aLeC: le a c :=
        (trans a b c
          (ltToLeNeq ab).left
          (ltToLeNeq bc).left)
      let aNeqC: a ≠ c :=
        fun eqAC =>
          let cb: lt c b := eqAC ▸ ab
          let eqCB: c = b := antisymmLt c b cb bc
          let cc: lt c c := eqCB ▸ cb
          (ltToLeNeq cc).right rfl
      leNeqToLt (And.intro aLeC aNeqC)
  
  def leToLtOrEq [PartialOrder T] {a b: T} (ab: le a b): lt a b ∨ a = b :=
    if h: a = b then
          Or.inr h
        else
          Or.inl (leNeqToLt (And.intro ab h))
  
  def ltOrEqToLe [PartialOrder T] {a b: T} (ab: lt a b ∨ a = b): le a b :=
      ab.elim
        (fun lt => (ltToLeNeq lt).left)
        (fun eq => eq ▸ (refl a))
  
  def ltToLe [PartialOrder T] {a b: T} (ab: lt a b): le a b := (ltToLeNeq ab).left
  def eqToLe [PartialOrder T] {a b: T} (eq: a = b): le a b := eq ▸ refl a
  
  def ltNotGe [PartialOrder T] {a b: T} (ab: lt a b): ¬ le b a :=
    fun leBA =>
      (leToLtOrEq leBA).elim
        (fun ba => antisymmLt.p ab ba)
        (fun eq => irefl a (eq ▸ ab))
  
  @[reducible] def Option.le (ord: PartialOrder T): Option T → Option T → Prop
    | none, none => True
    | none, some _ => False
    | some _, none => True
    | some t0, some t1 => ord.le t0 t1
  
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
  
  def option.lt.toOpt [ord: PartialOrder T] {t0 t1: T} (ltT: lt t0 t1):
    ord.option.lt t0 t1
  :=
    let and := ord.ltToLeNeq ltT
    And.intro and.left (fun n => Option.noConfusion n and.right)
  
  def option.lt.fromOpt
    [ord: PartialOrder T]
    {t0 t1: T}
    (ltT: ord.option.lt t0 t1)
  :
    lt t0 t1
  :=
    let leT: ord.option.le t0 t1 ∧ some t0 ≠ some t1 :=
      ord.option.ltToLeNeq ltT
    let leT: le t0 t1 ∧ t0 ≠ t1 :=
      And.intro leT.left (fun eq => leT.right (congr rfl eq))
    ord.leNeqToLt leT
end PartialOrder

class PartialOrderSt (T: Type) extends PartialOrder T, LE T, LT T where

-- The square less-equal relation: `x ⊑ y`.
class SqLE (α : Type u) where
  le : α → α → Prop

-- The square less-equal relation: `x ⊏ y`.
class SqLT (α : Type u) where
  lt : α → α → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt

class PartialOrderSq (T: Type) extends PartialOrder T, SqLE T, SqLT T where

def PartialOrderSq.le.fromPO
  [ord: PartialOrderSq T]
  (ab: ord.toPartialOrder.le a b):
  a ⊑ b
:=
  ab
