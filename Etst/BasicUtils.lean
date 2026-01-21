/-
  Some basic things that should be in a standard library.
  And maybe even are, but I didn't find them (or thought I
  could improve them a little).
  Plus making `Classical.propDecidable` always available.
-/

import Mathlib.Tactic.TypeStar


noncomputable def Exists.unwrap
  {T} {P: T → Prop} (ex: ∃ t, P t)
:
  { t // P t }
:=
  Classical.indefiniteDescription P ex

-- EM go brr
noncomputable instance propDecidable (P: Prop): Decidable P :=
  Classical.propDecidable P

def byContradiction {P: Prop} := @Classical.byContradiction P


-- The square le/lt relation: `x ⊑ y` / `x ⊏ y`.
class SqLE.{u} (T : Type u) where le : T → T → Prop
class SqLT.{u} (T : Type u) where lt : T → T → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt


def Not.dne {P: Prop} (h: ¬¬P): P :=
  (Classical.em P).elim id (absurd · h)

def Not.toAll {T} {P: T → Prop} {ImpliedByNotP: T → Sort*}
  (nEx: ¬(∃ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∀ t: T, ImpliedByNotP t
:=
  fun t =>  nptImpl t (Classical.byContradiction fun nnpt => nEx ⟨t, nnpt.dne⟩)

def Not.toEx {T} {P ImpliedByNotP: T → Prop}
  (nAll: ¬(∀ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∃ t: T, ImpliedByNotP t
:=
  byContradiction fun nEx =>
    nAll (fun t => byContradiction fun npt => nEx ⟨t, nptImpl t npt⟩)


def Iff.nmp {P Q: Prop} (h: P ↔ Q) : ¬P → ¬Q :=
  fun np q => np (h.mpr q)

def Iff.nmpr {P Q: Prop} (h: P ↔ Q) : ¬Q → ¬P :=
  fun qq p => qq (h.mp p)


abbrev List.Index {T} (l: List T) := Fin l.length

def List.Index.map
  {A} {list: List A}
  (i: list.Index)
  {B} (f: A → B)
:
  (list.map f).Index
:= ⟨
  i.val,
  by rw [List.length_map]; exact i.isLt
⟩

def List.Index.unmap
  {A} {list: List A}
  {B} {f: A → B}
  (i: (list.map f).Index)
:
  list.Index
:= ⟨
  i.val,
  by rw [←List.length_map f]; exact i.isLt
⟩

noncomputable def List.Mem.index 
  {T} {l: List T} {t}
:
  t ∈ l → ∃ i: List.Index l, l[i] = t
|  .head _ => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
| .tail _ memTail =>
  let ⟨i, eq⟩ := index memTail
  ⟨⟨.succ i, Nat.succ_lt_succ i.isLt⟩, eq⟩

def List.Index.indexedTail
  {T} {P: T → Sort*} {h t}
  (indexedFn: (i: (h :: t).Index) → P (h :: t)[i])
:
  (i: t.Index) → P t[i]
:=
  fun ⟨i, ilt⟩ => indexedFn ⟨i.succ, Nat.succ_lt_succ ilt⟩

def List.Mem.toOr
  {T} {t head: T} {rest}
  (mem: List.Mem t (head :: rest))
:
  t = head ∨ t ∈ rest
:=
  match mem with
  | Mem.head a => Or.inl rfl
  | Mem.tail a b => Or.inr b

def List.Mem.elim
  {T} {t head: T} {rest}
  (mem: List.Mem t (head :: rest))
  {C} (left: t = head → C)
  (rite: t ∈ rest → C)
:
  C
:=
  mem.toOr.elim left rite

def List.length_le_append_rite
  {T} (l r: List T)
:
  l.length ≤ (l ++ r).length
:=
  match l with
  | [] => Nat.zero_le _
  | _ :: tail =>
    Nat.succ_le_succ (List.length_le_append_rite tail r)


def String.append_inj_left
  {a0 a1 b0 b1: String}
  (eq: a0 ++ b0 = a1 ++ b1)
  (eqLength: a0.length = a1.length)
:
  a0 = a1
:= by
  apply String.toList_injective
  apply List.append_inj_left _ eqLength
  exact b0.toList
  exact b1.toList
  rw [←String.toList_append, ←String.toList_append]
  exact congr rfl eq

def String.append_inj_rite
  {a0 a1 b0 b1: String}
  (eq: a0 ++ b0 = a1 ++ b1)
  (eqLength: a0.length = a1.length)
:
  b0 = b1
:= by
  apply String.toList_injective
  apply List.append_inj_right _ eqLength
  rw [←String.toList_append, ←String.toList_append]
  exact congr rfl eq
