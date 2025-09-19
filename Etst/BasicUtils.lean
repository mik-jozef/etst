/-
  Some basic things that should be in a standard library.
  And maybe even are, but I didn't find them (or thought I
  could improve them a little).
  Plus making `Classical.propDecidable` always available.
-/

import Mathlib.Tactic.TypeStar


noncomputable def Exists.unwrap {P: T → Prop} (ex: ∃ t, P t): { t // P t } :=
  Classical.indefiniteDescription P ex

-- EM go brr
noncomputable instance propDecidable (P: Prop): Decidable P :=
  Classical.propDecidable P

def byContradiction {P: Prop} := @Classical.byContradiction P


-- The square le/lt relation: `x ⊑ y` / `x ⊏ y`.
class SqLE (T : Type u) where le : T → T → Prop
class SqLT (T : Type u) where lt : T → T → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt


def Not.dne {P: Prop} (h: ¬¬P): P :=
  (Classical.em P).elim id (absurd · h)

def Not.toAll {P: T → Prop} {ImpliedByNotP: T → Sort*}
  (nEx: ¬(∃ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∀ t: T, ImpliedByNotP t
:=
  fun t =>  nptImpl t (Classical.byContradiction fun nnpt => nEx ⟨t, nnpt.dne⟩)

def Not.toEx {P ImpliedByNotP: T → Prop}
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


abbrev List.Index (l: List T) := Fin l.length

noncomputable def List.Mem.index 
  {l: List T}
:
  t ∈ l → ∃ i: List.Index l, l[i] = t
|  .head _ => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
| .tail _ memTail =>
  let ⟨i, eq⟩ := index memTail
  ⟨⟨.succ i, Nat.succ_lt_succ i.isLt⟩, eq⟩

def List.Mem.toOr
  {t head: T}
  (mem: List.Mem t (head :: rest))
:
  t = head ∨ t ∈ rest
:=
  match mem with
  | Mem.head a => Or.inl rfl
  | Mem.tail a b => Or.inr b

def List.Mem.elim
  {t head: T}
  (mem: List.Mem t (head :: rest))
  (left: t = head → C)
  (rite: t ∈ rest → C)
:
  C
:=
  mem.toOr.elim left rite

def List.get?_append_left
  (lt: i < List.length l)
:
  l[i]? = (l ++ r)[i]?
:=
  match i, l with
  | 0, cons _ _ => rfl
  | n+1, cons _ t =>
    show t[n]? = (t ++ r)[n]? from
      List.get?_append_left (Nat.lt_of_succ_lt_succ lt)
