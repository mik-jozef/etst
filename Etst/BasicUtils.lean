/-
  Some basic things that should be in a standard library.
  And maybe even are, but I didn't find them (or thought I
  could improve them a little).
  Plus making `Classical.propDecidable` always available.
-/
module
import Mathlib.Tactic.TypeStar


macro "exposed " cmd:command : command =>
  `(@[expose] public section
    $cmd:command
    end)

public noncomputable def Exists.unwrap
  {T} {P: T → Prop} (ex: ∃ t, P t)
:
  { t // P t }
:=
  Classical.indefiniteDescription P ex

-- EM go brr
public noncomputable instance (priority := low) propDecidable
  (P: Prop)
:
  Decidable P
:=
  Classical.propDecidable P

public theorem byContradiction {P: Prop}: ¬¬ P → P :=
  @Classical.byContradiction P


-- The square le/lt relation: `x ⊑ y` / `x ⊏ y`.
public class SqLE.{u} (T : Type u) where le : T → T → Prop
public class SqLT.{u} (T : Type u) where lt : T → T → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt


public theorem Not.dne {P: Prop} (h: ¬¬P): P :=
  (Classical.em P).elim id (absurd · h)

public def Not.toAll {T} {P: T → Prop} {ImpliedByNotP: T → Sort*}
  (nEx: ¬(∃ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∀ t: T, ImpliedByNotP t
:=
  fun t =>  nptImpl t (Classical.byContradiction fun nnpt => nEx ⟨t, nnpt.dne⟩)

public theorem Not.toEx {T} {P ImpliedByNotP: T → Prop}
  (nAll: ¬(∀ t: T, P t))
  (nptImpl: ∀ t, ¬P t → ImpliedByNotP t)
:
  ∃ t: T, ImpliedByNotP t
:=
  byContradiction fun nEx =>
    nAll (fun t => byContradiction fun npt => nEx ⟨t, nptImpl t npt⟩)


public theorem Iff.nmp {P Q: Prop} (h: P ↔ Q) : ¬P → ¬Q :=
  fun np q => np (h.mpr q)

public theorem Iff.nmpr {P Q: Prop} (h: P ↔ Q) : ¬Q → ¬P :=
  fun qq p => qq (h.mp p)


public abbrev List.Index {T} (l: List T) := Fin l.length

exposed def List.Index.map
  {A} {list: List A}
  (i: list.Index)
  {B} (f: A → B)
:
  (list.map f).Index
:= ⟨
  i.val,
  by rw [List.length_map]; exact i.isLt
⟩

exposed def List.Index.unmap
  {A} {list: List A}
  {B} {f: A → B}
  (i: (list.map f).Index)
:
  list.Index
:= ⟨
  i.val,
  by rw [←List.length_map f]; exact i.isLt
⟩

public theorem List.Mem.index 
  {T} {l: List T} {t}
:
  t ∈ l → ∃ i: List.Index l, l[i] = t
|  .head _ => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
| .tail _ memTail =>
  let ⟨i, eq⟩ := index memTail
  ⟨⟨.succ i, Nat.succ_lt_succ i.isLt⟩, eq⟩

exposed def List.Index.indexedTail
  {T} {P: T → Sort*} {h t}
  (indexedFn: (i: (h :: t).Index) → P (h :: t)[i])
:
  (i: t.Index) → P t[i]
:=
  fun ⟨i, ilt⟩ => indexedFn ⟨i.succ, Nat.succ_lt_succ ilt⟩

public theorem List.Mem.toOr
  {T} {t head: T} {rest}
  (mem: List.Mem t (head :: rest))
:
  t = head ∨ t ∈ rest
:=
  match mem with
  | Mem.head a => Or.inl rfl
  | Mem.tail a b => Or.inr b

public theorem List.Mem.elim
  {T} {t head: T} {rest}
  (mem: List.Mem t (head :: rest))
  {C: Prop}
  (left: t = head → C)
  (rite: t ∈ rest → C)
:
  C
:=
  mem.toOr.elim left rite

public theorem List.length_le_append_rite
  {T} (l r: List T)
:
  l.length ≤ (l ++ r).length
:=
  match l with
  | [] => Nat.zero_le _
  | _ :: tail =>
    Nat.succ_le_succ (List.length_le_append_rite tail r)


public theorem String.append_inj_left
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

public theorem String.append_inj_rite
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
