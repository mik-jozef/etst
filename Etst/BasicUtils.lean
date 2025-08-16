/-
  Some basic things that should be in a standard library.
  Plus making `Classical.propDecidable` always available.
-/


noncomputable def Exists.unwrap {P: T → Prop} (ex: ∃ t, P t): { t // P t } :=
  Classical.indefiniteDescription P ex

-- EM go brr
noncomputable instance propDecidable (P: Prop): Decidable P :=
  Classical.propDecidable P


-- The square le/lt relation: `x ⊑ y` / `x ⊏ y`.
class SqLE (T : Type u) where le : T → T → Prop
class SqLT (T : Type u) where lt : T → T → Prop

infix:50 " ⊑ " => SqLE.le
infix:50 " ⊏ " => SqLT.lt
