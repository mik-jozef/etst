import Etst._Experiments.NamespaceSpecialization.NamespaceSpecialization

/-! Used by `Test.lean`, together with `TestB.lean`, which does not import this file. -/

namespace {n: Nat} (List (Fin n)) in
def fromA (_: List (Fin n)): Nat := 1
