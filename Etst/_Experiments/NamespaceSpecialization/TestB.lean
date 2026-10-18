import Etst._Experiments.NamespaceSpecialization.NamespaceSpecialization

/-! Used by `Test.lean`, together with `TestA.lean`, which is not imported here. -/

namespace Foo
  namespace {m} (List (Fin m)) in
  def fromB (_: List (Fin m)): Nat := 2
end Foo
