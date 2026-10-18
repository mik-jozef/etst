import Etst._Experiments.NamespaceSpecialization.NamespaceSpecialization
import Etst._Experiments.NamespaceSpecialization.TestA
import Etst._Experiments.NamespaceSpecialization.TestB

/-! Tests for specialized namespaces. -/

-- Modules that do not import each other agree on the namespace, like with ordinary namespaces.
example: [(0: Fin 2)].fromA + [(0: Fin 2)].fromB = 3 := rfl
example: List.«(List (Fin x₁))».fromA [(0: Fin 2)] = 1 := rfl
example: List.«(List (Fin x₁))».fromB [(0: Fin 2)] = 2 := rfl
example: (List (Fin 2)).fromB = List.«(List (Fin x₁))».fromB := rfl

namespace Etst.SpecializedNsTest

structure Sig where
  Op: Type

def Sig.pair: Sig := ⟨Bool⟩
def Sig.other: Sig := ⟨Nat⟩

inductive Ex (sig: Sig) (E: Type) where
| const (e: E)
| op (o: sig.Op)
| neg (e: Ex sig E)

def Ex.descr {sig E} (_: Ex sig E): String := "generic"
def Ex.size {sig E}: Ex sig E → Nat
| .const _ | .op _ => 1
| .neg e => e.size + 1

@[specialized_namespace] abbrev BasicEx (sig: Sig) := Ex sig Unit
@[specialized_namespace] abbrev PairEx (E: Type) := Ex .pair E
@[specialized_namespace] abbrev BasicPairEx := BasicEx .pair

def BasicEx.name {sig} (_: Ex sig Unit): String := "basic"
def PairEx.name {E} (_: PairEx E): String := "pair"
def BasicPairEx.name (_: BasicPairEx): String := "basicPair"

def BasicEx.descr {sig} (_: BasicEx sig): String := "basic"

def BasicEx.onlyBasic {sig} (_: BasicEx sig): Nat := 1
def PairEx.onlyPair {E} (_: PairEx E) (n: Nat): Nat := n
def PairEx.toUnit {E} (_: PairEx E): Ex .pair Unit := .const ()

def BasicEx.clash {sig} (_: BasicEx sig): Nat := 1
def PairEx.clash {E} (_: PairEx E): Nat := 2

def BasicEx.withFirst {sig} (n: Nat) (_: Ex sig Unit): Nat := n
def BasicEx.zero {sig}: BasicEx sig := .const ()
private def BasicEx.priv {sig} (_: BasicEx sig): Nat := 42

def eb: Ex .other Unit := .const ()
def ep: Ex .pair Nat := .const 0
def ebp: Ex .pair Unit := .neg (.const ())


/-! Named namespaces, independently of how the type is written. -/

example: eb.onlyBasic = 1 := rfl
example: (eb: BasicEx .other).onlyBasic = 1 := rfl
example: ep.onlyPair 3 = 3 := rfl
example: ebp.onlyBasic = 1 := rfl
example: ebp.onlyPair 5 = 5 := rfl
example: (Ex.const () : Ex .other Unit).onlyBasic = 1 := rfl
example {sig} (e: Ex sig Unit): e.onlyBasic = 1 := rfl

/-! A name declared in several matching namespaces is ambiguous, even if one is more specific. -/

example: eb.name = "basic" := rfl
example: ep.name = "pair" := rfl

/-- error: Ambiguous field `name`: it is declared in several specialized namespaces matching this type: `BasicEx.name`, `PairEx.name`, `BasicPairEx.name` -/
#guard_msgs in
example := ebp.name

/-- error: Ambiguous field `name`: it is declared in several specialized namespaces matching this type: `BasicEx.name`, `PairEx.name`, `BasicPairEx.name` -/
#guard_msgs in
example := (ebp: BasicPairEx).name

example: BasicPairEx.name ebp = "basicPair" := rfl

/-- error: Ambiguous field `clash`: it is declared in several specialized namespaces matching this type: `BasicEx.clash`, `PairEx.clash` -/
#guard_msgs in
example := ebp.clash

example: eb.clash = 1 := rfl
example: ep.clash = 2 := rfl

/-! Specialized namespaces shadow the generic one, which is the fallback. -/

example: eb.descr = "basic" := rfl
example: ep.descr = "generic" := rfl
example: ebp.size = 2 := rfl

/-! Lean's abbreviation convention: the namespace of the type as written wins. -/

abbrev Alias := Ex .pair Unit
def Alias.name (_: Alias): String := "alias"
def ebpAlias: Alias := .neg (.const ())

example: ebpAlias.name = "alias" := rfl
example: ebpAlias.onlyBasic = 1 := rfl

/-! Patterns are matched up to reducible unfolding. -/

abbrev MyUnit := Unit
def OpaqueUnit := Unit

example (e: Ex .other MyUnit): e.onlyBasic = 1 := rfl

/--
error: Invalid field `onlyBasic`: The environment does not contain `Etst.SpecializedNsTest.Ex.onlyBasic`, so it is not possible to project the field `onlyBasic` from an expression
  e
of type `Ex Sig.other OpaqueUnit`
-/
#guard_msgs in
example (e: Ex .other OpaqueUnit) := e.onlyBasic

/-! Chains, argument placement, `@`, `|>.`, private declarations. -/

example: ep.toUnit.onlyBasic = 1 := rfl
example: ep.toUnit.descr.length = 5 := rfl
example: (ep.onlyPair 3).succ = 4 := rfl
example: ep.toUnit.onlyPair 7 = 7 := rfl
example: (ep |>.onlyPair 3) = 3 := rfl
example: eb.withFirst 5 = 5 := rfl
example: eb.withFirst (n := 5) = 5 := rfl
example: ep.onlyPair (n := 3) = 3 := rfl
example: @eb.onlyBasic .other = 1 := rfl
example: eb.priv = 42 := rfl
example: BasicEx.onlyBasic eb = 1 := rfl

-- No postponement when no specialized namespace of the head declares the field.
def BasicEx.mpr {sig} (_: BasicEx sig): Nat := 0
theorem implicitIff {n: Nat}: n = 0 ↔ 0 = n := ⟨Eq.symm, Eq.symm⟩
example (n: Nat) (h: 0 = n) (x: Fin (n + 1)): Fin (0 + 1) :=
  let eq := implicitIff.mpr h
  eq ▸ x

/-! Recursion through dot notation. -/

def BasicEx.depth {sig}: Ex sig Unit → Nat
| .const _ | .op _ => 0
| .neg e => e.depth + 1

example: ebp.depth = 1 := rfl

/-! Postponement until the type of the receiver is known. -/

example: [eb, eb].map (·.onlyBasic) = [1, 1] := rfl
example: [1, 2, 3].map (fun n => (ep.onlyPair n)) = [1, 2, 3] := rfl

/-! `.f` with an expected type. -/

example: Ex .other Unit := .zero
example: (.zero: Ex .other Unit) = .const () := rfl

/-! `(T).f` refers to a declaration without a receiver. -/

example: (Ex .pair Nat).name ep = "pair" := rfl
example: (Ex .pair Nat).name = @PairEx.name Nat := rfl
example: (Ex .other Unit).name = @BasicEx.name .other := rfl
example: (Ex .pair Nat).onlyPair ep 4 = 4 := rfl
example: (Ex .other Unit).zero = .const () := rfl
example: (Ex .other Unit).zero.onlyBasic = 1 := rfl
example: (Alias).name ebp = "alias" := rfl


/-! Bare namespaces. -/

namespace {sig} (Ex sig Unit)
  def bare1 (_: Ex sig Unit): Nat := 7
  -- Names from the namespace of the head and sibling declarations are visible.
  def bare1' (e: Ex sig Unit): Ex sig Unit := neg (const (bare1 e |> fun _ => ()))
end (Ex sig Unit)

example: eb.bare1 = 7 := rfl
example: ebp.bare1 = 7 := rfl
example: eb.bare1' = .neg (.const ()) := rfl

-- The generated name does not depend on parameter names or the context.
/-- info: @Ex.«(Ex x₁ Unit)».bare1 : {sig : Sig} → Ex sig Unit → Nat -/
#guard_msgs in
#check @Ex.«(Ex x₁ Unit)».bare1

-- Equivalent patterns denote the same namespace.
namespace (s: Sig) (Ex s MyUnit)
  def bare2 (_: Ex s Unit): Nat := 8
end (Ex s Unit)

/-- info: Ex.«(Ex x₁ Unit)».bare2 : (s : Sig) → Ex s Unit → Nat -/
#guard_msgs in
#check @Ex.«(Ex x₁ Unit)».bare2

namespace (E: Type) (Ex .pair (MyUnit × E)) in
def bare6 := 6

/-- info: Etst.SpecializedNsTest.Ex.«(Ex Sig.pair (MyUnit × x₁))».bare6 : Nat -/
#guard_msgs in
#check Ex.«(Ex Sig.pair (MyUnit × x₁))».bare6

-- Parameter names are irrelevant.
namespace {sig} (Ex sig Unit) in
def dup := 4

/-- error: `Etst.SpecializedNsTest.Ex.«(Ex x₁ Unit)».dup` has already been declared -/
#guard_msgs in
namespace {signature} (Ex signature Unit) in
def dup := 4

-- A bare namespace equivalent to a named one is still a distinct namespace.
namespace {sig} (Ex sig Unit)
  def onlyBasic (_: Ex sig Unit): Nat := 3
end (Ex sig Unit)

/--
error: Ambiguous field `onlyBasic`: it is declared in several specialized namespaces matching this type: `BasicEx.onlyBasic`, `Ex.«(Ex x₁ Unit)».onlyBasic`
-/
#guard_msgs in
example := eb.onlyBasic

-- The one-declaration form.
namespace (Ex .pair Nat) in
def bare3 (e: Ex .pair Nat): Nat := e.onlyPair 3

namespace {sig} (Ex sig Unit) in
/-- Docs are kept. -/
def bare4 (_: Ex sig Unit): Nat := 4

namespace {sig} (Ex sig Unit) in
theorem bare4_eq (e: Ex sig Unit): e.bare4 = 4 := rfl

namespace (Ex .pair Nat) in
abbrev Bare5 := Nat

example: ep.bare3 = 3 := rfl
example: ebp.bare4 = 4 := rfl
example: (Ex .other Unit).bare4_eq eb = rfl := rfl
example: (5: (Ex .pair Nat).Bare5) = 5 := rfl

namespace (Ex .pair Nat)
/-- error: Invalid `end (…)`: expected the current namespace `(Ex Sig.pair Nat)` -/
#guard_msgs in
end (Ex .other Nat)
end (Ex .pair Nat)

/-- error: Invalid `end (…)`: the current scope is not a specialized namespace -/
#guard_msgs in
end (Ex .pair Nat)


/-! The example from the proposal. -/

inductive Foo.Bar (T: Type)
| intro (t: T)

namespace Foo.(Bar Nat) in
def four := intro 4
namespace Foo.(Bar Nat) in
def getNat: Bar Nat → Nat | intro n => n

example := Foo.(Bar Nat).four
example: Foo.(Bar Nat).four.getNat = 4 := rfl
example: Foo.(Bar Nat).getNat Foo.(Bar Nat).four = 4 := rfl
example: (Foo.Bar.intro 4).getNat = 4 := rfl
example: (Foo.Bar Nat).four.getNat = 4 := rfl
example: (Foo.(Bar Nat): Type) = Foo.Bar Nat := rfl

-- Declarations of the generic namespace, instantiated according to the type.
example: Foo.(Bar Nat).intro 4 = Foo.(Bar Nat).four := rfl
example: Foo.(Bar Nat).intro = @Foo.Bar.intro Nat := rfl

namespace Foo
  namespace (Bar Nat) in
  def five: Bar Nat := intro 5
  example: (Bar Nat).five.getNat = 5 := rfl
end Foo

example: Foo.(Bar Nat).five.getNat = 5 := rfl

-- Nesting.
namespace Foo.(Bar Nat)
  inductive Baz (T: Type)
  | mk (n: Nat) (t: T)
end Foo.(Bar Nat)

namespace Foo.(Bar Nat).(Baz Bool) in
def boo: Baz Bool → Nat | .mk n _ => n

example: Foo.(Bar Nat).(Baz Bool).boo (.mk 3 true) = 3 := rfl
example: ((Foo.Bar Nat).Baz Bool).boo (.mk 3 true) = 3 := rfl
example: (Foo.(Bar Nat).(Baz Bool).mk 3 true).boo = 3 := rfl

/-- error: Expected a term of the form `C args`, where `C` is an identifier -/
#guard_msgs in
example := Foo.((fun x => x) Nat)


/-! `open` -/

section
  open {sig} (Ex sig Unit)
  example: bare1 eb = 7 := rfl
  example: bare4 ebp = 4 := rfl
end

open Foo.(Bar Nat) in
example: getNat four = 4 := rfl

open Foo.(Bar Nat).(Baz Bool) in
example: boo (.mk 2 false) = 2 := rfl

-- Scoped to the section, like `open`.
/-- error: Unknown identifier `four` -/
#guard_msgs in
example := four

/-- error: Unknown specialized namespace `(Ex Sig.pair Bool)` -/
#guard_msgs in
open (Ex .pair Bool)


/-! Universe polymorphism. -/

universe u

@[specialized_namespace] abbrev NatList := List Nat
def NatList.sumAll (l: List Nat): Nat := l.foldl (· + ·) 0

@[specialized_namespace] abbrev ListList (α: Type u) := List (List α)
def ListList.flat {α: Type u} (l: List (List α)): List α := l.flatten

example: [1, 2, 3].sumAll = 6 := rfl
example: [[1], [2, 3]].flat = [1, 2, 3] := rfl
example: [["a"]].flat = ["a"] := rfl

/--
error: Invalid field `sumAll`: The environment does not contain `List.sumAll`, so it is not possible to project the field `sumAll` from an expression
  ["a"]
of type `List String`
-/
#guard_msgs in
example := ["a"].sumAll


/-! Errors in declarations. -/

/-- error: `specialized_namespace` requires an `abbrev`, as patterns are matched up to reducible unfolding -/
#guard_msgs in
@[specialized_namespace] def NotAbbrev := Ex .pair Nat

/-- error: Expected a type, got
  5 -/
#guard_msgs in
@[specialized_namespace] abbrev NotType := 5

/-! Pretty printing. -/

/-- info: fun e => e.descr : Ex Sig.other Unit → String -/
#guard_msgs in
#check fun (e: Ex .other Unit) => e.descr

/-- info: fun e => e.withFirst 5 : Ex Sig.other Unit → Nat -/
#guard_msgs in
#check fun (e: Ex .other Unit) => e.withFirst 5

/-- info: fun e => e.bare1 : Ex Sig.other Unit → Nat -/
#guard_msgs in
#check fun (e: Ex .other Unit) => e.bare1

/-- info: fun e => e.toUnit.onlyPair 3 : Ex Sig.pair Nat → Nat -/
#guard_msgs in
#check fun (e: Ex .pair Nat) => e.toUnit.onlyPair 3

-- Field notation would not elaborate back to the same function.
/-- info: fun e => BasicPairEx.name e : Ex Sig.pair Unit → String -/
#guard_msgs in
#check fun (e: Ex .pair Unit) => BasicPairEx.name e

/-- info: fun e => BasicEx.onlyBasic e : Ex Sig.other Unit → Nat -/
#guard_msgs in
#check fun (e: Ex .other Unit) => BasicEx.onlyBasic e

/-- info: BasicEx.withFirst 5 : Ex Sig.other Unit → Nat -/
#guard_msgs in
#check (BasicEx.withFirst 5: Ex .other Unit → Nat)

/-- info: fun e => BasicEx.descr e : Ex Sig.other Unit → String -/
#guard_msgs in
set_option pp.fieldNotation false in
#check fun (e: Ex .other Unit) => e.descr

end Etst.SpecializedNsTest
