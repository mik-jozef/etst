module
public import Etst.WFC.Utils.Set3

public section
namespace Etst


/--
  A relation with one component per membership lane, monotone in the
  lane (definite membership is stronger than possible membership).
-/
structure TriRelation (T: Type*) where
  Rel: Set3.Lane → T → T → Prop
  rel_mono:
    ∀ {laneA laneB: Set3.Lane} {a b: T},
      Set3.Lane.Le laneA laneB →
      Rel laneA a b →
      Rel laneB a b

structure TriRelation.Sat {T: Type*}
  (rel: TriRelation T)
  (P: (T → T → Prop) → Prop)
where
  satLane: ∀ lane, P (rel.Rel lane)


/--
  Witnesses that the relation `rel` on representatives holds for
  given representatives of the classes `a` and `b`.
-/
structure LiftRelExStruct {PreT}
  {s: Setoid PreT}
  (rel: PreT → PreT → Prop)
  (a b: Quotient s)
  (preA preB: PreT)
:
  Prop
where
  aEq: a = ⟦preA⟧
  bEq: b = ⟦preB⟧
  rel: rel preA preB

/-
  The quotient lift of a relation on representatives: `a` and `b`
  are related if some of their representatives are.
-/
exposed def LiftRelEx {PreT}
  {s: Setoid PreT}
  (rel: PreT → PreT → Prop)
  (a b: Quotient s)
:
  Prop
:=
  ∃ preA preB, LiftRelExStruct rel a b preA preB

/--
  The ternary variant of `LiftRelExStruct` (eg. the graph of
  a function application).
-/
structure LiftRelExStruct₃ {PreT}
  {s: Setoid PreT}
  (rel: PreT → PreT → PreT → Prop)
  (a b c: Quotient s)
  (preA preB preC: PreT)
:
  Prop
where
  aEq: a = ⟦preA⟧
  bEq: b = ⟦preB⟧
  cEq: c = ⟦preC⟧
  rel: rel preA preB preC

/- The ternary variant of `LiftRelEx`. -/
exposed def LiftRelEx₃ {PreT}
  {s: Setoid PreT}
  (rel: PreT → PreT → PreT → Prop)
  (a b c: Quotient s)
:
  Prop
:=
  ∃ preA preB preC, LiftRelExStruct₃ rel a b c preA preB preC

/-
  A lane-indexed relation on the quotient, written in terms of a
  relation on representatives that respects the setoid. This is the
  generic shape of every `directHas_mk_iff` lemma.
-/
theorem LiftRelEx_mk_iff {T}
  {st: Setoid T}
  {Mem: T → Set3.Lane → T → Prop}
  (hmatch:
    ∀ {a b x: T} {lane: Set3.Lane},
      st.r a b → Mem a lane x → ∃ y, Mem b lane y ∧ st.r x y)
  {lane: Set3.Lane}
  {a b: T}
:
  LiftRelEx (s := st) (fun x y => Mem x lane y) ⟦a⟧ ⟦b⟧ ↔
    ∃ b', Mem a lane b' ∧ st.r b b'
:=
  Iff.intro
    (fun ⟨_preA, _preB, aEq, bEq, has⟩ =>
      let ⟨b', hasB, preBbisimB'⟩ := hmatch (Quotient.exact aEq.symm) has
      ⟨b', hasB, st.iseqv.trans (Quotient.exact bEq) preBbisimB'⟩)
    (fun ⟨b', hasB, bBisim⟩ =>
      ⟨a, b', rfl, Quotient.sound bBisim, hasB⟩)

/- The ternary variant of `LiftRelEx_mk_iff`. -/
theorem LiftRelEx₃_mk_iff {T}
  {st: Setoid T}
  {R: T → Set3.Lane → T → T → Prop}
  (hmatch:
    ∀ {f f' a r: T} {lane: Set3.Lane},
      st.r f f' → R f lane a r →
      ∃ a' r', R f' lane a' r' ∧ st.r a a' ∧ st.r r r')
  {lane: Set3.Lane}
  {f a r: T}
:
  LiftRelEx₃ (s := st) (fun f a r => R f lane a r) ⟦f⟧ ⟦a⟧ ⟦r⟧ ↔
    ∃ a' r', R f lane a' r' ∧ st.r a a' ∧ st.r r r'
:=
  Iff.intro
    (fun ⟨_preF, _preA, _preR, fEq, aEq, rEq, has⟩ =>
      let ⟨fA, fR, has', preAbisimA', preRbisimR'⟩ :=
        hmatch (Quotient.exact fEq.symm) has
      ⟨fA, fR, has',
       st.iseqv.trans (Quotient.exact aEq) preAbisimA',
       st.iseqv.trans (Quotient.exact rEq) preRbisimR'⟩)
    (fun ⟨a', r', has, aBisim, rBisim⟩ =>
      ⟨f, a', r', rfl, Quotient.sound aBisim, Quotient.sound rBisim, has⟩)
