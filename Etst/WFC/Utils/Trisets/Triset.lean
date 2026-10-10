/-
  Here we quotient indices of uniSetMap by bisimilarity to define the
  "sets" of WFC.
  
  This quotient is based on the actual ("exact") bisimilarity defined
  as a Lean property, and is not WFC-definable (as WFC cannot treat the
  definite and possible membership separately). Contrast with the "fuzzy"
  bisimilarity of `Etst/WFC/Utils/Trisets/TrisetMembership.lean`, which
  is WFC-definable, and coincides with exact bisimilarity for classical
  trisets.
  
  The main purpose of quotienting the sets is to get an assurance that
  the operations on them respect their intended semantics, so that we
  don't, for example, treat two pairs coding empty sets differently just
  because they are different pairs.
  
  ## Some in-progress notes
  There is also TrisetPair, from before I realized I can represent
  pairs as `{ {{}, {A}}, {{{}}, {{B}}} }` (the standard Kuratowski
  `{{A}, {A, B}}` does not work for non-classical sets, we cannot
  reliably get both the zeroth and first elements of the pair).
  There is also a (WFC-definable) embedding from Triset to TrisetPair.
  
  Even though I figured out pairs, it seems that with Triset, there
  cannot be a way to represent functions & function calls that would
  - be general enough that that would work with arbitrary trisets as
    arguments,
  - map classical inputs to classical outputs.
  
  (The following paragraph will treat a triset of pairs as identical
  to a triset of triset encodings of pairs for simplicity.)
  
  This means that even a trivial type like List (of T, that accepts
  an arbitrary T) cannot be defined as a triset. WFC can easily define
  it if function application is the ordinary `Expr.call`. The only issue
  is that `Expr.call` does not in general respect bisimilarity. It does,
  however, respect bisimilarity if the function is defined using
  bisimilarity-preserving operations *and* every code is a part of its
  domain.
  
  So the options are:
  - To resign to `Triset`, and accept that a user wanting to define List
    that preserves classicalness will have to pick a some classical triset
    serving as a type universe, to limit its domain. Different type universes
    would have to have their own List definitions.
  - Since a general and classical-preserving List is easily definable in
    WFC, to try to extend `Triset` in a way that would accomodate these
    definitions.
  
  I consider the zeroth option to be severely impractical. That's my
  motivation for trying to define yet another variation on trisets,
  TrisetFn. An instance of TrisetFn would be either a triset of TrisetFn
  instances, or a function from TrisetFn to TrisetFn.
-/

import Etst.WFC.Ch7_Polymorphism
import Etst.WFC.Utils.General.Bisimilarity

namespace Etst


structure TriRelation (T: Type*) where
  RelDef: T → T → Prop
  RelPos: T → T → Prop
  def_le_pos: ∀ {a b: T}, RelDef a b → RelPos a b

structure TriRelation.Sat {T: Type*}
  (rel: TriRelation T)
  (P: Set (T → T → Prop))
where
  satDef: P rel.RelDef
  satPos: P rel.RelPos

/--
  Witnesses that the relation `rel` on representatives holds for
  given representatives of the classes `a` and `b`.
-/
structure DirectRelStruct
  {PreT: Type*} (s: Setoid PreT)
  (rel: PreT → PreT → Prop)
  (a b: let _ := s; Quotient s)
  (preA preB: PreT)
:
  Prop
where
  aEq: a = ⟦preA⟧
  bEq: b = ⟦preB⟧
  rel: rel preA preB

/--
  The quotient lift of a relation on representatives: `a` and `b`
  are related if some of their representatives are.
-/
def DirectRel
  {PreT: Type*} {s: Setoid PreT}
  (rel: PreT → PreT → Prop)
  (a b: Quotient s)
:
  Prop
:=
  ∃ preA preB, DirectRelStruct s rel a b preA preB

/--
  The ternary variant of `DirectRelStruct` (eg. the graph of
  a function application).
-/
structure DirectRelStruct₃
  {PreT: Type*} (s: Setoid PreT)
  (rel: PreT → PreT → PreT → Prop)
  (a b c: let _ := s; Quotient s)
  (preA preB preC: PreT)
:
  Prop
where
  aEq: a = ⟦preA⟧
  bEq: b = ⟦preB⟧
  cEq: c = ⟦preC⟧
  rel: rel preA preB preC

/-- The ternary variant of `DirectRel`. -/
def DirectRel₃
  {PreT: Type*} {s: Setoid PreT}
  (rel: PreT → PreT → PreT → Prop)
  (a b c: Quotient s)
:
  Prop
:=
  ∃ preA preB preC, DirectRelStruct₃ s rel a b c preA preB preC


namespace Pair
  def PreTriset := Pair
  
  namespace PreTriset
    -- Strong (a la "definite") membership, `a ∈ b`.
    def Ins (ts elem: PreTriset): Prop :=
      (uniSetMap.call ts).defMem elem
    
    -- Weak (a la "possible") membership, `a ∈? b`.
    def Inw (ts elem: PreTriset): Prop :=
      (uniSetMap.call ts).posMem elem
    
    inductive TransitionLabels where
    | ins
    | inw
    
    -- One can transition sets to their elements.
    def transitionSystem:
      LabeledTransitionSystem TransitionLabels PreTriset
    := fun
      | .ins, a, b => a.Ins b
      | .inw, a, b => a.Inw b
    
    def IsBisim := transitionSystem.IsBisimilar
    
    def setoid: Setoid PreTriset where
      r := IsBisim
      iseqv := transitionSystem.IsBisimilar_is_equivalence
    
    
    def empty: PreTriset := uniSetMapIndex.emptyIndex
    
    
    -- Equal `uniSetMap`-images are bisimilar.
    def isBisim_of_uniSetMap_call_eq {u v: Pair}
      (eq: uniSetMap.call u = uniSetMap.call v)
    :
      IsBisim u v
    :=
      ⟨fun uu vv => uniSetMap.call uu = uniSetMap.call vv,
        ⟨fun l uu vv uu' eq trans =>
          ⟨uu',
           match l, trans with
           | .ins, t =>
             show (uniSetMap.call vv).defMem uu' from
               eq ▸ (show (uniSetMap.call uu).defMem uu' from t)
           | .inw, t =>
             show (uniSetMap.call vv).posMem uu' from
               eq ▸ (show (uniSetMap.call uu).posMem uu' from t),
           rfl⟩,
        fun l uu vv uu' eq trans =>
          ⟨uu',
           match l, trans with
           | .ins, t =>
             show (uniSetMap.call vv).defMem uu' from
               eq ▸ (show (uniSetMap.call uu).defMem uu' from t)
           | .inw, t =>
             show (uniSetMap.call vv).posMem uu' from
               eq ▸ (show (uniSetMap.call uu).posMem uu' from t),
           rfl⟩⟩,
       eq⟩
    
  end PreTriset
  
  def Triset := Quotient PreTriset.setoid
  
  namespace Triset
    -- `ts` is a triset with definite member `elem`.
    def DirectIns (ts elem: Triset): Prop :=
      DirectRel PreTriset.Ins ts elem
    
    -- `ts` is a triset with possible member `elem`.
    def DirectInw (ts elem: Triset): Prop :=
      DirectRel PreTriset.Inw ts elem
    
    def DirectMem: TriRelation Triset where
      RelDef := DirectIns
      RelPos := DirectInw
      def_le_pos
      | ⟨preTs, preElem, ⟨tsEq, elemEq, ins⟩⟩ =>
        ⟨preTs, preElem, ⟨tsEq, elemEq, ins.toPos⟩⟩
    
    
    -- Not hereditarily classical.
    inductive Nhc: Triset → Prop
    | notClassical {ts elem: Triset}
        (isPos: ts.DirectInw elem)
        (notDef: ¬ ts.DirectIns elem)
      :
        Nhc ts
    | containsNhc {ts elem: Triset}
        (isPos: ts.DirectInw elem)
        (isNhc: Nhc elem)
      :
        Nhc ts
    
    -- Hereditarily classical.
    def Hc (ts: Triset): Prop := ¬ Nhc ts
    
  end Triset
end Pair
