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
module
public import Etst.WFC.Ch7_Polymorphism
public import Etst.WFC.Utils.General.Bisimilarity
public import Etst.WFC.Utils.LiftRelEx

public section
namespace Etst



namespace Pair
  exposed def PreTriset := Pair
  
  namespace PreTriset
    -- Membership in a lane: `a ∈ b` (`defLane`) or `a ∈? b` (`posLane`).
    exposed def Has (ts: PreTriset) (lane: Set3.Lane) (elem: PreTriset): Prop :=
      UniSetMapIndex.Has ts lane elem
    
    -- Strong (a la "definite") membership, `a ∈ b`.
    exposed abbrev Ins (ts elem: PreTriset): Prop := ts.Has .defLane elem
    
    -- Weak (a la "possible") membership, `a ∈? b`.
    exposed abbrev Inw (ts elem: PreTriset): Prop := ts.Has .posLane elem
    
    theorem Has.mono {ts elem: PreTriset} {laneA laneB}
      (has: ts.Has laneA elem)
      (le: Set3.Lane.Le laneA laneB := by decide)
    :
      ts.Has laneB elem
    :=
      le.liftMem has
    
    -- One can transition sets to their elements.
    exposed def transitionSystem:
      LabeledTransitionSystem Set3.Lane PreTriset
    :=
      fun l a b => a.Has l b
    
    exposed def IsBisim := transitionSystem.IsBisimilar
    
    exposed def setoid: Setoid PreTriset where
      r := IsBisim
      iseqv := transitionSystem.IsBisimilar_is_equivalence
    
    
    exposed def empty: PreTriset := UniSetMapIndex.emptyIndex
    
    
    -- Transporting a membership across an equality of `uniSetMap` images.
    theorem Has.of_call_eq {u v elem: Pair} {lane: Set3.Lane}
      (eq: uniSetMap.call u = uniSetMap.call v)
      (has: Has u lane elem)
    :
      Has v lane elem
    :=
      Eq.mp (congrArg (fun s => elem ∈ s.getLane lane) eq) has
    
    -- Equal `uniSetMap`-images are bisimilar.
    theorem isBisim_of_uniSetMap_call_eq {u v: Pair}
      (eq: uniSetMap.call u = uniSetMap.call v)
    :
      IsBisim u v
    :=
      ⟨fun uu vv => uniSetMap.call uu = uniSetMap.call vv,
        ⟨fun _ _uu _vv uu' uuEq trans =>
            ⟨uu', Has.of_call_eq (u := _uu) (v := _vv) uuEq trans, rfl⟩,
         fun _ _uu _vv uu' uuEq trans =>
            ⟨uu', Has.of_call_eq (u := _uu) (v := _vv) uuEq.symm trans, rfl⟩⟩,
       eq⟩
    
  end PreTriset
  
  exposed def Triset := Quotient PreTriset.setoid
  
  namespace Triset
    -- `ts` is a triset with `elem` as a member in the given lane.
    exposed def DirectHas (lane: Set3.Lane) (ts elem: Triset): Prop :=
      LiftRelEx (fun a b => a.Has lane b) ts elem
    
    exposed def DirectMem: TriRelation Triset where
      Rel := DirectHas
      rel_mono := fun le h =>
        let ⟨preTs, preElem, ⟨tsEq, elemEq, has⟩⟩ := h
        ⟨preTs, preElem, ⟨tsEq, elemEq, has.mono le⟩⟩
    
    
    -- Not hereditarily classical.
    inductive Nhc: Triset → Prop
    | notClassical {ts elem: Triset}
        (isPos: ts.DirectHas .posLane elem)
        (notDef: ¬ ts.DirectHas .defLane elem)
      :
        Nhc ts
    | containsNhc {ts elem: Triset}
        (isPos: ts.DirectHas .posLane elem)
        (isNhc: Nhc elem)
      :
        Nhc ts
    
    -- Hereditarily classical.
    exposed def Hc (ts: Triset): Prop := ¬ Nhc ts
    
  end Triset
end Pair
