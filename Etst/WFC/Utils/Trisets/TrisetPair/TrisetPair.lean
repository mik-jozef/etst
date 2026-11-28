/-
  See `Triset.lean`.
-/
module
public import Etst.WFC.Utils.Trisets.Triset.Triset

public section
namespace Etst


namespace Pair
  /-
    A `PreTrisetPair` is either a triset of `PreTrisetPair`s, null,
    or a pair of `PreTrisetPair`s.
    
    Trisets are nonwellfounded, pairs are. (Does this mean that
    pairs are inductive and trisets coinductive?)
  -/
  inductive PreTrisetPair where
  | set (ts: PreTriset)
  | null
  | pair (zth fst: PreTrisetPair)
  
  namespace PreTrisetPair
    /-
      Encodes a `PreTrisetPair` as a raw pair.
      Contrast with `PreTriset`, where all pairs code trisets.
    -/
    exposed def toPair: PreTrisetPair → Pair
    | .set ts => .pair (.nat 0) ts
    | .null => .pair (.nat 1) .null
    | .pair p0 p1 => .pair (.nat 1) (.pair p0.toPair p1.toPair)
    
    -- The encoding of `PreTrisetPair`s as raw pairs is injective.
    theorem toPair_inj {a b: PreTrisetPair} (h: a.toPair = b.toPair): a = b :=
      match a, b, h with
      | .set _, .set _, h =>
          congrArg set (Pair.noConfusion h fun _ hr => hr)
      | .null, .null, _ => rfl
      | .pair a0 a1, .pair b0 b1, h => by
          injection h with hTag h01
          injection h01 with h0 h1
          exact congrArg₂ pair (toPair_inj h0) (toPair_inj h1)
    
    
    -- Membership in a lane, `a ∈ b` (`defLane`) or `a ∈? b` (`posLane`).
    exposed def Has: PreTrisetPair → Set3.Lane → PreTrisetPair → Prop
    | set ts, lane, elem => ts.Has lane elem.toPair
    | _, _, _ => False
    
    theorem Has.mono {laneA laneB}
      {ts elem: PreTrisetPair}
      (has: ts.Has laneA elem)
      (le: Set3.Lane.Le laneA laneB := by decide)
    :
      ts.Has laneB elem
    :=
      match ts with
      | .set _ => Pair.PreTriset.Has.mono has le
      | .null => has
      | .pair _ _ => has
    
    
    inductive TransitionLabels where
    | has (lane: Set3.Lane) -- member of a triset, in the given lane
    | zth -- zeroth element of a pair
    | fst -- first element of a pair
    | isNull -- self loop that identifies null values
    
    /-
      One can transition a triset to its elements, a pair
      to its components, and null to itself.
    -/
    exposed def transitionSystem:
      LabeledTransitionSystem TransitionLabels PreTrisetPair
    := fun
      | .has lane, a, b => a.Has lane b
      | .zth, a, b => ∃ a1, a = pair b a1
      | .fst, a, b => ∃ a0, a = pair a0 b
      | .isNull, a, b => a = .null ∧ b = .null
    
    exposed def IsBisim := transitionSystem.IsBisimilar
    
    exposed def setoid: Setoid PreTrisetPair where
      r := IsBisim
      iseqv := transitionSystem.IsBisimilar_is_equivalence
    
    theorem IsBisim.refl (a: PreTrisetPair): a.IsBisim a :=
      transitionSystem.IsBisimilar_is_equivalence.refl _
    
    theorem IsBisim.symm {a b: PreTrisetPair} (h: a.IsBisim b): b.IsBisim a :=
      transitionSystem.IsBisimilar_is_equivalence.symm h
    
    theorem IsBisim.trans {a b c: PreTrisetPair}
      (h0: a.IsBisim b)
      (h1: b.IsBisim c)
    :
      a.IsBisim c
    :=
      transitionSystem.IsBisimilar_is_equivalence.trans h0 h1
    
    -- Bisimilar values have matching members, in either lane.
    theorem IsBisim.has {a b e: PreTrisetPair}
      {lane: Set3.Lane}
      (bisim: a.IsBisim b)
      (has: a.Has lane e)
    :
      ∃ e', b.Has lane e' ∧ e.IsBisim e'
    :=
      transitionSystem.IsBisimilar_isSimulation (.has lane) a b e bisim has
    
  end PreTrisetPair
  
  exposed def TrisetPair := Quotient PreTrisetPair.setoid
  
  namespace TrisetPair
    exposed def DirectTrans
      (label: PreTrisetPair.TransitionLabels)
      (a b: TrisetPair)
    :
      Prop
    :=
      LiftRelEx (PreTrisetPair.transitionSystem label) a b
    
    
    -- `ts` has `elem` as a member in the given lane.
    exposed def DirectHas (lane: Set3.Lane) (ts elem: TrisetPair): Prop :=
      DirectTrans (.has lane) ts elem
    
    -- `p` is a pair with zeroth component `zth`.
    exposed def DirectZth (p zth: TrisetPair): Prop :=
      DirectTrans .zth p zth
    
    -- `p` is a pair with first component `fst`.
    exposed def DirectFst (p fst: TrisetPair): Prop :=
      DirectTrans .fst p fst
    
    -- `p` is null.
    exposed def DirectNull (p: TrisetPair): Prop :=
      DirectTrans .isNull p p
    
    
    exposed def DirectMem: TriRelation TrisetPair where
      Rel := DirectHas
      rel_mono := fun le h =>
        let ⟨preA, preB, ⟨aEq, bEq, has⟩⟩ := h
        ⟨preA, preB, ⟨aEq, bEq, has.mono le⟩⟩
    
    theorem directHas_mk_iff {lane: Set3.Lane} {s e: PreTrisetPair}:
      DirectHas lane ⟦s⟧ ⟦e⟧ ↔ ∃ e', s.Has lane e' ∧ e.IsBisim e'
    :=
      LiftRelEx_mk_iff (st := PreTrisetPair.setoid) (Mem := PreTrisetPair.Has)
        (fun h => PreTrisetPair.IsBisim.has h)
    
  end TrisetPair
end Pair
