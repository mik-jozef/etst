/-
  A `TrisetFn` value is either a triset whose members are values,
  or a function from values to values. Equivalently, `TrisetFn` is
  an extension of `Triset` that includes functional values. There is
  an embedding (`Triset.toTrisetFn`) of `Triset` into `TrisetFn`.
  See `Triset.lean` for additional context.
  
  While `Triset` values are represented with `uniSetMap` indices directly,
  the codes representing `TrisetFn` values are tagged:
  * `(0, i)` encodes a triset,
  * `(1, g)` encodes a function.
  
  The body of a code is a `uniSetMap` index:
  * the `i` of `(0, i)` — an index such that `uniSetMap.call i` is the
    triset of the *codes* of the members.
  * the `g` of `(1, g)` — an index such that `uniSetMap.call g` is the
    triset of the pairs `(a, r)` of codes such that `f` sends `a` to `r`.
  
  Function application is definable in WFC using `Expr.call` on those
  codes that are total and bisimilarity preserving. 
  
  ## Notes
  I have some doubts about this approach for functions, as it suffers from
  two issues:
  0. Not only is function application not WFC-definable for every code,
    but there are functions for which no code has a WFC-definable appli-
    cation. Take a code F whose domain is exactly one code C, where C
    represents a value V. F represents a function whose domain is V, but
    WFC has no way to tell whether an arbitrary code represents V, so it
    cannot reliably produce `⟦F⟧ V` for any code but C.
  1. The functions are in general multivalued. This is what happens when
    a code sends two bisimilar codes to different values. In this case,
    `Expr.call` only represents function application if all such bisimilar
    codes are equal.
  
  The intention was to capture only those functions that are WFC-definable
  and somehow single-valued by construction. However, I got stuck trying
  to get there, and I have to move on. The hope is that these extra values
  will turn out not to interfere with the intended behavior of TrisetFn.
  Who knows, given the relative simplicity of this solution, and that
  I couldn't come up with something else, maybe this is the natural one
  after all.
  
  An approach I've considered is syntactically restricting which function
  codes are valid. However, this feels ad hoc, would presumably be a lot
  of work, would likely depend on the precise syntactic class of codes,
  and who knows whether the result would even be natural. It is what it is.
  
  TODO: It would be really nice to have some results that reduce TrisetFn
  to Triset somehow. Trisets are simpler, and while TrisetFn aren't really
  a conservative extension (at least in a naive way; a triset cannot
  simulate exact call), it would be nice if we could bound the differences
  between them, and find a way to port results about one to results about
  the other.
  
  For example, it could be a nice result if any type universe of TrisetFn,
  when restricted to itself (ie. we restrict the domains of functions),
  is also a type universe of Triset (when functions are coded).
-/
module
public import Etst.WFC.Utils.Trisets.Triset

public section
namespace Etst


namespace Pair
  inductive PreTrisetFn where
  | set (ts: PreTriset)
  | fn (graph: PreTriset)
  
  namespace PreTrisetFn
    exposed def toPair: PreTrisetFn → Pair
    | .set ts => .pair (.nat 0) ts
    | .fn graph => .pair (.nat 1) graph
    
    theorem toPair_inj {a b: PreTrisetFn} (h: a.toPair = b.toPair): a = b :=
      match a, b, h with
      | .set _, .set _, h => congrArg set (Pair.noConfusion h fun _ hr => hr)
      | .fn _, .fn _, h => congrArg fn (Pair.noConfusion h fun _ hr => hr)
    
    exposed def IsFn: PreTrisetFn → Prop
    | fn _ => True
    | set _ => False
    
    -- Membership in a lane, `a ∈ b` (`defLane`) or `a ∈? b` (`posLane`).
    exposed def Has: PreTrisetFn → Set3.Lane → PreTrisetFn → Prop
    | set ts, lane, e => ts.Has lane e.toPair
    | .fn _, _, _ => False
    
    -- `(a, r)` is an entry of the graph of `f`, in the given lane.
    exposed def HasEntry: PreTrisetFn → Set3.Lane → PreTrisetFn → PreTrisetFn → Prop
    | fn graph, lane, a, r => graph.Has lane (.pair a.toPair r.toPair)
    | .set _, _, _, _ => False
    
    theorem Has.mono {laneA laneB}
      {s e: PreTrisetFn}
      (has: s.Has laneA e)
      (le: Set3.Lane.Le laneA laneB := by decide)
    :
      s.Has laneB e
    :=
      match s with
      | set _ => Pair.PreTriset.Has.mono has le
      | .fn _ => has
    
    theorem HasEntry.mono {laneA laneB}
      {f a r: PreTrisetFn}
      (has: f.HasEntry laneA a r)
      (le: Set3.Lane.Le laneA laneB := by decide)
    :
      f.HasEntry laneB a r
    :=
      match f with
      | fn _ => Pair.PreTriset.Has.mono has le
      | .set _ => has
    
    theorem not_hasEntry_of_not_isFn {lane a r}
      {f: PreTrisetFn}
      (notFn: ¬ f.IsFn)
      (has: f.HasEntry lane a r)
    :
      False
    :=
      match f with
      | fn _ => notFn trivial
    
    theorem not_has_of_isFn {lane e}
      {s: PreTrisetFn}
      (isFn: s.IsFn)
      (has: s.Has lane e)
    :
      False
    :=
      match s with
      | set _ => isFn
    
    
    -- `entry a r` is internal to the transition system, not a value.
    inductive Node where
    | val (v: PreTrisetFn)
    | entry (arg res: PreTrisetFn)
    
    inductive TransitionLabels where
    | has (lane: Set3.Lane) -- member of a triset, in the given lane
    | hasEntry (lane: Set3.Lane) -- entry of a function graph
    | arg
    | res
    | isFn -- self loop that distinguishes functions from trisets
    
    inductive Step: LabeledTransitionSystem TransitionLabels Node
    | has {lane s e}
        (h: s.Has lane e)
      :
        Step (.has lane) (.val s) (.val e)
    | hasEntry {lane f a r}
        (h: f.HasEntry lane a r)
      :
        Step (.hasEntry lane) (.val f) (.entry a r)
    | arg (a r): Step .arg (.entry a r) (.val a)
    | res (a r): Step .res (.entry a r) (.val r)
    | isFn (graph): Step .isFn (.val (.fn graph)) (.val (.fn graph))
    
    abbrev transitionSystem := Step
    
    theorem Step.ofIsFn {v: PreTrisetFn} (isFn: v.IsFn): Step .isFn (.val v) (.val v) :=
      match v with
      | fn graph => .isFn graph
    
    exposed def IsBisim (a b: PreTrisetFn): Prop :=
      transitionSystem.IsBisimilar (.val a) (.val b)
    
    theorem IsBisim.refl (a: PreTrisetFn): a.IsBisim a :=
      transitionSystem.IsBisimilar_is_equivalence.refl _
    
    theorem IsBisim.symm {a b: PreTrisetFn} (h: a.IsBisim b): b.IsBisim a :=
      transitionSystem.IsBisimilar_is_equivalence.symm h
    
    theorem IsBisim.trans {a b c: PreTrisetFn}
      (h0: a.IsBisim b)
      (h1: b.IsBisim c)
    :
      a.IsBisim c
    :=
      transitionSystem.IsBisimilar_is_equivalence.trans h0 h1
    
    exposed def setoid: Setoid PreTrisetFn where
      r := IsBisim
      iseqv := ⟨IsBisim.refl, IsBisim.symm, IsBisim.trans⟩
    
    
    /-
      Two nodes are bisimilar if their steps match, landing either in
      bisimilar nodes, or back in the pair itself.
    -/
    theorem isBisimilar_of_steps {x0 y0: Node}
      (fwd:
        ∀ l x', Step l x0 x' →
        ∃ y', Step l y0 y' ∧
          (transitionSystem.IsBisimilar x' y' ∨ (x' = x0 ∧ y' = y0)))
      (bwd:
        ∀ l y', Step l y0 y' →
        ∃ x', Step l x0 x' ∧
          (transitionSystem.IsBisimilar x' y' ∨ (x' = x0 ∧ y' = y0)))
    :
      transitionSystem.IsBisimilar x0 y0
    :=
      let R (x y: Node): Prop :=
        transitionSystem.IsBisimilar x y ∨ (x = x0 ∧ y = y0)
      let simL: transitionSystem.IsSimulation R := fun
        | l, x, y, x', .inl b, st =>
          let ⟨y', st', b'⟩ :=
            transitionSystem.IsBisimilar_isSimulation l x y x' b st
          ⟨y', st', .inl b'⟩
        | l, _, _, x', .inr ⟨rfl, rfl⟩, st => fwd l x' st
      let simR: transitionSystem.IsSimulation (Function.swap R) := fun
        | l, x, y, x', .inl b, st =>
          let ⟨y', st', b'⟩ :=
            transitionSystem.IsBisimilar_isSimulation l x y x'
              (transitionSystem.IsBisimilar_is_equivalence.symm b) st
          ⟨y', st', .inl (transitionSystem.IsBisimilar_is_equivalence.symm b')⟩
        | l, _, _, y', .inr ⟨rfl, rfl⟩, st => bwd l y' st
      ⟨R, ⟨simL, simR⟩, .inr ⟨rfl, rfl⟩⟩
    
    theorem isBisimilar_entry {a a' r r': PreTrisetFn}
      (ha: a.IsBisim a')
      (hr: r.IsBisim r')
    :
      transitionSystem.IsBisimilar (.entry a r) (.entry a' r')
    :=
      isBisimilar_of_steps
        (fun _ _ st =>
          match st with
          | .arg _ _ => ⟨_, .arg a' r', .inl ha⟩
          | .res _ _ => ⟨_, .res a' r', .inl hr⟩)
        (fun _ _ st =>
          match st with
          | .arg _ _ => ⟨_, .arg a r, .inl ha⟩
          | .res _ _ => ⟨_, .res a r, .inl hr⟩)
    
    theorem IsBisim.entryArg {a r a' r': PreTrisetFn}
      (h: transitionSystem.IsBisimilar (.entry a r) (.entry a' r'))
    :
      a.IsBisim a'
    :=
      let ⟨_, st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation .arg _ _ _ h (.arg a r)
      match st with
      | .arg _ _ => hy
    
    theorem IsBisim.entryRes {a r a' r': PreTrisetFn}
      (h: transitionSystem.IsBisimilar (.entry a r) (.entry a' r'))
    :
      r.IsBisim r'
    :=
      let ⟨_, st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation .res _ _ _ h (.res a r)
      match st with
      | .res _ _ => hy
    
    
    -- Bisimilar values have matching members.
    theorem IsBisim.has {lane}
      {s s' e: PreTrisetFn}
      (b: s.IsBisim s')
      (has: s.Has lane e)
    :
      ∃ e', s'.Has lane e' ∧ e.IsBisim e'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation
          (.has lane) _ _ _ b (.has has)
      match y', st, hy with
      | _, .has has', hy => ⟨_, has', hy⟩
    
    -- Bisimilar values have matching graph entries.
    theorem IsBisim.hasEntry {lane}
      {f f' a r: PreTrisetFn}
      (b: f.IsBisim f')
      (has: f.HasEntry lane a r)
    :
      ∃ a' r', f'.HasEntry lane a' r' ∧ a.IsBisim a' ∧ r.IsBisim r'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation
          (.hasEntry lane) _ _ _ b (.hasEntry has)
      match y', st, hy with
      | _, .hasEntry has', hy =>
        ⟨_, _, has', IsBisim.entryArg hy, IsBisim.entryRes hy⟩
    
    theorem IsBisim.isFn {v v': PreTrisetFn}
      (b: v.IsBisim v')
      (isFn: v.IsFn)
    :
      v'.IsFn
    :=
      let ⟨_, st, _⟩ :=
        transitionSystem.IsBisimilar_isSimulation
          .isFn _ _ _ b (Step.ofIsFn isFn)
      match st with
      | .isFn _ => trivial
    
    
    -- ## Extensionality on representatives
    
    theorem isBisim_of_members {s t: PreTrisetFn}
      (sNotFn: ¬ s.IsFn)
      (tNotFn: ¬ t.IsFn)
      (hasST: ∀ {lane e}, s.Has lane e → ∃ e', t.Has lane e' ∧ e.IsBisim e')
      (hasTS: ∀ {lane e}, t.Has lane e → ∃ e', s.Has lane e' ∧ e'.IsBisim e)
    :
      s.IsBisim t
    :=
      isBisimilar_of_steps
        (fun _ _ st =>
          match st with
          | .has has =>
            let ⟨_, has', b⟩ := hasST has
            ⟨_, .has has', .inl b⟩
          | .hasEntry has =>
            (not_hasEntry_of_not_isFn sNotFn has).elim
          | .isFn _ => (sNotFn trivial).elim)
        (fun _ _ st =>
          match st with
          | .has has =>
            let ⟨_, has', b⟩ := hasTS has
            ⟨_, .has has', .inl b⟩
          | .hasEntry has =>
            (not_hasEntry_of_not_isFn tNotFn has).elim
          | .isFn _ => (tNotFn trivial).elim)
    
    theorem isBisim_of_entries {f g: PreTrisetFn}
      (fFn: f.IsFn)
      (gFn: g.IsFn)
      (hasFG:
        ∀ {lane a r}, f.HasEntry lane a r →
        ∃ a' r', g.HasEntry lane a' r' ∧ a.IsBisim a' ∧ r.IsBisim r')
      (hasGF:
        ∀ {lane a r}, g.HasEntry lane a r →
        ∃ a' r', f.HasEntry lane a' r' ∧ a'.IsBisim a ∧ r'.IsBisim r)
    :
      f.IsBisim g
    :=
      isBisimilar_of_steps
        (fun _ _ st =>
          match st with
          | .has has => (not_has_of_isFn fFn has).elim
          | .hasEntry has =>
            let ⟨_, _, has', ba, br⟩ := hasFG has
            ⟨_, .hasEntry has', .inl (isBisimilar_entry ba br)⟩
          | .isFn _ => ⟨_, Step.ofIsFn gFn, .inr ⟨rfl, rfl⟩⟩)
        (fun _ _ st =>
          match st with
          | .has has => (not_has_of_isFn gFn has).elim
          | .hasEntry has =>
            let ⟨_, _, has', ba, br⟩ := hasGF has
            ⟨_, .hasEntry has', .inl (isBisimilar_entry ba br)⟩
          | .isFn _ => ⟨_, Step.ofIsFn fFn, .inr ⟨rfl, rfl⟩⟩)
    
    
    /-
      A graph is saturated if bisimilar arguments have bisimilar results.
      For saturated graphs, looking up the exact code of the argument
      (ie. `Expr.call`) computes the application.
    -/
    structure Saturated (f: PreTrisetFn): Prop where
      has:
        ∀ {lane a a' r}, a.IsBisim a' → f.HasEntry lane a r →
        ∃ r', f.HasEntry lane a' r' ∧ r.IsBisim r'
    
    theorem hasEntry_iff_call {lane}
      {graph a r: PreTrisetFn}
    :
      (fn graph.toPair).HasEntry lane a r
        ↔
      r.toPair ∈ ((uniSetMap.call graph.toPair).call a.toPair).getLane lane
    :=
      ⟨Set3.inCall, Set3.inCallElim⟩
    
  end PreTrisetFn
  
  
  exposed def TrisetFn := Quotient PreTrisetFn.setoid
  
  namespace TrisetFn
    open PreTrisetFn
    
    exposed def IsFn: TrisetFn → Prop :=
      Quotient.lift PreTrisetFn.IsFn fun _ _ b =>
        propext ⟨IsBisim.isFn b, IsBisim.isFn (IsBisim.symm b)⟩
    
    -- `ts` has `elem` as a member in the given lane.
    exposed def DirectHas (lane: Set3.Lane) (ts elem: TrisetFn): Prop :=
      DirectRel (fun a b => a.Has lane b) ts elem
    
    exposed def DirectMem: TriRelation TrisetFn where
      Rel := DirectHas
      rel_mono := fun le h =>
        let ⟨preTs, preElem, ⟨tsEq, elemEq, has⟩⟩ := h
        ⟨preTs, preElem, ⟨tsEq, elemEq, has.mono le⟩⟩
    
    -- `res` is a member of the result of applying `f` to `arg`, in the
    -- given lane.
    exposed def DirectCallHas (lane: Set3.Lane) (f arg res: TrisetFn): Prop :=
      DirectRel₃ (fun f a r => f.HasEntry lane a r) f arg res
    
    theorem DirectCallHas.mono {laneA laneB}
      {f arg res: TrisetFn}
      (has: f.DirectCallHas laneA arg res)
      (le: Set3.Lane.Le laneA laneB := by decide)
    :
      f.DirectCallHas laneB arg res
    :=
      let ⟨preF, preArg, preRes, fEq, argEq, resEq, has⟩ := has
      ⟨preF, preArg, preRes, fEq, argEq, resEq, has.mono le⟩
    
    
    -- ## The direct relations on representatives
    
    theorem directHas_mk_iff {lane s e}:
      DirectHas lane ⟦s⟧ ⟦e⟧ ↔ ∃ e', s.Has lane e' ∧ e.IsBisim e'
    :=
      DirectRel_mk_iff
        (st := PreTrisetFn.setoid)
        (Mem := PreTrisetFn.Has)
        (fun h => PreTrisetFn.IsBisim.has h)
    
    theorem directCallHas_mk_iff {lane f a r}:
      DirectCallHas lane ⟦f⟧ ⟦a⟧ ⟦r⟧
        ↔
      ∃ a' r', f.HasEntry lane a' r' ∧ a.IsBisim a' ∧ r.IsBisim r'
    :=
      DirectRel₃_mk_iff
        (st := PreTrisetFn.setoid)
        (R := PreTrisetFn.HasEntry)
        (fun h => PreTrisetFn.IsBisim.hasEntry h)
    
    -- For saturated graphs, the exact code of the argument suffices.
    theorem directCallHas_mk_iff_of_saturated {lane}
      {f a r: PreTrisetFn}
      (sat: f.Saturated)
    :
      DirectCallHas lane ⟦f⟧ ⟦a⟧ ⟦r⟧
        ↔
      ∃ r', f.HasEntry lane a r' ∧ r.IsBisim r'
    :=
      ⟨
        fun h =>
          let ⟨_, _, has, ba, br⟩ := directCallHas_mk_iff.mp h
          let ⟨r'', has', br'⟩ := sat.has ba.symm has
          ⟨r'', has', br.trans br'⟩,
        fun ⟨r', has, br⟩ =>
          directCallHas_mk_iff.mpr ⟨a, r', has, IsBisim.refl a, br⟩,
      ⟩
    
    
    -- ## Extensionality
    
    -- Trisets with the same members are equal.
    theorem eq_of_directMem
      {s t: TrisetFn}
      (sNotFn: ¬ s.IsFn)
      (tNotFn: ¬ t.IsFn)
      (has: ∀ lane e, s.DirectHas lane e ↔ t.DirectHas lane e)
    :
      s = t
    :=
      Quotient.inductionOn₂
        (motive := fun (s t: TrisetFn) =>
          ¬ s.IsFn → ¬ t.IsFn →
          (∀ lane e, s.DirectHas lane e ↔ t.DirectHas lane e) →
          s = t)
        s
        t
        (fun _ _ sNotFn tNotFn has =>
          Quotient.sound
            (isBisim_of_members sNotFn tNotFn
              (fun {lane} e h =>
                directHas_mk_iff.mp
                  ((has lane ⟦e⟧).mp
                    (directHas_mk_iff.mpr ⟨e, h, .refl e⟩)))
              (fun {lane} e h =>
                let ⟨e', h', b⟩ :=
                  directHas_mk_iff.mp
                    ((has lane ⟦e⟧).mpr
                      (directHas_mk_iff.mpr ⟨e, h, .refl e⟩))
                ⟨e', h', b.symm⟩)))
        sNotFn
        tNotFn
        has
    
    -- Functions with the same input-output behavior are equal.
    theorem eq_of_directCall
      {f g: TrisetFn}
      (fFn: f.IsFn)
      (gFn: g.IsFn)
      (has:
        ∀ {lane a r},
        f.DirectCallHas lane a r ↔ g.DirectCallHas lane a r)
    :
      f = g
    :=
      Quotient.inductionOn₂
        (motive := fun (f g: TrisetFn) =>
          f.IsFn → g.IsFn →
          (∀ {lane a r},
            f.DirectCallHas lane a r ↔ g.DirectCallHas lane a r) →
          f = g)
        f
        g
        (fun _ _ fFn gFn has =>
          Quotient.sound
            (isBisim_of_entries fFn gFn
              (fun {_ a r} h =>
                directCallHas_mk_iff.mp
                  (has.mp
                    (directCallHas_mk_iff.mpr
                      ⟨a, r, h, .refl a, .refl r⟩)))
              (fun {_ a r} h =>
                let ⟨a', r', h', ba, br⟩ :=
                  directCallHas_mk_iff.mp
                    (has.mpr
                      (directCallHas_mk_iff.mpr
                        ⟨a, r, h, .refl a, .refl r⟩))
                ⟨a', r', h', ba.symm, br.symm⟩)))
        fFn
        gFn
        has
    
  end TrisetFn
end Pair
