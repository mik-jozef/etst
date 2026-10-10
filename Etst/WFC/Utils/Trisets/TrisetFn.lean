/-
  An extension of `Triset` that includes functional values. See
  `Triset.lean` for context.
  
  A value is either a triset whose members are values, or a function from
  values to values. Function application is definable in WFC using
  `Expr.call` on those codes that are total and bisimilarity-preserving.
  
  Note: I have serious doubts about this approach for functions, as it
  suffers from two issues:
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
-/

import Etst.WFC.Utils.Trisets.Triset

namespace Etst


namespace Pair
  inductive PreTrisetFn where
  | set (ts: PreTriset)
  | fn (graph: PreTriset)
  
  namespace PreTrisetFn
    def toPair: PreTrisetFn → Pair
    | .set ts => .pair (.nat 0) ts
    | .fn graph => .pair (.nat 1) graph
    
    def toPair_inj {a b: PreTrisetFn} (h: a.toPair = b.toPair): a = b :=
      match a, b, h with
      | .set _, .set _, h => congrArg set (Pair.noConfusion h fun _ hr => hr)
      | .fn _, .fn _, h => congrArg fn (Pair.noConfusion h fun _ hr => hr)
    
    def IsFn: PreTrisetFn → Prop
    | fn _ => True
    | set _ => False
    
    def Ins: PreTrisetFn → PreTrisetFn → Prop
    | set ts, e => ts.Ins e.toPair
    | fn _, _ => False
    
    def Inw: PreTrisetFn → PreTrisetFn → Prop
    | set ts, e => ts.Inw e.toPair
    | fn _, _ => False
    
    -- `(a, r)` is a definite entry of the graph of `f`.
    def InsEntry: PreTrisetFn → PreTrisetFn → PreTrisetFn → Prop
    | fn graph, a, r => graph.Ins (.pair a.toPair r.toPair)
    | set _, _, _ => False
    
    -- `(a, r)` is a possible entry of the graph of `f`.
    def InwEntry: PreTrisetFn → PreTrisetFn → PreTrisetFn → Prop
    | fn graph, a, r => graph.Inw (.pair a.toPair r.toPair)
    | set _, _, _ => False
    
    def insLeInw {s e: PreTrisetFn} (ins: s.Ins e): s.Inw e :=
      match s with
      | set _ => Set3.defMem.toPos ins
    
    def insEntryLeInwEntry {f a r: PreTrisetFn}
      (ins: f.InsEntry a r)
    :
      f.InwEntry a r
    :=
      match f with
      | fn _ => Set3.defMem.toPos ins
    
    def not_inwEntry_of_not_isFn {f a r: PreTrisetFn}
      (notFn: ¬ f.IsFn)
      (ins: f.InwEntry a r)
    :
      False
    :=
      match f with
      | fn _ => notFn trivial
    
    def not_inw_of_isFn {s e: PreTrisetFn}
      (isFn: s.IsFn)
      (inw: s.Inw e)
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
    | ins
    | inw
    | insEntry
    | inwEntry
    | arg
    | res
    | isFn -- self loop that distinguishes functions from trisets
    
    inductive Step: TransitionLabels → Node → Node → Prop
    | ins {s e} (h: Ins s e): Step .ins (.val s) (.val e)
    | inw {s e} (h: Inw s e): Step .inw (.val s) (.val e)
    | insEntry {f a r} (h: InsEntry f a r): Step .insEntry (.val f) (.entry a r)
    | inwEntry {f a r} (h: InwEntry f a r): Step .inwEntry (.val f) (.entry a r)
    | arg (a r): Step .arg (.entry a r) (.val a)
    | res (a r): Step .res (.entry a r) (.val r)
    | isFn (graph): Step .isFn (.val (.fn graph)) (.val (.fn graph))
    
    abbrev transitionSystem:
      LabeledTransitionSystem TransitionLabels Node
    :=
      Step
    
    def Step.ofIsFn {v: PreTrisetFn} (isFn: v.IsFn): Step .isFn (.val v) (.val v) :=
      match v with
      | fn graph => .isFn graph
    
    def Step.fromVal {l v x'} (st: Step l (.val v) x'):
      Or (∃ e, l = .ins ∧ x' = .val e ∧ Ins v e) <|
      Or (∃ e, l = .inw ∧ x' = .val e ∧ Inw v e) <|
      Or (∃ a r, l = .insEntry ∧ x' = .entry a r ∧ InsEntry v a r) <|
      Or (∃ a r, l = .inwEntry ∧ x' = .entry a r ∧ InwEntry v a r)
        (l = .isFn ∧ x' = .val v ∧ IsFn v)
    :=
      match st with
      | .ins h => .inl ⟨_, rfl, rfl, h⟩
      | .inw h => .inr (.inl ⟨_, rfl, rfl, h⟩)
      | .insEntry h => .inr (.inr (.inl ⟨_, _, rfl, rfl, h⟩))
      | .inwEntry h => .inr (.inr (.inr (.inl ⟨_, _, rfl, rfl, h⟩)))
      | .isFn _ => .inr (.inr (.inr (.inr ⟨rfl, rfl, trivial⟩)))
    
    def Step.fromEntry {l a r x'} (st: Step l (.entry a r) x'):
      Or (l = .arg ∧ x' = .val a) (l = .res ∧ x' = .val r)
    :=
      match st with
      | .arg _ _ => .inl ⟨rfl, rfl⟩
      | .res _ _ => .inr ⟨rfl, rfl⟩
    
    def IsBisim (a b: PreTrisetFn): Prop :=
      transitionSystem.IsBisimilar (.val a) (.val b)
    
    def IsBisim.refl (a: PreTrisetFn): a.IsBisim a :=
      transitionSystem.IsBisimilar_is_equivalence.refl _
    
    def IsBisim.symm {a b: PreTrisetFn} (h: a.IsBisim b): b.IsBisim a :=
      transitionSystem.IsBisimilar_is_equivalence.symm h
    
    def IsBisim.trans {a b c: PreTrisetFn}
      (h0: a.IsBisim b)
      (h1: b.IsBisim c)
    :
      a.IsBisim c
    :=
      transitionSystem.IsBisimilar_is_equivalence.trans h0 h1
    
    def setoid: Setoid PreTrisetFn where
      r := IsBisim
      iseqv := ⟨IsBisim.refl, IsBisim.symm, IsBisim.trans⟩
    
    
    /-
      Two nodes are bisimilar if their steps match, landing either in
      bisimilar nodes, or back in the pair itself.
    -/
    def isBisimilar_of_steps {x0 y0: Node}
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
    
    def isBisimilar_entry {a a' r r': PreTrisetFn}
      (ha: a.IsBisim a')
      (hr: r.IsBisim r')
    :
      transitionSystem.IsBisimilar (.entry a r) (.entry a' r')
    :=
      isBisimilar_of_steps
        (fun l x' st =>
          match l, x', Step.fromEntry st with
          | _, _, .inl ⟨rfl, rfl⟩ => ⟨_, .arg a' r', .inl ha⟩
          | _, _, .inr ⟨rfl, rfl⟩ => ⟨_, .res a' r', .inl hr⟩)
        (fun l y' st =>
          match l, y', Step.fromEntry st with
          | _, _, .inl ⟨rfl, rfl⟩ => ⟨_, .arg a r, .inl ha⟩
          | _, _, .inr ⟨rfl, rfl⟩ => ⟨_, .res a r, .inl hr⟩)
    
    def IsBisim.entryArg {a r a' r': PreTrisetFn}
      (h: transitionSystem.IsBisimilar (.entry a r) (.entry a' r'))
    :
      a.IsBisim a'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation .arg _ _ _ h (.arg a r)
      match y', Step.fromEntry st, hy with
      | _, .inl ⟨_, rfl⟩, hy => hy
    
    def IsBisim.entryRes {a r a' r': PreTrisetFn}
      (h: transitionSystem.IsBisimilar (.entry a r) (.entry a' r'))
    :
      r.IsBisim r'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation .res _ _ _ h (.res a r)
      match y', Step.fromEntry st, hy with
      | _, .inr ⟨_, rfl⟩, hy => hy
    
    
    -- ## Bisimilar values have matching members, entries and kinds
    
    def IsBisim.ins {s s' e: PreTrisetFn}
      (b: s.IsBisim s')
      (ins: s.Ins e)
    :
      ∃ e', s'.Ins e' ∧ e.IsBisim e'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation .ins _ _ _ b (.ins ins)
      match y', Step.fromVal st, hy with
      | _, .inl ⟨e', _, rfl, ins'⟩, hy => ⟨e', ins', hy⟩
    
    def IsBisim.inw {s s' e: PreTrisetFn}
      (b: s.IsBisim s')
      (inw: s.Inw e)
    :
      ∃ e', s'.Inw e' ∧ e.IsBisim e'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation .inw _ _ _ b (.inw inw)
      match y', Step.fromVal st, hy with
      | _, .inr (.inl ⟨e', _, rfl, inw'⟩), hy => ⟨e', inw', hy⟩
    
    def IsBisim.insEntry {f f' a r: PreTrisetFn}
      (b: f.IsBisim f')
      (ins: f.InsEntry a r)
    :
      ∃ a' r', f'.InsEntry a' r' ∧ a.IsBisim a' ∧ r.IsBisim r'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation
          .insEntry _ _ _ b (.insEntry ins)
      match y', Step.fromVal st, hy with
      | _, .inr (.inr (.inl ⟨a', r', _, rfl, ins'⟩)), hy =>
        ⟨a', r', ins', IsBisim.entryArg hy, IsBisim.entryRes hy⟩
    
    def IsBisim.inwEntry {f f' a r: PreTrisetFn}
      (b: f.IsBisim f')
      (inw: f.InwEntry a r)
    :
      ∃ a' r', f'.InwEntry a' r' ∧ a.IsBisim a' ∧ r.IsBisim r'
    :=
      let ⟨y', st, hy⟩ :=
        transitionSystem.IsBisimilar_isSimulation
          .inwEntry _ _ _ b (.inwEntry inw)
      match y', Step.fromVal st, hy with
      | _, .inr (.inr (.inr (.inl ⟨a', r', _, rfl, inw'⟩))), hy =>
        ⟨a', r', inw', IsBisim.entryArg hy, IsBisim.entryRes hy⟩
    
    def IsBisim.isFn {v v': PreTrisetFn}
      (b: v.IsBisim v')
      (isFn: v.IsFn)
    :
      v'.IsFn
    :=
      let ⟨_, st, _⟩ :=
        transitionSystem.IsBisimilar_isSimulation
          .isFn _ _ _ b (Step.ofIsFn isFn)
      match Step.fromVal st with
      | .inr (.inr (.inr (.inr ⟨_, _, isFn'⟩))) => isFn'
    
    
    -- ## Extensionality on representatives
    
    def isBisim_of_members {s t: PreTrisetFn}
      (sNotFn: ¬ s.IsFn)
      (tNotFn: ¬ t.IsFn)
      (insST: ∀ e, s.Ins e → ∃ e', t.Ins e' ∧ e.IsBisim e')
      (insTS: ∀ e, t.Ins e → ∃ e', s.Ins e' ∧ e'.IsBisim e)
      (inwST: ∀ e, s.Inw e → ∃ e', t.Inw e' ∧ e.IsBisim e')
      (inwTS: ∀ e, t.Inw e → ∃ e', s.Inw e' ∧ e'.IsBisim e)
    :
      s.IsBisim t
    :=
      isBisimilar_of_steps
        (fun l x' st =>
          match l, x', Step.fromVal st with
          | _, _, .inl ⟨e, rfl, rfl, ins⟩ =>
            let ⟨_, ins', b⟩ := insST e ins
            ⟨_, .ins ins', .inl b⟩
          | _, _, .inr (.inl ⟨e, rfl, rfl, inw⟩) =>
            let ⟨_, inw', b⟩ := inwST e inw
            ⟨_, .inw inw', .inl b⟩
          | _, _, .inr (.inr (.inl ⟨_, _, _, _, ins⟩)) =>
            (not_inwEntry_of_not_isFn sNotFn (insEntryLeInwEntry ins)).elim
          | _, _, .inr (.inr (.inr (.inl ⟨_, _, _, _, inw⟩))) =>
            (not_inwEntry_of_not_isFn sNotFn inw).elim
          | _, _, .inr (.inr (.inr (.inr ⟨_, _, isFn⟩))) =>
            (sNotFn isFn).elim)
        (fun l y' st =>
          match l, y', Step.fromVal st with
          | _, _, .inl ⟨e, rfl, rfl, ins⟩ =>
            let ⟨_, ins', b⟩ := insTS e ins
            ⟨_, .ins ins', .inl b⟩
          | _, _, .inr (.inl ⟨e, rfl, rfl, inw⟩) =>
            let ⟨_, inw', b⟩ := inwTS e inw
            ⟨_, .inw inw', .inl b⟩
          | _, _, .inr (.inr (.inl ⟨_, _, _, _, ins⟩)) =>
            (not_inwEntry_of_not_isFn tNotFn (insEntryLeInwEntry ins)).elim
          | _, _, .inr (.inr (.inr (.inl ⟨_, _, _, _, inw⟩))) =>
            (not_inwEntry_of_not_isFn tNotFn inw).elim
          | _, _, .inr (.inr (.inr (.inr ⟨_, _, isFn⟩))) =>
            (tNotFn isFn).elim)
    
    def isBisim_of_entries {f g: PreTrisetFn}
      (fFn: f.IsFn)
      (gFn: g.IsFn)
      (insFG:
        ∀ a r, f.InsEntry a r →
        ∃ a' r', g.InsEntry a' r' ∧ a.IsBisim a' ∧ r.IsBisim r')
      (insGF:
        ∀ a r, g.InsEntry a r →
        ∃ a' r', f.InsEntry a' r' ∧ a'.IsBisim a ∧ r'.IsBisim r)
      (inwFG:
        ∀ a r, f.InwEntry a r →
        ∃ a' r', g.InwEntry a' r' ∧ a.IsBisim a' ∧ r.IsBisim r')
      (inwGF:
        ∀ a r, g.InwEntry a r →
        ∃ a' r', f.InwEntry a' r' ∧ a'.IsBisim a ∧ r'.IsBisim r)
    :
      f.IsBisim g
    :=
      isBisimilar_of_steps
        (fun l x' st =>
          match l, x', Step.fromVal st with
          | _, _, .inl ⟨_, _, _, ins⟩ =>
            (not_inw_of_isFn fFn (insLeInw ins)).elim
          | _, _, .inr (.inl ⟨_, _, _, inw⟩) =>
            (not_inw_of_isFn fFn inw).elim
          | _, _, .inr (.inr (.inl ⟨a, r, rfl, rfl, ins⟩)) =>
            let ⟨_, _, ins', ba, br⟩ := insFG a r ins
            ⟨_, .insEntry ins', .inl (isBisimilar_entry ba br)⟩
          | _, _, .inr (.inr (.inr (.inl ⟨a, r, rfl, rfl, inw⟩))) =>
            let ⟨_, _, inw', ba, br⟩ := inwFG a r inw
            ⟨_, .inwEntry inw', .inl (isBisimilar_entry ba br)⟩
          | _, _, .inr (.inr (.inr (.inr ⟨rfl, rfl, _⟩))) =>
            ⟨_, Step.ofIsFn gFn, .inr ⟨rfl, rfl⟩⟩)
        (fun l y' st =>
          match l, y', Step.fromVal st with
          | _, _, .inl ⟨_, _, _, ins⟩ =>
            (not_inw_of_isFn gFn (insLeInw ins)).elim
          | _, _, .inr (.inl ⟨_, _, _, inw⟩) =>
            (not_inw_of_isFn gFn inw).elim
          | _, _, .inr (.inr (.inl ⟨a, r, rfl, rfl, ins⟩)) =>
            let ⟨_, _, ins', ba, br⟩ := insGF a r ins
            ⟨_, .insEntry ins', .inl (isBisimilar_entry ba br)⟩
          | _, _, .inr (.inr (.inr (.inl ⟨a, r, rfl, rfl, inw⟩))) =>
            let ⟨_, _, inw', ba, br⟩ := inwGF a r inw
            ⟨_, .inwEntry inw', .inl (isBisimilar_entry ba br)⟩
          | _, _, .inr (.inr (.inr (.inr ⟨rfl, rfl, _⟩))) =>
            ⟨_, Step.ofIsFn fFn, .inr ⟨rfl, rfl⟩⟩)
    
    
    /-
      A graph is saturated if bisimilar arguments have bisimilar results.
      For saturated graphs, looking up the exact code of the argument
      (ie. `Expr.call`) computes the application.
    -/
    structure Saturated (f: PreTrisetFn): Prop where
      ins:
        ∀ {a a' r}, a.IsBisim a' → f.InsEntry a r →
        ∃ r', f.InsEntry a' r' ∧ r.IsBisim r'
      inw:
        ∀ {a a' r}, a.IsBisim a' → f.InwEntry a r →
        ∃ r', f.InwEntry a' r' ∧ r.IsBisim r'
    
    def insEntry_iff_call {graph a r: PreTrisetFn}:
      (fn graph.toPair).InsEntry a r
        ↔
      ((uniSetMap.call graph.toPair).call a.toPair).defMem r.toPair
    :=
      Iff.rfl
    
    def inwEntry_iff_call {graph a r: PreTrisetFn}:
      (fn graph.toPair).InwEntry a r
        ↔
      ((uniSetMap.call graph.toPair).call a.toPair).posMem r.toPair
    :=
      Iff.rfl
    
  end PreTrisetFn
  
  
  def TrisetFn := Quotient PreTrisetFn.setoid
  
  namespace TrisetFn
    open PreTrisetFn
    
    def IsFn: TrisetFn → Prop :=
      Quotient.lift PreTrisetFn.IsFn fun _ _ b =>
        propext ⟨IsBisim.isFn b, IsBisim.isFn (IsBisim.symm b)⟩
    
    -- `ts` is a triset with a definite member `elem`.
    def DirectIns (ts elem: TrisetFn): Prop :=
      DirectRel PreTrisetFn.Ins ts elem
    
    -- `ts` is a triset with a possible member `elem`.
    def DirectInw (ts elem: TrisetFn): Prop :=
      DirectRel PreTrisetFn.Inw ts elem
    
    def DirectMem: TriRelation TrisetFn where
      RelDef := DirectIns
      RelPos := DirectInw
      def_le_pos
      | ⟨preTs, preElem, ⟨tsEq, elemEq, ins⟩⟩ =>
        ⟨preTs, preElem, ⟨tsEq, elemEq, insLeInw ins⟩⟩
    
    -- `res` is a definite member of the result of applying `f` to `arg`.
    def DirectCallIns (f arg res: TrisetFn): Prop :=
      DirectRel₃ PreTrisetFn.InsEntry f arg res
    
    -- `res` is a possible member of the result of applying `f` to `arg`.
    def DirectCallInw (f arg res: TrisetFn): Prop :=
      DirectRel₃ PreTrisetFn.InwEntry f arg res
    
    def DirectCallIns.toInw {f arg res: TrisetFn}
      (ins: f.DirectCallIns arg res)
    :
      f.DirectCallInw arg res
    :=
      let ⟨preF, preArg, preRes, fEq, argEq, resEq, ins⟩ := ins
      ⟨preF, preArg, preRes, fEq, argEq, resEq, insEntryLeInwEntry ins⟩
    
    
    -- ## The direct relations on representatives
    
    def directIns_mk_iff {s e: PreTrisetFn}:
      DirectIns ⟦s⟧ ⟦e⟧ ↔ ∃ e', s.Ins e' ∧ e.IsBisim e'
    :=
      ⟨
        fun ⟨_, _, sEq, eEq, ins⟩ =>
          let sB: s.IsBisim _ := Quotient.exact sEq
          let eB: e.IsBisim _ := Quotient.exact eEq
          let ⟨e', ins', b⟩ := sB.symm.ins ins
          ⟨e', ins', eB.trans b⟩,
        fun ⟨e', ins', b⟩ => ⟨s, e', rfl, Quotient.sound b, ins'⟩,
      ⟩
    
    def directInw_mk_iff {s e: PreTrisetFn}:
      DirectInw ⟦s⟧ ⟦e⟧ ↔ ∃ e', s.Inw e' ∧ e.IsBisim e'
    :=
      ⟨
        fun ⟨_, _, sEq, eEq, inw⟩ =>
          let sB: s.IsBisim _ := Quotient.exact sEq
          let eB: e.IsBisim _ := Quotient.exact eEq
          let ⟨e', inw', b⟩ := sB.symm.inw inw
          ⟨e', inw', eB.trans b⟩,
        fun ⟨e', inw', b⟩ => ⟨s, e', rfl, Quotient.sound b, inw'⟩,
      ⟩
    
    def directCallIns_mk_iff {f a r: PreTrisetFn}:
      DirectCallIns ⟦f⟧ ⟦a⟧ ⟦r⟧
        ↔
      ∃ a' r', f.InsEntry a' r' ∧ a.IsBisim a' ∧ r.IsBisim r'
    :=
      ⟨
        fun ⟨_, _, _, fEq, aEq, rEq, ins⟩ =>
          let fB: f.IsBisim _ := Quotient.exact fEq
          let aB: a.IsBisim _ := Quotient.exact aEq
          let rB: r.IsBisim _ := Quotient.exact rEq
          let ⟨a', r', ins', ba, br⟩ := fB.symm.insEntry ins
          ⟨a', r', ins', aB.trans ba, rB.trans br⟩,
        fun ⟨a', r', ins', ba, br⟩ =>
          ⟨f, a', r', rfl, Quotient.sound ba, Quotient.sound br, ins'⟩,
      ⟩
    
    def directCallInw_mk_iff {f a r: PreTrisetFn}:
      DirectCallInw ⟦f⟧ ⟦a⟧ ⟦r⟧
        ↔
      ∃ a' r', f.InwEntry a' r' ∧ a.IsBisim a' ∧ r.IsBisim r'
    :=
      ⟨
        fun ⟨_, _, _, fEq, aEq, rEq, inw⟩ =>
          let fB: f.IsBisim _ := Quotient.exact fEq
          let aB: a.IsBisim _ := Quotient.exact aEq
          let rB: r.IsBisim _ := Quotient.exact rEq
          let ⟨a', r', inw', ba, br⟩ := fB.symm.inwEntry inw
          ⟨a', r', inw', aB.trans ba, rB.trans br⟩,
        fun ⟨a', r', inw', ba, br⟩ =>
          ⟨f, a', r', rfl, Quotient.sound ba, Quotient.sound br, inw'⟩,
      ⟩
    
    -- For saturated graphs, the exact code of the argument suffices.
    def directCallIns_mk_iff_of_saturated {f a r: PreTrisetFn}
      (sat: f.Saturated)
    :
      DirectCallIns ⟦f⟧ ⟦a⟧ ⟦r⟧ ↔ ∃ r', f.InsEntry a r' ∧ r.IsBisim r'
    :=
      ⟨
        fun h =>
          let ⟨_, _, ins, ba, br⟩ := directCallIns_mk_iff.mp h
          let ⟨r'', ins', br'⟩ := sat.ins ba.symm ins
          ⟨r'', ins', br.trans br'⟩,
        fun ⟨r', ins, br⟩ =>
          directCallIns_mk_iff.mpr ⟨a, r', ins, IsBisim.refl a, br⟩,
      ⟩
    
    def directCallInw_mk_iff_of_saturated {f a r: PreTrisetFn}
      (sat: f.Saturated)
    :
      DirectCallInw ⟦f⟧ ⟦a⟧ ⟦r⟧ ↔ ∃ r', f.InwEntry a r' ∧ r.IsBisim r'
    :=
      ⟨
        fun h =>
          let ⟨_, _, inw, ba, br⟩ := directCallInw_mk_iff.mp h
          let ⟨r'', inw', br'⟩ := sat.inw ba.symm inw
          ⟨r'', inw', br.trans br'⟩,
        fun ⟨r', inw, br⟩ =>
          directCallInw_mk_iff.mpr ⟨a, r', inw, IsBisim.refl a, br⟩,
      ⟩
    
    
    -- ## Extensionality
    
    -- Trisets with the same members are equal.
    def eq_of_directMem {s t: TrisetFn}
      (sNotFn: ¬ s.IsFn)
      (tNotFn: ¬ t.IsFn)
      (ins: ∀ e, s.DirectIns e ↔ t.DirectIns e)
      (inw: ∀ e, s.DirectInw e ↔ t.DirectInw e)
    :
      s = t
    :=
      Quotient.inductionOn₂
        (motive := fun (s t: TrisetFn) =>
          ¬ s.IsFn → ¬ t.IsFn →
          (∀ e, s.DirectIns e ↔ t.DirectIns e) →
          (∀ e, s.DirectInw e ↔ t.DirectInw e) →
          s = t)
        s
        t
        (fun _ _ sNotFn tNotFn ins inw =>
          Quotient.sound
            (isBisim_of_members sNotFn tNotFn
              (fun e h =>
                directIns_mk_iff.mp
                  ((ins ⟦e⟧).mp (directIns_mk_iff.mpr ⟨e, h, .refl e⟩)))
              (fun e h =>
                let ⟨e', h', b⟩ :=
                  directIns_mk_iff.mp
                    ((ins ⟦e⟧).mpr (directIns_mk_iff.mpr ⟨e, h, .refl e⟩))
                ⟨e', h', b.symm⟩)
              (fun e h =>
                directInw_mk_iff.mp
                  ((inw ⟦e⟧).mp (directInw_mk_iff.mpr ⟨e, h, .refl e⟩)))
              (fun e h =>
                let ⟨e', h', b⟩ :=
                  directInw_mk_iff.mp
                    ((inw ⟦e⟧).mpr (directInw_mk_iff.mpr ⟨e, h, .refl e⟩))
                ⟨e', h', b.symm⟩)))
        sNotFn
        tNotFn
        ins
        inw
    
    -- Functions with the same input-output behavior are equal.
    def eq_of_directCall {f g: TrisetFn}
      (fFn: f.IsFn)
      (gFn: g.IsFn)
      (ins: ∀ a r, f.DirectCallIns a r ↔ g.DirectCallIns a r)
      (inw: ∀ a r, f.DirectCallInw a r ↔ g.DirectCallInw a r)
    :
      f = g
    :=
      Quotient.inductionOn₂
        (motive := fun (f g: TrisetFn) =>
          f.IsFn → g.IsFn →
          (∀ a r, f.DirectCallIns a r ↔ g.DirectCallIns a r) →
          (∀ a r, f.DirectCallInw a r ↔ g.DirectCallInw a r) →
          f = g)
        f
        g
        (fun _ _ fFn gFn ins inw =>
          Quotient.sound
            (isBisim_of_entries fFn gFn
              (fun a r h =>
                directCallIns_mk_iff.mp
                  ((ins ⟦a⟧ ⟦r⟧).mp
                    (directCallIns_mk_iff.mpr
                      ⟨a, r, h, .refl a, .refl r⟩)))
              (fun a r h =>
                let ⟨a', r', h', ba, br⟩ :=
                  directCallIns_mk_iff.mp
                    ((ins ⟦a⟧ ⟦r⟧).mpr
                      (directCallIns_mk_iff.mpr
                        ⟨a, r, h, .refl a, .refl r⟩))
                ⟨a', r', h', ba.symm, br.symm⟩)
              (fun a r h =>
                directCallInw_mk_iff.mp
                  ((inw ⟦a⟧ ⟦r⟧).mp
                    (directCallInw_mk_iff.mpr
                      ⟨a, r, h, .refl a, .refl r⟩)))
              (fun a r h =>
                let ⟨a', r', h', ba, br⟩ :=
                  directCallInw_mk_iff.mp
                    ((inw ⟦a⟧ ⟦r⟧).mpr
                      (directCallInw_mk_iff.mpr
                        ⟨a, r, h, .refl a, .refl r⟩))
                ⟨a', r', h', ba.symm, br.symm⟩)))
        fFn
        gFn
        ins
        inw
    
  end TrisetFn
end Pair
