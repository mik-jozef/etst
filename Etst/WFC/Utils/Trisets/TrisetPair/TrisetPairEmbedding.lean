import Etst.WFC.Utils.Trisets.TrisetEmbedding
import Etst.WFC.Utils.Trisets.TrisetPair.TrisetPair

/-
  An embedding of `Triset` into `TrisetPair` (defined internally
  in WFC).
-/

namespace Etst


namespace Pair
  open TrisetEmbedding
  
  namespace PreTriset
    /--
      The embedding on representatives: embed the triset so that its
      members are TrisetPair codes, then wrap it in the `set` constructor.
    -/
    def toPreTrisetPair (t: PreTriset): PreTrisetPair :=
      .set (embed t)
    
    -- The embedding preserves definitive membership.
    def ins_toPreTrisetPair {t e: PreTriset}
      (ins: t.Ins e)
    :
      t.toPreTrisetPair.Ins e.toPreTrisetPair
    :=
      embed_ins ins
    
    -- The embedding preserves possible membership.
    def inw_toPreTrisetPair {t e: PreTriset}
      (inw: t.Inw e)
    :
      t.toPreTrisetPair.Inw e.toPreTrisetPair
    :=
      embed_inw inw
    
    -- Definitive members of an embedding are embeddings.
    def ins_toPreTrisetPair_elim {t: PreTriset} {e: PreTrisetPair}
      (ins: t.toPreTrisetPair.Ins e)
    :
      ∃ e0: PreTriset, t.Ins e0 ∧ e = e0.toPreTrisetPair
    :=
      let ⟨e0, e0In, eq⟩ := embed_elim_def (t := t) (p := e.toPair) ins
      ⟨e0, e0In, PreTrisetPair.toPair_inj (b := toPreTrisetPair e0) eq⟩
    
    -- Possible members of an embedding are embeddings.
    def inw_toPreTrisetPair_elim {t: PreTriset} {e: PreTrisetPair}
      (inw: t.toPreTrisetPair.Inw e)
    :
      ∃ e0: PreTriset, t.Inw e0 ∧ e = e0.toPreTrisetPair
    :=
      let ⟨e0, e0In, eq⟩ := embed_elim_pos (t := t) (p := e.toPair) inw
      ⟨e0, e0In, PreTrisetPair.toPair_inj (b := toPreTrisetPair e0) eq⟩
    
    /-
      If two trisets are bisimilar, so are their embeddings.
    -/
    def toPreTrisetPair_bisim {t t': PreTriset}
      (bisim: t.IsBisim t')
    :
      t.toPreTrisetPair.IsBisim t'.toPreTrisetPair
    :=
      let R (x y: PreTrisetPair): Prop :=
        ∃ t0 t1: PreTriset,
          t0.IsBisim t1 ∧
          x = t0.toPreTrisetPair ∧
          y = t1.toPreTrisetPair
      let symm {x y} (r: R x y): R y x :=
        let ⟨t0, t1, b, xEq, yEq⟩ := r
        ⟨t1, t0, PreTriset.setoid.iseqv.symm b, yEq, xEq⟩
      let sim: PreTrisetPair.transitionSystem.IsSimulation R := fun
        | .ins, _, _, _, ⟨t0, t1, b, rfl, rfl⟩, ins =>
          let ⟨e0, e0In, eEq⟩ := ins_toPreTrisetPair_elim ins
          let ⟨e1, e1In, be⟩ :=
            PreTriset.transitionSystem.IsBisimilar_isSimulation
              .ins t0 t1 e0 b e0In
          ⟨
            e1.toPreTrisetPair,
            ins_toPreTrisetPair e1In,
            e0, e1, be, eEq, rfl,
          ⟩
        | .inw, _, _, _, ⟨t0, t1, b, rfl, rfl⟩, inw =>
          let ⟨e0, e0In, eEq⟩ := inw_toPreTrisetPair_elim inw
          let ⟨e1, e1In, be⟩ :=
            PreTriset.transitionSystem.IsBisimilar_isSimulation
              .inw t0 t1 e0 b e0In
          ⟨
            e1.toPreTrisetPair,
            inw_toPreTrisetPair e1In,
            e0, e1, be, eEq, rfl,
          ⟩
        | .zth, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨_, hEq⟩ =>
          PreTrisetPair.noConfusion hEq
        | .fst, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨_, hEq⟩ =>
          PreTrisetPair.noConfusion hEq
        | .isNull, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨hEq, _⟩ =>
          PreTrisetPair.noConfusion hEq
      ⟨
        R,
        LabeledTransitionSystem.isBisimulation_of_symm symm sim,
        t, t', bisim, rfl, rfl,
      ⟩
    
    /-
      If the embeddings of two trisets are bisimilar, so are the
      trisets themselves.
    -/
    def bisim_of_toPreTrisetPair_bisim {t t': PreTriset}
      (bisim: t.toPreTrisetPair.IsBisim t'.toPreTrisetPair)
    :
      t.IsBisim t'
    :=
      let R (a b: PreTriset): Prop :=
        a.toPreTrisetPair.IsBisim b.toPreTrisetPair
      let sim: PreTriset.transitionSystem.IsSimulation R := fun
        | .ins, _, _, e, rab, ins =>
          let ⟨_, ins', be⟩ :=
            PreTrisetPair.IsBisim.ins rab (ins_toPreTrisetPair ins)
          let ⟨e1, e1In, eq⟩ := ins_toPreTrisetPair_elim ins'
          ⟨
            e1,
            e1In,
            show e.toPreTrisetPair.IsBisim e1.toPreTrisetPair from eq ▸ be,
          ⟩
        | .inw, _, _, e, rab, inw =>
          let ⟨_, inw', be⟩ :=
            PreTrisetPair.IsBisim.inw rab (inw_toPreTrisetPair inw)
          let ⟨e1, e1In, eq⟩ := inw_toPreTrisetPair_elim inw'
          ⟨
            e1,
            e1In,
            show e.toPreTrisetPair.IsBisim e1.toPreTrisetPair from eq ▸ be,
          ⟩
      ⟨
        R,
        LabeledTransitionSystem.isBisimulation_of_symm
          (fun r => PreTrisetPair.setoid.iseqv.symm r)
          sim,
        bisim,
      ⟩
    
  end PreTriset
  
  namespace Triset
    /--
      The embedding of `Triset` into `TrisetPair`: the class of
      a triset index `t` is sent to the class of `set (embed t)`.
    -/
    def toTrisetPair: Triset → TrisetPair :=
      Quotient.lift
        (fun t => ⟦PreTriset.toPreTrisetPair t⟧)
        (fun _ _ bisim =>
          Quot.sound (PreTriset.toPreTrisetPair_bisim bisim))
    
    /-- The embedding applied to a class of an index. -/
    def toTrisetPair_eq (t: PreTriset):
      toTrisetPair ⟦t⟧ = ⟦t.toPreTrisetPair⟧
    :=
      rfl
    
    /-- The embedding is injective. -/
    def toTrisetPair_inj: Function.Injective toTrisetPair :=
      fun a b eq =>
        a.exists_rep.elim fun t aEq =>
        b.exists_rep.elim fun t' bEq => by
          subst aEq
          subst bEq
          exact
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim
                (Quotient.exact eq))
    
    -- The embedding preserves definitive membership (PreTriset version).
    def directIns_toTrisetPair_pre {t e: PreTriset} (ins: t.Ins e):
      (toTrisetPair ⟦t⟧).DirectIns (toTrisetPair ⟦e⟧)
    :=
      ⟨
        t.toPreTrisetPair,
        e.toPreTrisetPair,
        rfl,
        rfl,
        PreTriset.ins_toPreTrisetPair ins,
      ⟩
    
    -- The embedding preserves possible membership (PreTriset version).
    def directInw_toTrisetPair_pre {t e: PreTriset} (inw: t.Inw e):
      (toTrisetPair ⟦t⟧).DirectInw (toTrisetPair ⟦e⟧)
    :=
      ⟨
        t.toPreTrisetPair,
        e.toPreTrisetPair,
        rfl,
        rfl,
        PreTriset.inw_toPreTrisetPair inw,
      ⟩
    
    -- The embedding preserves definitive membership.
    def directIns_toTrisetPair {ts elem: Triset}
      (ins: ts.DirectIns elem)
    :
      ts.toTrisetPair.DirectIns elem.toTrisetPair
    :=
      let ⟨_, _, tsEq, elemEq, ins⟩ := ins
      tsEq ▸ elemEq ▸ directIns_toTrisetPair_pre ins
    
    -- The embedding preserves possible membership.
    def directInw_toTrisetPair {ts elem: Triset}
      (inw: ts.DirectInw elem)
    :
      ts.toTrisetPair.DirectInw elem.toTrisetPair
    :=
      let ⟨_, _, tsEq, elemEq, inw⟩ := inw
      tsEq ▸ elemEq ▸ directInw_toTrisetPair_pre inw
    
    -- The embedding reflects definitive membership.
    def directIns_of_toTrisetPair {ts elem: Triset}
      (ins: ts.toTrisetPair.DirectIns elem.toTrisetPair)
    :
      ts.DirectIns elem
    :=
      Quotient.inductionOn₂
        (motive := fun (ts elem: Triset) =>
          ts.toTrisetPair.DirectIns elem.toTrisetPair → ts.DirectIns elem)
        ts
        elem
        (fun t _ ins =>
          let ⟨_, ins', be⟩ := TrisetPair.directIns_mk_iff.mp ins
          let ⟨e1, e1In, eq⟩ := PreTriset.ins_toPreTrisetPair_elim ins'
          ⟨
            t,
            e1,
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim (eq ▸ be)),
            e1In,
          ⟩)
        ins
    
    -- The embedding reflects possible membership.
    def directInw_of_toTrisetPair {ts elem: Triset}
      (inw: ts.toTrisetPair.DirectInw elem.toTrisetPair)
    :
      ts.DirectInw elem
    :=
      Quotient.inductionOn₂
        (motive := fun (ts elem: Triset) =>
          ts.toTrisetPair.DirectInw elem.toTrisetPair → ts.DirectInw elem)
        ts
        elem
        (fun t _ inw =>
          let ⟨_, inw', be⟩ := TrisetPair.directInw_mk_iff.mp inw
          let ⟨e1, e1In, eq⟩ := PreTriset.inw_toPreTrisetPair_elim inw'
          ⟨
            t,
            e1,
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim (eq ▸ be)),
            e1In,
          ⟩)
        inw
    
    def directIns_iff_toTrisetPair {ts elem: Triset}:
      ts.DirectIns elem ↔ ts.toTrisetPair.DirectIns elem.toTrisetPair
    :=
      ⟨directIns_toTrisetPair, directIns_of_toTrisetPair⟩
    
    def directInw_iff_toTrisetPair {ts elem: Triset}:
      ts.DirectInw elem ↔ ts.toTrisetPair.DirectInw elem.toTrisetPair
    :=
      ⟨directInw_toTrisetPair, directInw_of_toTrisetPair⟩
    
  end Triset
end Pair
