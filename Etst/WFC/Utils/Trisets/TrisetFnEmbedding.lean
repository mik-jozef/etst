import Etst.WFC.Utils.Trisets.TrisetFn
import Etst.WFC.Utils.Trisets.TrisetEmbedding

/-
  An embedding of `Triset` into `TrisetFn`. The triset `t` is sent to
  `set (embed t)`, whose members are again embedded trisets.
-/

namespace Etst


namespace Pair
  open TrisetEmbedding
  
  namespace PreTriset
    def toPreTrisetFn (t: PreTriset): PreTrisetFn := .set (embed t)
    
    def not_isFn_toPreTrisetFn (t: PreTriset): ¬ t.toPreTrisetFn.IsFn :=
      id
    
    -- The embedding preserves definitive membership.
    def ins_toPreTrisetFn {t e: PreTriset}
      (ins: t.Ins e)
    :
      t.toPreTrisetFn.Ins e.toPreTrisetFn
    :=
      embed_ins ins
    
    -- The embedding preserves possible membership.
    def inw_toPreTrisetFn {t e: PreTriset}
      (inw: t.Inw e)
    :
      t.toPreTrisetFn.Inw e.toPreTrisetFn
    :=
      embed_inw inw
    
    -- Definitive members of an embedding are embeddings.
    def ins_toPreTrisetFn_elim {t: PreTriset} {e: PreTrisetFn}
      (ins: t.toPreTrisetFn.Ins e)
    :
      ∃ e0: PreTriset, t.Ins e0 ∧ e = e0.toPreTrisetFn
    :=
      let ⟨e0, e0In, eq⟩ := embed_elim_def (t := t) (p := e.toPair) ins
      ⟨e0, e0In, PreTrisetFn.toPair_inj (b := toPreTrisetFn e0) eq⟩
    
    -- Possible members of an embedding are embeddings.
    def inw_toPreTrisetFn_elim {t: PreTriset} {e: PreTrisetFn}
      (inw: t.toPreTrisetFn.Inw e)
    :
      ∃ e0: PreTriset, t.Inw e0 ∧ e = e0.toPreTrisetFn
    :=
      let ⟨e0, e0In, eq⟩ := embed_elim_pos (t := t) (p := e.toPair) inw
      ⟨e0, e0In, PreTrisetFn.toPair_inj (b := toPreTrisetFn e0) eq⟩
    
    -- If two trisets are bisimilar, so are their embeddings.
    def toPreTrisetFn_bisim {t t': PreTriset}
      (bisim: t.IsBisim t')
    :
      t.toPreTrisetFn.IsBisim t'.toPreTrisetFn
    :=
      let R (x y: PreTrisetFn.Node): Prop :=
        ∃ t0 t1: PreTriset,
          t0.IsBisim t1 ∧
          x = .val t0.toPreTrisetFn ∧
          y = .val t1.toPreTrisetFn
      let symm {x y} (r: R x y): R y x :=
        let ⟨t0, t1, b, xEq, yEq⟩ := r
        ⟨t1, t0, PreTriset.setoid.iseqv.symm b, yEq, xEq⟩
      let sim: PreTrisetFn.transitionSystem.IsSimulation R := fun
        | l, _, _, x', ⟨t0, t1, b, rfl, rfl⟩, st =>
          match l, x', PreTrisetFn.Step.fromVal st with
          | _, _, .inl ⟨_, rfl, rfl, ins⟩ =>
            let ⟨e0, e0In, eEq⟩ := ins_toPreTrisetFn_elim ins
            let ⟨e1, e1In, be⟩ :=
              PreTriset.transitionSystem.IsBisimilar_isSimulation
                .ins t0 t1 e0 b e0In
            ⟨
              _,
              .ins (ins_toPreTrisetFn (t := t1) (e := e1) e1In),
              e0, e1, be, congrArg _ eEq, rfl,
            ⟩
          | _, _, .inr (.inl ⟨_, rfl, rfl, inw⟩) =>
            let ⟨e0, e0In, eEq⟩ := inw_toPreTrisetFn_elim inw
            let ⟨e1, e1In, be⟩ :=
              PreTriset.transitionSystem.IsBisimilar_isSimulation
                .inw t0 t1 e0 b e0In
            ⟨
              _,
              .inw (inw_toPreTrisetFn (t := t1) (e := e1) e1In),
              e0, e1, be, congrArg _ eEq, rfl,
            ⟩
          | _, _, .inr (.inr (.inl ⟨_, _, _, _, ins⟩)) => ins.elim
          | _, _, .inr (.inr (.inr (.inl ⟨_, _, _, _, inw⟩))) => inw.elim
          | _, _, .inr (.inr (.inr (.inr ⟨_, _, isFn⟩))) => isFn.elim
      ⟨
        R,
        LabeledTransitionSystem.isBisimulation_of_symm symm sim,
        t, t', bisim, rfl, rfl,
      ⟩
    
    -- If the embeddings of two trisets are bisimilar, so are the trisets.
    def bisim_of_toPreTrisetFn_bisim {t t': PreTriset}
      (bisim: t.toPreTrisetFn.IsBisim t'.toPreTrisetFn)
    :
      t.IsBisim t'
    :=
      let R (a b: PreTriset): Prop :=
        a.toPreTrisetFn.IsBisim b.toPreTrisetFn
      let sim: PreTriset.transitionSystem.IsSimulation R := fun
        | .ins, _, _, e, rab, ins =>
          let ⟨_, ins', be⟩ := PreTrisetFn.IsBisim.ins rab (ins_toPreTrisetFn ins)
          let ⟨e1, e1In, eq⟩ := ins_toPreTrisetFn_elim ins'
          ⟨
            e1,
            e1In,
            show e.toPreTrisetFn.IsBisim e1.toPreTrisetFn from eq ▸ be,
          ⟩
        | .inw, _, _, e, rab, inw =>
          let ⟨_, inw', be⟩ := PreTrisetFn.IsBisim.inw rab (inw_toPreTrisetFn inw)
          let ⟨e1, e1In, eq⟩ := inw_toPreTrisetFn_elim inw'
          ⟨
            e1,
            e1In,
            show e.toPreTrisetFn.IsBisim e1.toPreTrisetFn from eq ▸ be,
          ⟩
      ⟨
        R,
        LabeledTransitionSystem.isBisimulation_of_symm
          (fun r => PreTrisetFn.IsBisim.symm r)
          sim,
        bisim,
      ⟩
    
  end PreTriset
  
  namespace Triset
    def toTrisetFn: Triset → TrisetFn :=
      Quotient.lift
        (fun t => ⟦t.toPreTrisetFn⟧)
        (fun _ _ bisim =>
          Quotient.sound (PreTriset.toPreTrisetFn_bisim bisim))
    
    def toTrisetFn_inj: Function.Injective toTrisetFn :=
      fun a b eq =>
        a.exists_rep.elim fun t aEq =>
        b.exists_rep.elim fun t' bEq => by
          subst aEq
          subst bEq
          exact
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetFn_bisim (Quotient.exact eq))
    
    def not_isFn_toTrisetFn (ts: Triset): ¬ ts.toTrisetFn.IsFn :=
      Quotient.inductionOn
        (motive := fun (ts: Triset) => ¬ ts.toTrisetFn.IsFn)
        ts
        PreTriset.not_isFn_toPreTrisetFn
    
    -- The embedding preserves definitive membership.
    def directIns_toTrisetFn {ts elem: Triset}
      (ins: ts.DirectIns elem)
    :
      ts.toTrisetFn.DirectIns elem.toTrisetFn
    :=
      let ⟨t, e, tsEq, elemEq, ins⟩ := ins
      tsEq ▸ elemEq ▸
        ⟨t.toPreTrisetFn, e.toPreTrisetFn, rfl, rfl, PreTriset.ins_toPreTrisetFn ins⟩
    
    -- The embedding preserves possible membership.
    def directInw_toTrisetFn {ts elem: Triset}
      (inw: ts.DirectInw elem)
    :
      ts.toTrisetFn.DirectInw elem.toTrisetFn
    :=
      let ⟨t, e, tsEq, elemEq, inw⟩ := inw
      tsEq ▸ elemEq ▸
        ⟨t.toPreTrisetFn, e.toPreTrisetFn, rfl, rfl, PreTriset.inw_toPreTrisetFn inw⟩
    
    -- The embedding reflects definitive membership.
    def directIns_of_toTrisetFn {ts elem: Triset}
      (ins: ts.toTrisetFn.DirectIns elem.toTrisetFn)
    :
      ts.DirectIns elem
    :=
      Quotient.inductionOn₂
        (motive := fun (ts elem: Triset) =>
          ts.toTrisetFn.DirectIns elem.toTrisetFn → ts.DirectIns elem)
        ts
        elem
        (fun t _ ins =>
          let ⟨_, ins', be⟩ := TrisetFn.directIns_mk_iff.mp ins
          let ⟨e1, e1In, eq⟩ := PreTriset.ins_toPreTrisetFn_elim ins'
          ⟨
            t,
            e1,
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetFn_bisim (eq ▸ be)),
            e1In,
          ⟩)
        ins
    
    -- The embedding reflects possible membership.
    def directInw_of_toTrisetFn {ts elem: Triset}
      (inw: ts.toTrisetFn.DirectInw elem.toTrisetFn)
    :
      ts.DirectInw elem
    :=
      Quotient.inductionOn₂
        (motive := fun (ts elem: Triset) =>
          ts.toTrisetFn.DirectInw elem.toTrisetFn → ts.DirectInw elem)
        ts
        elem
        (fun t _ inw =>
          let ⟨_, inw', be⟩ := TrisetFn.directInw_mk_iff.mp inw
          let ⟨e1, e1In, eq⟩ := PreTriset.inw_toPreTrisetFn_elim inw'
          ⟨
            t,
            e1,
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetFn_bisim (eq ▸ be)),
            e1In,
          ⟩)
        inw
    
    def directIns_iff_toTrisetFn {ts elem: Triset}:
      ts.DirectIns elem ↔ ts.toTrisetFn.DirectIns elem.toTrisetFn
    :=
      ⟨directIns_toTrisetFn, directIns_of_toTrisetFn⟩
    
    def directInw_iff_toTrisetFn {ts elem: Triset}:
      ts.DirectInw elem ↔ ts.toTrisetFn.DirectInw elem.toTrisetFn
    :=
      ⟨directInw_toTrisetFn, directInw_of_toTrisetFn⟩
    
  end Triset
end Pair
