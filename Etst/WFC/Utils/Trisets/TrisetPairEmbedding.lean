import Etst.WFC.Utils.Trisets.TrisetPair
import Etst.WFC.Utils.Trisets.TrisetEmbedding

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
    
    /-
      If two trisets are bisimilar, so are their embeddings.
    -/
    def toPreTrisetPair_bisim {t t': PreTriset}
      (bisim: t.IsBisim t')
    :
      t.toPreTrisetPair.IsBisim t'.toPreTrisetPair
    :=
      let ⟨R, ⟨simLR, simRL⟩, r⟩ := bisim
      let R': PreTrisetPair → PreTrisetPair → Prop :=
        fun a b =>
          ∃ t0 t1: PreTriset,
            R t0 t1
              ∧
            a = t0.toPreTrisetPair
              ∧
            b = t1.toPreTrisetPair
      let simL: PreTrisetPair.transitionSystem.IsSimulation R' := fun
        | .zth, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨_, hEq⟩ =>
          PreTrisetPair.noConfusion hEq
        | .fst, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨_, hEq⟩ =>
          PreTrisetPair.noConfusion hEq
        | .isNull, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨hEq, _⟩ =>
          PreTrisetPair.noConfusion hEq
        | .ins, _, _, el, ⟨t0, t1, r01, rfl, rfl⟩, ins =>
          let ⟨e0, e0In, e0Eq⟩ :=
            embed_elim_def (show Ins (embed t0) el.toPair from ins)
          let ⟨e1, e1In, rE⟩ := simLR .ins t0 t1 e0 r01 e0In
          ⟨
            e1.toPreTrisetPair,
            embed_ins e1In,
            e0,
            e1,
            rE,
            PreTrisetPair.toPair_inj e0Eq,
            rfl
          ⟩
        | .inw, _, _, el, ⟨t0, t1, r01, rfl, rfl⟩, inw =>
          let ⟨e0, e0In, e0Eq⟩ :=
            embed_elim_pos (show Inw (embed t0) el.toPair from inw)
          let ⟨e1, e1In, rE⟩ := simLR .inw t0 t1 e0 r01 e0In
          ⟨
            e1.toPreTrisetPair,
            embed_inw e1In,
            e0,
            e1,
            rE,
            PreTrisetPair.toPair_inj e0Eq,
            rfl
          ⟩
      let simR:
        PreTrisetPair.transitionSystem.IsSimulation (Function.swap R')
      := fun
        | .zth, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨_, hEq⟩ =>
          PreTrisetPair.noConfusion hEq
        | .fst, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨_, hEq⟩ =>
          PreTrisetPair.noConfusion hEq
        | .isNull, _, _, _, ⟨_, _, _, rfl, rfl⟩, ⟨hEq, _⟩ =>
          PreTrisetPair.noConfusion hEq
        | .ins, _, _, el, ⟨t0, t1, r01, rfl, rfl⟩, ins =>
          let ⟨e1, e1In, e1Eq⟩ :=
            embed_elim_def (show Ins (embed t1) el.toPair from ins)
          let ⟨e0, e0In, rE⟩ := simRL .ins t1 t0 e1 r01 e1In
          ⟨
            e0.toPreTrisetPair,
            embed_ins e0In,
            e0,
            e1,
            rE,
            rfl,
            PreTrisetPair.toPair_inj e1Eq
          ⟩
        | .inw, _, _, el, ⟨t0, t1, r01, rfl, rfl⟩, inw =>
          let ⟨e1, e1In, e1Eq⟩ :=
            embed_elim_pos (show Inw (embed t1) el.toPair from inw)
          let ⟨e0, e0In, rE⟩ := simRL .inw t1 t0 e1 r01 e1In
          ⟨
            e0.toPreTrisetPair,
            embed_inw e0In,
            e0,
            e1,
            rE,
            rfl,
            PreTrisetPair.toPair_inj e1Eq
          ⟩
      ⟨R', ⟨simL, simR⟩, t, t', r, rfl, rfl⟩
    
    /-
      If the embeddings of two trisets are bisimilar, so are the
      trisets themselves.
    -/
    def bisim_of_toPreTrisetPair_bisim {t t': PreTriset}
      (bisim: t.toPreTrisetPair.IsBisim t'.toPreTrisetPair)
    :
      t.IsBisim t'
    :=
      let ⟨R', ⟨simLR, simRL⟩, r⟩ := bisim
      let R: PreTriset → PreTriset → Prop :=
        fun a b => R' a.toPreTrisetPair b.toPreTrisetPair
      let simL: transitionSystem.IsSimulation R := fun
        | .ins, a, b, e, rab, ins =>
          let ⟨q, qIn, rq⟩ :=
            simLR .ins
              a.toPreTrisetPair b.toPreTrisetPair e.toPreTrisetPair
              rab
              (embed_ins ins)
          let ⟨e', e'In, qEq⟩ :=
            embed_elim_def (show Ins (embed b) q.toPair from qIn)
          let qEncEq: q = toPreTrisetPair e' :=
            PreTrisetPair.toPair_inj qEq
          ⟨
            e',
            e'In,
            show R' (toPreTrisetPair e) (toPreTrisetPair e')
              from qEncEq ▸ rq,
          ⟩
        | .inw, a, b, e, rab, inw =>
          let ⟨q, qIn, rq⟩ :=
            simLR .inw
              a.toPreTrisetPair b.toPreTrisetPair e.toPreTrisetPair
              rab
              (embed_inw inw)
          let ⟨e', e'In, qEq⟩ :=
            embed_elim_pos (show Inw (embed b) q.toPair from qIn)
          let qEncEq: q = toPreTrisetPair e' :=
            PreTrisetPair.toPair_inj qEq
          ⟨
            e',
            e'In,
            show R' (toPreTrisetPair e) (toPreTrisetPair e')
              from qEncEq ▸ rq,
          ⟩
      let simR: transitionSystem.IsSimulation (Function.swap R) := fun
        | .ins, a, b, e, rab, ins =>
          let ⟨q, qIn, rq⟩ :=
            simRL .ins
              a.toPreTrisetPair b.toPreTrisetPair e.toPreTrisetPair
              rab
              (embed_ins ins)
          let ⟨e', e'In, qEq⟩ :=
            embed_elim_def (show Ins (embed b) q.toPair from qIn)
          let qEncEq: q = toPreTrisetPair e' :=
            PreTrisetPair.toPair_inj qEq
          ⟨
            e',
            e'In,
            show R' (toPreTrisetPair e') (toPreTrisetPair e)
              from qEncEq ▸ rq,
          ⟩
        | .inw, a, b, e, rab, inw =>
          let ⟨q, qIn, rq⟩ :=
            simRL .inw
              a.toPreTrisetPair b.toPreTrisetPair e.toPreTrisetPair
              rab
              (embed_inw inw)
          let ⟨e', e'In, qEq⟩ :=
            embed_elim_pos (show Inw (embed b) q.toPair from qIn)
          let qEncEq: q = toPreTrisetPair e' :=
            PreTrisetPair.toPair_inj qEq
          ⟨
            e',
            e'In,
            show R' (toPreTrisetPair e') (toPreTrisetPair e)
              from qEncEq ▸ rq,
          ⟩
      ⟨R, ⟨simL, simR⟩, r⟩
    
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
      ⟨t.toPreTrisetPair, e.toPreTrisetPair, rfl, rfl, embed_ins ins⟩
    
    -- The embedding preserves possible membership (PreTriset version).
    def directInw_toTrisetPair_pre {t e: PreTriset} (inw: t.Inw e):
      (toTrisetPair ⟦t⟧).DirectInw (toTrisetPair ⟦e⟧)
    :=
      ⟨t.toPreTrisetPair, e.toPreTrisetPair, rfl, rfl, embed_inw inw⟩
    
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
        (fun t e ⟨preA, preB, aEq, bEq, st⟩ =>
          let aBisim: t.toPreTrisetPair.IsBisim preA := Quotient.exact aEq
          let bBisim: e.toPreTrisetPair.IsBisim preB := Quotient.exact bEq
          let ⟨q, qIn, qBisim⟩ :=
            PreTrisetPair.transitionSystem.IsBisimilar_isSimulation
              .ins _ _ _ (PreTrisetPair.setoid.iseqv.symm aBisim) st
          let ⟨(e': PreTriset), e'In, qEq⟩ :=
            embed_elim_def (show PreTriset.Ins (embed t) q.toPair from qIn)
          let qEq: q = e'.toPreTrisetPair := PreTrisetPair.toPair_inj qEq
          let qBisim: preB.IsBisim e'.toPreTrisetPair := qEq ▸ qBisim
          ⟨
            t,
            e',
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim
                (PreTrisetPair.setoid.iseqv.trans bBisim qBisim)),
            e'In,
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
        (fun t e ⟨preA, preB, aEq, bEq, st⟩ =>
          let aBisim: t.toPreTrisetPair.IsBisim preA := Quotient.exact aEq
          let bBisim: e.toPreTrisetPair.IsBisim preB := Quotient.exact bEq
          let ⟨q, qIn, qBisim⟩ :=
            PreTrisetPair.transitionSystem.IsBisimilar_isSimulation
              .inw _ _ _ (PreTrisetPair.setoid.iseqv.symm aBisim) st
          let ⟨(e': PreTriset), e'In, qEq⟩ :=
            embed_elim_pos (show PreTriset.Inw (embed t) q.toPair from qIn)
          let qEq: q = e'.toPreTrisetPair := PreTrisetPair.toPair_inj qEq
          let qBisim: preB.IsBisim e'.toPreTrisetPair := qEq ▸ qBisim
          ⟨
            t,
            e',
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim
                (PreTrisetPair.setoid.iseqv.trans bBisim qBisim)),
            e'In,
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
