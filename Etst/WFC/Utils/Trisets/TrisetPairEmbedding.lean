import Etst.WFC.Utils.Trisets.TrisetPair
import Etst.WFC.Utils.Trisets.TrisetPairEncoding

/-
  An embedding of `Triset` into `TrisetPair`.
-/

namespace Etst


namespace Pair
  open TrisetPairEncoding
  
  namespace PreTriset
    /--
      The embedding on representatives: re-encode the triset
      so that its members are TrisetPair encodings, then wrap
      it in the `set` constructor.
    -/
    def toPreTrisetPair (t: PreTriset): PreTrisetPair :=
      .set (encode t)
    
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
            encode_elim_def (show Ins (encode t0) el.toPair from ins)
          let ⟨e1, e1In, rE⟩ := simLR .ins t0 t1 e0 r01 e0In
          ⟨
            e1.toPreTrisetPair,
            encode_ins e1In,
            e0,
            e1,
            rE,
            PreTrisetPair.toPair_inj e0Eq,
            rfl
          ⟩
        | .inw, _, _, el, ⟨t0, t1, r01, rfl, rfl⟩, inw =>
          let ⟨e0, e0In, e0Eq⟩ :=
            encode_elim_pos (show Inw (encode t0) el.toPair from inw)
          let ⟨e1, e1In, rE⟩ := simLR .inw t0 t1 e0 r01 e0In
          ⟨
            e1.toPreTrisetPair,
            encode_inw e1In,
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
            encode_elim_def (show Ins (encode t1) el.toPair from ins)
          let ⟨e0, e0In, rE⟩ := simRL .ins t1 t0 e1 r01 e1In
          ⟨
            e0.toPreTrisetPair,
            encode_ins e0In,
            e0,
            e1,
            rE,
            rfl,
            PreTrisetPair.toPair_inj e1Eq
          ⟩
        | .inw, _, _, el, ⟨t0, t1, r01, rfl, rfl⟩, inw =>
          let ⟨e1, e1In, e1Eq⟩ :=
            encode_elim_pos (show Inw (encode t1) el.toPair from inw)
          let ⟨e0, e0In, rE⟩ := simRL .inw t1 t0 e1 r01 e1In
          ⟨
            e0.toPreTrisetPair,
            encode_inw e0In,
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
              (encode_ins ins)
          let ⟨e', e'In, qEq⟩ :=
            encode_elim_def (show Ins (encode b) q.toPair from qIn)
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
              (encode_inw inw)
          let ⟨e', e'In, qEq⟩ :=
            encode_elim_pos (show Inw (encode b) q.toPair from qIn)
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
              (encode_ins ins)
          let ⟨e', e'In, qEq⟩ :=
            encode_elim_def (show Ins (encode b) q.toPair from qIn)
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
              (encode_inw inw)
          let ⟨e', e'In, qEq⟩ :=
            encode_elim_pos (show Inw (encode b) q.toPair from qIn)
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
      a triset index `t` is sent to the class of `set (encode t)`.
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
    def exactIns_toTrisetPair_pre {t e: PreTriset} (ins: t.Ins e):
      TrisetPair.ExactIns (toTrisetPair ⟦t⟧) (toTrisetPair ⟦e⟧)
    :=
      ⟨t.toPreTrisetPair, e.toPreTrisetPair, rfl, rfl, encode_ins ins⟩
    
    -- The embedding preserves possible membership (PreTriset version).
    def exactInw_toTrisetPair_pre {t e: PreTriset} (inw: t.Inw e):
      TrisetPair.ExactInw (toTrisetPair ⟦t⟧) (toTrisetPair ⟦e⟧)
    :=
      ⟨t.toPreTrisetPair, e.toPreTrisetPair, rfl, rfl, encode_inw inw⟩
    
    -- The embedding preserves definitive membership.
    def exactIns_toTrisetPair {ts elem: Triset}
      (ins: ts.ExactIns elem)
    :
      TrisetPair.ExactIns (toTrisetPair ts) (toTrisetPair elem)
    :=
      let ⟨_, _, tsEq, elemEq, ins⟩ := ins
      tsEq ▸ elemEq ▸ exactIns_toTrisetPair_pre ins
    
    -- The embedding preserves possible membership.
    def exactInw_toTrisetPair {ts elem: Triset}
      (inw: ts.ExactInw elem)
    :
      TrisetPair.ExactInw (toTrisetPair ts) (toTrisetPair elem)
    :=
      let ⟨_, _, tsEq, elemEq, inw⟩ := inw
      tsEq ▸ elemEq ▸ exactInw_toTrisetPair_pre inw
    
  end Triset
end Pair
