/-
  An embedding of `Triset` into `TrisetPair` (defined internally
  in WFC).
-/
module
public import Etst.WFC.Utils.Trisets.Triset.TrisetEmbedding
public import Etst.WFC.Utils.Trisets.TrisetPair.TrisetPair

public section
namespace Etst


namespace Pair
  open TrisetEmbedding
  
  namespace PreTriset
    /-
      The embedding on representatives: embed the triset so that its
      members are TrisetPair codes, then wrap it in the `set` constructor.
    -/
    exposed def toPreTrisetPair (t: PreTriset): PreTrisetPair :=
      .set (embed t)
    
    -- The embedding preserves membership.
    theorem has_toPreTrisetPair {lane}
      {t e: PreTriset}
      (has: t.Has lane e)
    :
      t.toPreTrisetPair.Has lane e.toPreTrisetPair
    :=
      embed_mem has
    
    -- Members of an embedding are embeddings.
    theorem has_toPreTrisetPair_elim {lane}
      {t: PreTriset}
      {e: PreTrisetPair}
      (has: t.toPreTrisetPair.Has lane e)
    :
      ∃ e0: PreTriset, t.Has lane e0 ∧ e = e0.toPreTrisetPair
    :=
      let ⟨e0, e0In, eq⟩ := embed_elim has
      ⟨e0, e0In, PreTrisetPair.toPair_inj (b := toPreTrisetPair e0) eq⟩
    
    /-
      If two trisets are bisimilar, so are their embeddings.
    -/
    theorem toPreTrisetPair_bisim {t t': PreTriset}
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
        | .has lane, _, _, _, ⟨t0, t1, b, rfl, rfl⟩, has =>
          let ⟨e0, e0In, eEq⟩ := has_toPreTrisetPair_elim has
          let ⟨e1, e1In, be⟩ :=
            PreTriset.transitionSystem.IsBisimilar_isSimulation
              lane t0 t1 e0 b e0In
          ⟨
            e1.toPreTrisetPair,
            has_toPreTrisetPair e1In,
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
    theorem bisim_of_toPreTrisetPair_bisim {t t': PreTriset}
      (bisim: t.toPreTrisetPair.IsBisim t'.toPreTrisetPair)
    :
      t.IsBisim t'
    :=
      let R (a b: PreTriset): Prop :=
        a.toPreTrisetPair.IsBisim b.toPreTrisetPair
      let sim: PreTriset.transitionSystem.IsSimulation R :=
        fun _ _ _ e rab has =>
          let ⟨_, has', be⟩ :=
            PreTrisetPair.IsBisim.has rab (has_toPreTrisetPair has)
          let ⟨e1, e1In, eq⟩ := has_toPreTrisetPair_elim has'
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
    /-
      The embedding of `Triset` into `TrisetPair`: the class of
      a triset index `t` is sent to the class of `set (embed t)`.
    -/
    exposed def toTrisetPair: Triset → TrisetPair :=
      Quotient.lift
        (fun t => ⟦PreTriset.toPreTrisetPair t⟧)
        (fun _ _ bisim =>
          Quot.sound (PreTriset.toPreTrisetPair_bisim bisim))
    
    /-- The embedding applied to a class of an index. -/
    theorem toTrisetPair_eq (t: PreTriset):
      toTrisetPair ⟦t⟧ = ⟦t.toPreTrisetPair⟧
    :=
      rfl
    
    /-- The embedding is injective. -/
    theorem toTrisetPair_inj: Function.Injective toTrisetPair :=
      fun a b eq =>
        a.exists_rep.elim fun t aEq =>
        b.exists_rep.elim fun t' bEq => by
          subst aEq
          subst bEq
          exact
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim
                (Quotient.exact eq))
    
    -- The embedding preserves membership (on representatives).
    theorem directHas_toTrisetPair_pre {t e lane}
      (has: t.Has lane e)
    :
      (toTrisetPair ⟦t⟧).DirectHas lane (toTrisetPair ⟦e⟧)
    :=
      ⟨
        t.toPreTrisetPair,
        e.toPreTrisetPair,
        rfl,
        rfl,
        PreTriset.has_toPreTrisetPair has,
      ⟩
    
    -- The embedding preserves membership.
    theorem directHas_toTrisetPair {lane}
      {ts elem: Triset}
      (has: ts.DirectHas lane elem)
    :
      ts.toTrisetPair.DirectHas lane elem.toTrisetPair
    :=
      let ⟨_, _, tsEq, elemEq, has⟩ := has
      tsEq ▸ elemEq ▸ directHas_toTrisetPair_pre has
    
    -- The embedding reflects membership.
    theorem directHas_of_toTrisetPair {lane}
      {ts elem: Triset}
      (has: ts.toTrisetPair.DirectHas lane elem.toTrisetPair)
    :
      ts.DirectHas lane elem
    :=
      Quotient.inductionOn₂
        (motive := fun (ts elem: Triset) =>
          ts.toTrisetPair.DirectHas lane elem.toTrisetPair →
          ts.DirectHas lane elem)
        ts
        elem
        (fun t _ has =>
          let ⟨_, has', be⟩ := TrisetPair.directHas_mk_iff.mp has
          let ⟨e1, e1In, eq⟩ := PreTriset.has_toPreTrisetPair_elim has'
          ⟨
            t,
            e1,
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetPair_bisim (eq ▸ be)),
            e1In,
          ⟩)
        has
    
    theorem directHas_iff_toTrisetPair {lane}
      {ts elem: Triset}
    :
      Iff
        (ts.DirectHas lane elem)
        (ts.toTrisetPair.DirectHas lane elem.toTrisetPair)
    :=
      ⟨directHas_toTrisetPair, directHas_of_toTrisetPair⟩
    
  end Triset
end Pair
