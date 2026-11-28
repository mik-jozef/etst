/-
  An embedding of `Triset` into `TrisetFn`. The triset `t` is sent to
  `set (embed t)`, whose members are again embedded trisets.
-/
module
public import Etst.WFC.Utils.Trisets.Triset.Triset
public import Etst.WFC.Utils.Trisets.Triset.TrisetEmbedding
public import Etst.WFC.Utils.Trisets.TrisetFn.TrisetFn

public section
namespace Etst


namespace Pair
  open TrisetEmbedding
  
  namespace PreTriset
    exposed def toPreTrisetFn (t: PreTriset): PreTrisetFn := .set (embed t)
    
    theorem not_isFn_toPreTrisetFn (t: PreTriset): ¬ t.toPreTrisetFn.IsFn :=
      id
    
    -- The embedding preserves membership.
    theorem has_toPreTrisetFn {lane}
      {t e: PreTriset}
      (has: t.Has lane e)
    :
      t.toPreTrisetFn.Has lane e.toPreTrisetFn
    :=
      embed_mem has
    
    -- Members of an embedding are embeddings.
    theorem has_toPreTrisetFn_elim {lane}
      {t: PreTriset}
      {e: PreTrisetFn}
      (has: t.toPreTrisetFn.Has lane e)
    :
      ∃ e0: PreTriset, t.Has lane e0 ∧ e = e0.toPreTrisetFn
    :=
      let ⟨e0, e0In, eq⟩ := embed_elim has
      ⟨e0, e0In, PreTrisetFn.toPair_inj (b := toPreTrisetFn e0) eq⟩
    
    -- If two trisets are bisimilar, so are their embeddings.
    theorem toPreTrisetFn_bisim {t t': PreTriset}
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
        | _, _, _, x', ⟨t0, t1, b, rfl, rfl⟩, st =>
          match st with
          | .has has =>
            let ⟨e0, e0In, eEq⟩ := has_toPreTrisetFn_elim has
            let ⟨e1, e1In, be⟩ :=
              PreTriset.transitionSystem.IsBisimilar_isSimulation
                _ t0 t1 e0 b e0In
            ⟨
              _,
              .has (has_toPreTrisetFn e1In),
              e0, e1, be, congrArg _ eEq, rfl,
            ⟩
          | .hasEntry has => nomatch has
      ⟨
        R,
        LabeledTransitionSystem.isBisimulation_of_symm symm sim,
        t, t', bisim, rfl, rfl,
      ⟩
    
    -- If the embeddings of two trisets are bisimilar, so are the trisets.
    theorem bisim_of_toPreTrisetFn_bisim {t t': PreTriset}
      (bisim: t.toPreTrisetFn.IsBisim t'.toPreTrisetFn)
    :
      t.IsBisim t'
    :=
      let R (a b: PreTriset): Prop :=
        a.toPreTrisetFn.IsBisim b.toPreTrisetFn
      let sim: PreTriset.transitionSystem.IsSimulation R :=
        fun _ _ _ e rab ins =>
          let ⟨_, ins', be⟩ :=
            PreTrisetFn.IsBisim.has rab (has_toPreTrisetFn ins)
          let ⟨e1, e1In, eq⟩ := has_toPreTrisetFn_elim ins'
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
    exposed def toTrisetFn: Triset → TrisetFn :=
      Quotient.lift
        (fun t => ⟦t.toPreTrisetFn⟧)
        (fun _ _ bisim =>
          Quotient.sound (PreTriset.toPreTrisetFn_bisim bisim))
    
    theorem toTrisetFn_inj: Function.Injective toTrisetFn :=
      fun a b eq =>
        a.exists_rep.elim fun t aEq =>
        b.exists_rep.elim fun t' bEq => by
          subst aEq
          subst bEq
          exact
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetFn_bisim (Quotient.exact eq))
    
    theorem not_isFn_toTrisetFn (ts: Triset): ¬ ts.toTrisetFn.IsFn :=
      Quotient.inductionOn
        (motive := fun (ts: Triset) => ¬ ts.toTrisetFn.IsFn)
        ts
        PreTriset.not_isFn_toPreTrisetFn
    
    -- The embedding preserves membership (on representatives).
    theorem directHas_toTrisetFn_pre {lane}
      {t e: PreTriset}
      (has: t.Has lane e)
    :
      (toTrisetFn ⟦t⟧).DirectHas lane (toTrisetFn ⟦e⟧)
    :=
      let has := PreTriset.has_toPreTrisetFn has
      ⟨t.toPreTrisetFn, e.toPreTrisetFn, rfl, rfl, has⟩
    
    -- The embedding preserves membership.
    theorem directHas_toTrisetFn {lane}
      {ts elem: Triset}
      (has: ts.DirectHas lane elem)
    :
      ts.toTrisetFn.DirectHas lane elem.toTrisetFn
    :=
      let ⟨_, _, tsEq, elemEq, has⟩ := has
      tsEq ▸ elemEq ▸ directHas_toTrisetFn_pre has
    
    -- The embedding reflects membership.
    theorem directHas_of_toTrisetFn {lane}
      {ts elem: Triset}
      (has: ts.toTrisetFn.DirectHas lane elem.toTrisetFn)
    :
      ts.DirectHas lane elem
    :=
      Quotient.inductionOn₂
        (motive := fun (ts elem: Triset) =>
          ts.toTrisetFn.DirectHas lane elem.toTrisetFn →
          ts.DirectHas lane elem)
        ts
        elem
        (fun t _ has =>
          let ⟨_, has', be⟩ := TrisetFn.directHas_mk_iff.mp has
          let ⟨e1, e1In, eq⟩ := PreTriset.has_toPreTrisetFn_elim has'
          ⟨
            t,
            e1,
            rfl,
            Quotient.sound
              (PreTriset.bisim_of_toPreTrisetFn_bisim (eq ▸ be)),
            e1In,
          ⟩)
        has
    
    theorem directHas_iff_toTrisetFn {lane}
      {ts elem: Triset}
    :
      Iff
        (ts.DirectHas lane elem)
        (ts.toTrisetFn.DirectHas lane elem.toTrisetFn)
    :=
      ⟨directHas_toTrisetFn, directHas_of_toTrisetFn⟩
    
  end Triset
end Pair
