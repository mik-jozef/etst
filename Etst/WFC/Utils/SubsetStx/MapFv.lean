import Etst.WFC.Ch5_SubsethoodPS

namespace Etst
open Expr


namespace DefList.SubsetStx
  variable {dl: DefList}
  
  private def subsingle_subst
    (t: SingleLaneExpr)
    (map: Nat → Nat)
  :
    substVar (liftFvMapVar map) t.isSubsingleton
      =
    (substVar map t).isSubsingleton
  := by
    show
      impl
        (some (ir (substVar (liftFvMapVar map) t.lift) (var 0)))
        (full (impl (substVar (liftFvMapVar map) t.lift) (var 0)))
        =
      impl
        (some (ir ((substVar map t).lift) (var 0)))
        (full (impl ((substVar map t).lift) (var 0)))
    rw [lift_substVar_eq t map]

  -- TODO unify with liftFvMapVarDepth?
  private def mapAtDepth
    (map: Nat → Nat)
    (depth: Nat)
  :
    Nat → Nat
  :=
    Nat.rec map (fun _ ih => liftFvMapVar ih) depth

  private lemma substVar_hypothesify_map
    (desc: MutIndDescriptor dl)
    (map: Nat → Nat)
    (mapDesc: InductionDescriptor dl → InductionDescriptor dl)
    (descMap: MutIndDescriptor dl)
    (hMapDesc:
      mapDesc
        =
      fun d => {
        lane := d.lane
        x := d.x
        expr := substVar map d.expr
        expansion := d.expansion
        expandsInto := d.expandsInto
      })
    (hDescMap: descMap = desc.map mapDesc)
    (depth: Nat)
    (expr: SingleLaneExpr)
    (exprVarLt: ∀ x ∈ expr.UsesFreeVar, x < depth)
  :
    substVar (mapAtDepth map depth) (desc.hypothesify depth expr)
      =
    descMap.hypothesify depth expr
  :=
    sorry

  def mapFv
    {x a: SingleLaneExpr}
    (sub: dl.SubsetStx x a)
    (map: Nat → Nat)
  :
    dl.SubsetStx (x.substVar map) (a.substVar map)
  :=
    /-
      Status (2026-02-14): all `mapFv` branches are routine except
      `mutInduction`.

      In that branch, descriptor/index bookkeeping (`mapDesc`, `descMap`,
      `iMap`, `eqMap`) is already in place, and the final return cast is solved.

      The only remaining proof work is `mappedPremises`: transport the codomain
      of `mapFv (premises j.unmap) map` from
        `substVar map (desc.hypothesify 0 Ej)`
      to
        `descMap.hypothesify 0 Ej`
      (with the expected depth-sensitive behavior under binders).

      So the current target is a dedicated compatibility lemma between
      `substVar` and `MutIndDescriptor.hypothesify`.
    -/
    match sub with
    | subId =>
      subId
    | defPos sub => defPos (mapFv sub map)
    | irL sub => irL (mapFv sub map)
    | irR sub => irR (mapFv sub map)
    | irI subL subR => irI (mapFv subL map) (mapFv subR map)
    | complI subL subR =>
      complI (mapFv subL map) (mapFv subR map)
    | complElim subL subR =>
      complElim (mapFv subL map) (mapFv subR map)
    | isFullImpl sub => isFullImpl (mapFv sub map)
    | fullImplDist sub => fullImplDist (mapFv sub map)
    | fullElim sub => fullElim (mapFv sub map)
    | someStripFull sub => someStripFull (mapFv sub map)
    | arbIrI (a:=a) sub =>
      let ih :=
        substVar_liftFvMapVar_subst a map ▸
        lift_substVar_eq x map ▸
        mapFv sub (liftFvMapVar map)
      arbIrI ih
    | arbIrElim (t:=t) (a:=a) someSub subsingle sub =>
      let ihSome := mapFv someSub map
      let ih := mapFv sub map
      
      let ihSubsingle:
        dl.SubsetStx
          (substVar (liftFvMapVar map) (lift x))
          (substVar (liftFvMapVar map) t.isSubsingleton)
      :=
        mapFv subsingle (liftFvMapVar map)
      
      let isSubsingle:
        dl.SubsetStx
          (substVar map x).lift
          (substVar map t).isSubsingleton
      :=
        subsingle_subst t map ▸ (lift_substVar_eq x map ▸ ihSubsingle)
      
      let subInst:
        dl.SubsetStx
          (substVar map x)
          (subst
            (instantiateVar.fn (t.substVar map) ∘ (liftFvMapVar map))
            a)
      :=
        subst_comp_var _ _ _ ▸
        substVar_liftFvMapVar_subst a map ▸
        arbIrElim ihSome isSubsingle ih
      let eq:
        (instantiateVar.fn (substVar map t) ∘ liftFvMapVar map)
          =
        (fun x => subst (var ∘ map) (instantiateVar.fn t x))
      :=
        funext fun | 0 => rfl | _ + 1 => rfl
      show dl.SubsetStx _ (subst _ (subst _ _)) from
      subst_subst _ _ _ ▸ eq ▸ subInst
    | varSomeFull sub => varSomeFull (mapFv sub map)
    | varFullSome sub => varFullSome (mapFv sub map)
    | unfold (lane:=lane) (c:=c) sub =>
      let ih := mapFv sub map
      let hClean :=
        substVar_eq_of_isClean ((dl.isClean c).toLane lane) map
      hClean.symm ▸ unfold ih
    | fold (lane:=lane) (c:=c) sub =>
      let ih := mapFv sub map
      let hClean :=
        substVar_eq_of_isClean ((dl.isClean c).toLane lane) map
      fold (hClean ▸ ih)
    | trans subAb subBc =>
      trans (mapFv subAb map) (mapFv subBc map)
    | mutInduction desc premises i =>
      let mapDesc: InductionDescriptor dl → InductionDescriptor dl :=
        fun d => {
          lane := d.lane
          x := d.x
          expr := substVar map d.expr
          expansion := d.expansion
          expandsInto := d.expandsInto
        }
      let descMap: MutIndDescriptor dl := desc.map mapDesc
      let iMap := i.map mapDesc
      let listEq j: List.get _ _ = _ := desc.getElem_map mapDesc
      let eqMap (j: descMap.Index):
        descMap[j] = mapDesc desc[j.unmap]
      := by
        show descMap.get j = mapDesc (desc.get j.unmap)
        rw [listEq]
        rfl
      
      let mappedPremises (j: descMap.Index):
        dl.SubsetStx
          (substVar map x)
          (full
            (impl
              (descMap.hypothesify 0 (descMap[j].expansion.toLane descMap[j].lane))
              descMap[j].expr))
      :=
        let premMapped := mapFv (premises j.unmap) map
        let hHyp:
          substVar map
            (desc.hypothesify 0 (desc[j.unmap].expansion.toLane desc[j.unmap].lane))
            =
          descMap.hypothesify 0 (desc[j.unmap].expansion.toLane desc[j.unmap].lane)
        :=
          by
            simpa [mapAtDepth] using
              (substVar_hypothesify_map
                desc
                map
                mapDesc
                descMap
                rfl
                rfl
                0
                (desc[j.unmap].expansion.toLane desc[j.unmap].lane)
                (by
                  /-
                    Expected source: cleanliness of descriptor expansions
                    (`desc[j].expansion`) coming from the underlying definition
                    list invariants.
                  -/
                  sorry))
        /-
          Remaining obligation in this branch:
          rewrite the `hypothesify` part in `premMapped` via the pending
          `substVar`-`hypothesify` compatibility lemma.
        -/
        eqMap j ▸
        hHyp ▸
        premMapped

      let ih:
        dl.SubsetStx
          (substVar map x)
          (full
            (impl
              (const descMap[iMap].lane descMap[iMap].x)
              descMap[iMap].expr))
      :=
        mutInduction descMap mappedPremises iMap

      show dl.SubsetStx _ (substVar map ((const desc[i.val].lane desc[i.val].x).impl desc[i.val].expr).full) from
      by simpa [descMap, iMap, mapDesc] using ih
    | simplePairInduction sub =>
      simplePairInduction (mapFv sub map)
  
  def ofLift {x a d l}
    (sub: dl.SubsetStx (x.lift d l) (a.lift d l))
  :
    dl.SubsetStx x a
  :=
    sorry
  
  -- TODO special case of `mapFv`.
  def toLift
    {x a: SingleLaneExpr}
    (sub: dl.SubsetStx x a)
    (d l: Nat)
  :
    dl.SubsetStx (x.lift d l) (a.lift d l)
  :=
    match sub with
    | subId => subId
    | defPos sub => defPos (toLift sub d l)
    | irL sub => irL (toLift sub d l)
    | irR sub => irR (toLift sub d l)
    | irI subL subR => irI (toLift subL d l) (toLift subR d l)
    | complI subL subR =>
      complI (toLift subL d l) (toLift subR d l)
    | complElim subL subR => complElim (toLift subL d l) (toLift subR d l)
    | isFullImpl sub => isFullImpl (toLift sub d l)
    | fullImplDist sub => fullImplDist (toLift sub d l)
    | fullElim sub => fullElim (toLift sub d l)
    | someStripFull sub => someStripFull (toLift sub d l)
    | arbIrI sub =>
      -- let ih := toLift sub (d + 1) l
      -- arbIrI ih
      sorry
    | arbIrElim someSub subsingle sub =>
      sorry
    | varSomeFull sub => varSomeFull (toLift sub d l)
    | varFullSome sub => varFullSome (toLift sub d l)
    | unfold sub => sorry
    | fold sub => fold sorry
    | trans subAb subBc => trans (toLift subAb d l) (toLift subBc d l)
    | mutInduction desc premises i => sorry
    | simplePairInduction sub => simplePairInduction (toLift sub d l)
  
end DefList.SubsetStx
