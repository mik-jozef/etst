import Etst.WFC.Ch5_SubsethoodPS

namespace Etst
open Expr


namespace DefList.SubsetStx
  variable {dl: DefList}
  
  private def subsingle_body_subst
    (t: SingleLaneExpr)
    (map: Nat → Nat)
  :
    Eq
      (substVar (liftFvMapVar map) t.isSubsingleton_body)
      ((substVar map t).isSubsingleton_body)
  :=
    congrArg
      (fun e => impl (some (ir e (var 0))) (full (impl e (var 0))))
      (lift_substVar_eq t map)
  
  private def subsingle_subst
    (t: SingleLaneExpr)
    (map: Nat → Nat)
  :
    substVar map t.isSubsingleton = (substVar map t).isSubsingleton
  := by
    apply congrArg Expr.arbIr
    rw [←substVar_liftFvMapVar_subst t.isSubsingleton_body map]
    exact subsingle_body_subst t map
  
  private def substVar_hypothesify_map
    (desc: MutIndDescriptor dl)
    (map: Nat → Nat)
    (depth: Nat)
    (ed: Bool)
    (expr: SingleLaneExpr)
    (varLt: ∀ x ∈ expr.UsesFreeVar, x < depth)
  :
    let mapDesc d: InductionDescriptor dl := {
      lane := d.lane
      x := d.x
      expr := substVar map d.expr
      expansion := d.expansion
      expandsInto := d.expandsInto
    }
    Eq
      (substVar
        (liftFvMapVarDepth depth map)
        (replaceDepthEvenConsts expr depth ed desc.hypothesis))
      (replaceDepthEvenConsts
        expr
        depth
        ed
        (MutIndDescriptor.hypothesis (desc.map mapDesc)))
  := by
    intro mapDesc; exact
    let rec map_var_lt {d y} (lt: y < d):
      liftFvMapVarDepth d map y = y
    :=
      match d with
      | 0 => (Nat.not_lt_zero y lt).elim
      | dPred + 1 =>
        match y with
        | 0 => rfl
        | yPred + 1 =>
          congrArg Nat.succ (map_var_lt (Nat.lt_of_succ_lt_succ lt))

    let rec map_var_ge {d y}:
      liftFvMapVarDepth d map (y + d) = map y + d
    :=
      match d with
      | 0 => rfl
      | dPred + 1 => congrArg Nat.succ (map_var_ge)

    let substVar_lift_depth_eq
      (body: SingleLaneExpr)
    :
      Eq
        (substVar (liftFvMapVarDepth depth map) (body.lift 0 depth))
        ((substVar map body).lift 0 depth)
    := by
      let compEq:
        Eq
          ((liftFvMapVarDepth depth map) ∘ (substLift.fn 0 depth))
          ((substLift.fn 0 depth) ∘ map)
      :=
        funext fun _ => map_var_ge
      rw [body.lift_eq_substLift, substLift]
      rw [←substVar_comp]
      rw [compEq]
      rw [substVar_comp]
      rw [lift_eq_substLift, substLift]

    match expr with
    | .const lane x =>
      match ed with
      | true =>
        let rec hypo_map desc:
          Eq
            (substVar
              (liftFvMapVarDepth depth map)
              (MutIndDescriptor.hypothesis desc depth lane x))
            (MutIndDescriptor.hypothesis (desc.map mapDesc) depth lane x)
        :=
          match desc with
          | [] => rfl
          | head :: tail => by
            let ih := hypo_map tail
            dsimp [MutIndDescriptor.hypothesis, InductionDescriptor.hypothesis]
            split_ifs with h
            · exact congrArg₂ Expr.ir (substVar_lift_depth_eq head.expr) ih
            · exact ih
        hypo_map desc
      | false => rfl
    | .var x =>
      congrArg Expr.var (map_var_lt (varLt x rfl))
    | .null => rfl
    | .pair l r =>
      let varLtL x h := varLt x (Or.inl h)
      let varLtR x h := varLt x (Or.inr h)
      congrArg₂
        pair
          (substVar_hypothesify_map desc map depth ed l varLtL)
          (substVar_hypothesify_map desc map depth ed r varLtR)
    | .ir l r =>
      let varLtL x h := varLt x (Or.inl h)
      let varLtR x h := varLt x (Or.inr h)
      congrArg₂
        ir
          (substVar_hypothesify_map desc map depth ed l varLtL)
          (substVar_hypothesify_map desc map depth ed r varLtR)
    | .full body =>
      congrArg
        full
        (substVar_hypothesify_map desc map depth ed body varLt)
    | .compl body =>
      congrArg
        Expr.compl
        (substVar_hypothesify_map desc map depth (!ed) body varLt)
    | .arbIr body =>
      let varLtB x (h: body.UsesFreeVar x): x < depth + 1 :=
        match x with
        | 0 => Nat.zero_lt_succ depth
        | xp + 1 => Nat.succ_lt_succ (varLt xp h)
      let ih:
        Eq
          (substVar
            (liftFvMapVarDepth (depth + 1) map)
            (replaceDepthEvenConsts body (depth + 1) ed desc.hypothesis))
          _
      :=
        substVar_hypothesify_map desc map (depth + 1) ed body varLtB
      congrArg
        arbIr
        (substVar_liftFvMapVar_subst _ _ ▸ ih)
  
  def mapFv
    {x a: SingleLaneExpr}
    (sub: dl.SubsetStx x a)
    (map: Nat → Nat)
  :
    dl.SubsetStx (x.substVar map) (a.substVar map)
  :=
    match sub with
    | subId =>
      subId
    | defPos sub => defPos (mapFv sub map)
    | varSomeFull sub => varSomeFull (mapFv sub map)
    | varFullSome sub => varFullSome (mapFv sub map)
    | nullSomeFull sub => nullSomeFull (mapFv sub map)
    | nullFullSome sub => nullFullSome (mapFv sub map)
    | somePair subL subR =>
      somePair (mapFv subL map) (mapFv subR map)
    | pairSubsingleton (x:=x) (a:=a) (b:=b) subL subR =>
      let ihL := subsingle_subst a map ▸ mapFv subL map
      let ihR := subsingle_subst b map ▸ mapFv subR map
      subsingle_subst (a.pair b) map ▸
      pairSubsingleton ihL ihR
    | pairMono subL subR =>
      pairMono (mapFv subL map) (mapFv subR map)
    | complPair sub => complPair (mapFv sub map)
    | complPairElim sub => complPairElim (mapFv sub map)
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
    | arbIrElim (t:=t) (a:=a) sub someSub subsingle =>
      let ihSome := mapFv someSub map
      let ih := mapFv sub map
      
      let isSubsingle:
        dl.SubsetStx
          (substVar map x)
          (substVar map t).isSubsingleton
      :=
        subsingle_subst t map ▸ mapFv subsingle map
      
      let subInst:
        dl.SubsetStx
          (substVar map x)
          (subst
            (instantiateVar.fn (t.substVar map) ∘ (liftFvMapVar map))
            a)
      :=
        subst_comp_var _ _ _ ▸
        substVar_liftFvMapVar_subst a map ▸
        arbIrElim ih ihSome isSubsingle
      
      let eq:
        Eq
          (instantiateVar.fn (substVar map t) ∘ liftFvMapVar map)
          (fun x => subst (var ∘ map) (instantiateVar.fn t x))
      :=
        funext fun | 0 => rfl | _ + 1 => rfl
      
      show dl.SubsetStx _ (subst _ (subst _ _)) from
      subst_subst _ _ _ ▸ eq ▸ subInst
    
    | noneElim sub => noneElim (mapFv sub map)
    | unfold (lane:=lane) (c:=c) sub =>
      let hClean :=
        substVar_eq_of_isClean ((dl.isClean c).toLane lane) map
      hClean.symm ▸ unfold (mapFv sub map)
    | fold (lane:=lane) (c:=c) sub =>
      let hClean :=
        substVar_eq_of_isClean ((dl.isClean c).toLane lane) map
      fold (hClean ▸ mapFv sub map)
    | trans subAb subBc =>
      trans (mapFv subAb map) (mapFv subBc map)
    | mutInduction desc premises i =>
      let mapDesc (d: InductionDescriptor dl): InductionDescriptor dl := {
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
      
      let substHypoEq (j: descMap.Index):
        Eq
        (substVar
          map
          (desc.hypothesify 0 (desc[j.unmap].expansion.toLane desc[j.unmap].lane)))
          (descMap.hypothesify 0 (desc[j.unmap].expansion.toLane desc[j.unmap].lane))
      :=
        let d := desc[j.unmap]
        let expr := d.expansion.toLane d.lane
        let expClean: d.expansion.IsClean :=
          d.expandsInto.isClean_expands
            0
            (fun x h => (dl.isClean d.x) (x + 0) h)
        let varLt: ∀ x ∈ UsesFreeVar expr, x < 0 :=
          fun x h =>
            let iff := BasicExpr.toLane_UsesFreeVar d.expansion d.lane x
            False.elim (expClean x (iff.mp h))
        substVar_hypothesify_map desc map 0 true expr varLt
      
      let mappedPremises (j: descMap.Index):
        dl.SubsetStx
          (substVar map x)
          (full
            (impl
              (descMap.hypothesify 0 (descMap[j].expansion.toLane descMap[j].lane))
              descMap[j].expr))
      :=
        let premMapped := mapFv (premises j.unmap) map
        eqMap j ▸ substHypoEq j ▸ premMapped

      let ih := mutInduction descMap mappedPremises iMap
      
      by rw [eqMap] at ih; exact ih
    | simplePairInduction sub =>
      simplePairInduction (mapFv sub map)
  
  def ofLift {x a d l}
    (sub: dl.SubsetStx (x.lift d l) (a.lift d l))
  :
    dl.SubsetStx x a
  :=
    let xEq := substVar_substUnlift_lift_eq x d l
    let aEq := substVar_substUnlift_lift_eq a d l
    xEq ▸ aEq ▸ mapFv sub (substUnlift.fn d l)
  
  def toLift {x a}
    (sub: dl.SubsetStx x a)
    (d: Nat := 0)
    (l: Nat := 1)
  :
    dl.SubsetStx (x.lift d l) (a.lift d l)
  :=
    lift_eq_substLift x d l ▸
    lift_eq_substLift a d l ▸
    mapFv sub (substLift.fn d l)
  
end DefList.SubsetStx
