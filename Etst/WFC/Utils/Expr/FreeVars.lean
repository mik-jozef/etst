module
public import Etst.WFC.Ch2_Interpretation
public import Etst.WFC.Utils.PairExpr
public import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.Expr.ConstsVarsSat

public section
namespace Etst
variable {kind: ExprKind}


namespace Expr
  exposed def substVar
    (fvMap: Nat → Nat)
  :
    Expr kind → Expr kind
  :=
    subst (var ∘ fvMap)
  
  exposed def instantiateVar.fn (t: Expr kind): Nat → Expr kind
  | 0 => t
  | n + 1 => var n
  
  exposed def instantiateVar (expr: Expr kind) (t: Expr kind): Expr kind :=
    expr.subst (instantiateVar.fn t)
  
  exposed def substId: Expr kind → Expr kind := substVar id  
  
  exposed def substLift.fn (depth liftBy: Nat) :=
    fun x => if x < depth then x else x + liftBy
  
  exposed def substUnlift.fn (depth unliftBy: Nat) :=
    fun x => if x < depth then x else x - unliftBy
  
  -- Redefining `lift` using `substVar`, so we can use composition
  -- properties of `substVar` to prove properties of `lift`.
  exposed def substLift
    (expr: Expr kind)
    (depth: Nat)
    (liftBy: Nat)
  :
    Expr kind
  :=
    expr.substVar (substLift.fn depth liftBy)
  
  def clearFreeVars: Expr kind → Expr kind :=
    Expr.subst fun _ => .none
  
  
  exposed def liftFvMapVar
    (fvMap: Nat → Nat)
  :
    Nat → Nat
  | 0 => 0
  | n + 1 => (fvMap n) + 1
  
  exposed def liftFvMapVarDepth
    (depth: Nat)
    (map: Nat → Nat)
  :
    Nat → Nat
  :=
    Nat.rec map (fun _ ih => liftFvMapVar ih) depth
  
  theorem lift_var_lt
    (x: Nat)
    {depth} (lt: x < depth)
    (liftBy: Nat)
  :
    (var (kind := kind) x).lift depth liftBy = var x
  :=
    show var _ = _ from ite_eq_left lt ▸ rfl
  
  theorem lift_var_ge
    (x: Nat)
    {depth} (ge: depth ≤ x)
    (liftBy: Nat)
  :
    (var (kind := kind) x).lift depth liftBy = var (x + liftBy)
  :=
    show var _ = _ from ite_eq_right (not_lt.mpr ge) ▸ rfl
  
  theorem lift_zero_eq
    (expr: Expr kind)
    (depth: Nat)
  :
    expr.lift depth 0 = expr
  :=
    match expr with
    | const _ _ => rfl
    | var x =>
        if h: x < depth then
          (lift_var_lt x h 0).symm ▸ rfl
        else
          (lift_var_ge x (not_lt.mp h) 0).symm ▸ rfl
    | null => rfl
    | prod l r =>
      congrArg₂
        prod
        (l.lift_zero_eq depth)
        (r.lift_zero_eq depth)
    | ir l r =>
      congrArg₂
        ir
        (l.lift_zero_eq depth)
        (r.lift_zero_eq depth)
    | full body => congrArg full (body.lift_zero_eq depth)
    | compl body => congrArg compl (body.lift_zero_eq depth)
    | arbIr body => congrArg arbIr (body.lift_zero_eq depth.succ)
  
  theorem lift_add_eq
    (expr: Expr kind)
    {d0 d1} (le0: d0 ≤ d1)
    {a} (le1: d1 ≤ d0 + a)
    (b: Nat)
  :
    expr.lift d0 (a + b) = (expr.lift d0 a).lift d1 b
  :=
    match expr with
    | const _ _ => rfl
    | var x => by
      if h: x < d0 then
        rw [lift_var_lt x h]
        rw [lift_var_lt x h]
        rw [lift_var_lt x (h.trans_le le0)]
      else
        let ge: x >= d0 := not_lt.mp h
        rw [lift_var_ge x ge]
        rw [lift_var_ge x ge]
        let le1X := le1.trans (Nat.add_le_add_right ge a)
        rw [lift_var_ge (x + a) le1X]
        rw [Nat.add_assoc]
    | null => rfl
    | prod l r =>
      congrArg₂
        prod
        (l.lift_add_eq le0 le1 b)
        (r.lift_add_eq le0 le1 b)
    | ir l r =>
      congrArg₂
        ir
        (l.lift_add_eq le0 le1 b)
        (r.lift_add_eq le0 le1 b)
    | full body => congrArg full (body.lift_add_eq le0 le1 b)
    | compl body => congrArg compl (body.lift_add_eq le0 le1 b)
    | arbIr body =>
      congrArg
        arbIr
        (body.lift_add_eq
          (Nat.succ_le_succ le0)
          (Nat.succ_add _ _ ▸ Nat.succ_le_succ le1)
          b)
  
  theorem lift_inj
    {a b: Expr kind} {depth liftBy}
    (eq: a.lift depth liftBy = b.lift depth liftBy)
  :
    a = b
  :=
    match a, b with
    | const _ _, const _ _ => eq
    | var x, var y => by
      let hX := Classical.em (x < depth)
      let hY := Classical.em (y < depth)
      match hX, hY with
      | .inl ltX, .inl ltY =>
        rw [lift_var_lt x ltX liftBy] at eq
        rw [lift_var_lt y ltY liftBy] at eq
        exact eq
      | .inl ltX, .inr geY =>
        rw [lift_var_lt x ltX liftBy] at eq
        rw [lift_var_ge y (le_of_not_gt geY) liftBy] at eq
        let iEq: x = y + liftBy :=
          Expr.noConfusion rfl (heq_of_eq eq) id
        let ltY: y + liftBy < depth := iEq ▸ ltX
        exact absurd (Nat.lt_of_add_right_lt ltY) geY
      | .inr geX, .inl ltY =>
        rw [lift_var_ge x (le_of_not_gt geX) liftBy] at eq
        rw [lift_var_lt y ltY liftBy] at eq
        let iEq: x + liftBy = y :=
          Expr.noConfusion rfl (heq_of_eq eq) id
        let ltX: x + liftBy < depth := iEq.symm ▸ ltY
        exact absurd (Nat.lt_of_add_right_lt ltX) geX
      | .inr geX, .inr geY =>
        rw [lift_var_ge x (le_of_not_gt geX) liftBy] at eq
        rw [lift_var_ge y (le_of_not_gt geY) liftBy] at eq
        let iEq: x + liftBy = y + liftBy :=
          Expr.noConfusion rfl (heq_of_eq eq) id
        exact congr rfl (Nat.add_right_cancel iEq)
    | null, null => rfl
    | prod al ar, prod bl br => by
      injection eq with eql eqr
      exact congrArg₂ prod (lift_inj eql) (lift_inj eqr)
    | ir al ar, ir bl br => by
      injection eq with eql eqr
      exact congrArg₂ ir (lift_inj eql) (lift_inj eqr)
    | full a, full b => by
      injection eq with eqf
      exact congrArg full (lift_inj eqf)
    | compl a, compl b => by
      injection eq with eqc
      exact congrArg compl (lift_inj eqc)
    | arbIr a, arbIr b => by
      injection eq with eqa
      exact congrArg arbIr (lift_inj eqa)
  
  -- Intuition: if one lift at `depth` already lands where a lift at
  -- `k + depth` would land, then after lifting once more we keep that
  -- alignment one level up (`depth` ↦ `k + depth + 1`).
  theorem lift_inv_step {expr: Expr kind} {k depth}
    (eq: expr.lift depth 1 = expr.lift (k + depth) 1)
  :
    Eq
      ((expr.lift depth 1).lift depth 1)
      ((expr.lift depth 1).lift (k + depth + 1) 1)
  :=
    match expr with
    | const _ _ => rfl
    | var x => by
      if h: x < depth then
        rw [lift_var_lt x h 1]
        have hx: x < k + depth + 1 := by omega
        rw [lift_var_lt x hx 1]
        exact lift_var_lt x h 1
      else
        let ge := not_lt.mp h
        rw [lift_var_ge x ge 1]
        rw [lift_var_ge _ (Nat.le_trans ge (Nat.le_succ _)) 1]
        have x_ge: x >= k + depth := by
          by_contra h_ge
          have h_lt: x < k + depth := Nat.lt_of_not_ge h_ge
          rw [lift_var_ge x ge 1] at eq
          rw [lift_var_lt x h_lt 1] at eq
          injection eq with eq
          omega
        rw [lift_var_ge _ (Nat.succ_le_succ x_ge) 1]
    | null => rfl
    | prod l r =>
      congrArg₂
        prod
        (lift_inv_step (by injection eq))
        (lift_inv_step (by injection eq))
    | ir l r =>
      congrArg₂
        ir
        (lift_inv_step (by injection eq))
        (lift_inv_step (by injection eq))
    | full body =>
      congrArg full (lift_inv_step (by injection eq))
    | compl body =>
      congrArg compl (lift_inv_step (by injection eq))
    | arbIr body =>
      congrArg arbIr (lift_inv_step (depth:=depth+1) (by injection eq))
  
  theorem lift_lift_eq_one
    (expr: Expr kind)
  :
    expr.lift.lift = expr.lift.lift 1
  :=
    lift_inv_step rfl
  
  theorem lift_zth
    (expr: Expr kind)
  :
    expr.lift.zth.lift = expr.lift.lift.zth
  :=
    congrArg zth (lift_lift_eq_one expr).symm
  
  theorem lift_fst
    (expr: Expr kind)
  :
    expr.lift.fst.lift = expr.lift.lift.fst
  :=
    congrArg fst (lift_lift_eq_one expr).symm
  
  
  theorem liftFvMapVar_comp
    (f g: Nat → Nat)
  :
    liftFvMapVar (f ∘ g) = (liftFvMapVar f) ∘ (liftFvMapVar g)
  :=
    funext fun
    | 0 => rfl
    | _ + 1 => rfl
  
  theorem liftFvMap_comp_var
    (f: Nat → Expr kind)
    (g: Nat → Nat)
  :
    liftFvMap (f ∘ g) = (liftFvMap f) ∘ (liftFvMapVar g)
  :=
    funext fun
    | 0 => rfl
    | _ + 1 => rfl
  
  theorem substVar_liftFvMapVar_subst
    (expr: Expr kind)
    (map: Nat → Nat)
  :
    Eq
      (substVar (liftFvMapVar map) expr)
      (subst (liftFvMap (var ∘ map)) expr)
  :=
    let mapEq: var ∘ (liftFvMapVar map) = liftFvMap (var ∘ map) :=
      funext fun
      | 0 => rfl
      | n + 1 => by
        show var (map n + 1) = var _
        rw [ite_eq_right (not_lt.mpr (Nat.zero_le _))]
    congrArg (subst · expr) mapEq
  
  theorem subst_comp_var
    (f: Nat → Expr kind)
    (g: Nat → Nat)
    (expr: Expr kind)
  :
    subst (f ∘ g) expr = subst f (substVar g expr)
  :=
    match expr with
    | const _ _ => rfl
    | var x => rfl
    | null => rfl
    | prod l r =>
      congrArg₂ prod (subst_comp_var f g l) (subst_comp_var f g r)
    | ir l r =>
      congrArg₂ ir (subst_comp_var f g l) (subst_comp_var f g r)
    | full body => congrArg full (subst_comp_var f g body)
    | compl body => congrArg compl (subst_comp_var f g body)
    | arbIr body =>
      congrArg
        arbIr
        (by
          rw [
            ←substVar_liftFvMapVar_subst body g,
            liftFvMap_comp_var,
            subst_comp_var (liftFvMap f) (liftFvMapVar g) body
          ])
  
  theorem substVar_comp
    (f g: Nat → Nat)
    (expr: Expr kind)
  :
    substVar (f ∘ g) expr = substVar f (substVar g expr)
  :=
    subst_comp_var (var ∘ f) g expr
  
  theorem substUnlift_comp_substLift
    (depth liftBy: Nat)
  :
    Eq
      ((substUnlift.fn depth liftBy) ∘ (substLift.fn depth liftBy))
      id
  :=
    funext fun y =>
      if h: y < depth then
        by
          dsimp [substUnlift.fn, substLift.fn]
          rw [ite_eq_left h, ite_eq_left h]
      else
        by
          let ge: depth ≤ y := Nat.le_of_not_lt h
          dsimp [substUnlift.fn, substLift.fn]
          rw [ite_eq_right h]
          rw [ite_eq_right (not_lt.mpr (Nat.le_trans ge (Nat.le_add_right _ _)))]
          exact Nat.add_sub_cancel y liftBy
  
  theorem liftFvMapVar_substLiftFun {depth liftBy}:
    Eq
      (liftFvMapVar (substLift.fn depth liftBy))
      (substLift.fn (depth + 1) liftBy)
  :=
    funext fun
    | 0 => rfl
    | n + 1 => by
      dsimp [liftFvMapVar, substLift.fn]
      if h : n < depth then
        rw [ite_eq_left h]
        rw [ite_eq_left (Nat.succ_lt_succ h)]
      else
        rw [ite_eq_right h]
        rw [ite_eq_right (not_lt.mpr (Nat.succ_le_succ (not_lt.mp h)))]
        rw [Nat.add_right_comm]
  
  theorem lift_eq_substLift
    (expr: Expr kind)
    (depth: Nat)
    (liftBy: Nat)
  :
    expr.lift depth liftBy = substLift expr depth liftBy
  :=
    match expr with
    | const _ _ => rfl
    | var _ => rfl
    | null => rfl
    | prod l r =>
      congrArg₂ prod (lift_eq_substLift l ..) (lift_eq_substLift r ..)
    | ir l r =>
      congrArg₂ ir (lift_eq_substLift l ..) (lift_eq_substLift r ..)
    | full body =>
      congrArg full (lift_eq_substLift body ..)
    | compl body =>
      congrArg compl (lift_eq_substLift body ..)
    | arbIr body =>
      congrArg
        arbIr
        (substVar_liftFvMapVar_subst body _ ▸
        liftFvMapVar_substLiftFun ▸
        lift_eq_substLift body (depth + 1) liftBy)
  
  theorem lift_substVar_eq
    (expr: Expr kind)
    (map: Nat → Nat)
  :
    Eq
      (substVar (liftFvMapVar map) (lift expr))
      (substVar map expr).lift
  := by
    rw [expr.lift_eq_substLift, lift_eq_substLift]
    rw [substLift, substLift]
    rw [←substVar_comp, ←substVar_comp]
    rfl
  
  theorem subst_liftFvMap_lift_general
    (k: Nat)
    (f: Nat → Expr kind)
    (expr: Expr kind)
    (h_safe: ∀ x, k ≤ x → (f x).lift 0 1 = (f x).lift k 1)
    (h_id: ∀ x, x < k → f x = var x)
  :
    subst (liftFvMap f) (expr.lift k 1) = (subst f expr).lift k 1
  :=
    match expr with
    | const _ _ => rfl
    | var x => by
      if h: x < k then
        rw [lift_var_lt x h 1]
        simp only [subst, liftFvMap]
        split
        next =>
          rw [h_id 0 h]
          rw [lift_var_lt 0 h 1]
        next y =>
          rw [h_id y (Nat.lt_trans (Nat.lt_succ_self y) h)]
          rw [lift_var_ge y (Nat.zero_le _) 1]
          rw [h_id (y + 1) h]
          rw [lift_var_lt (y + 1) h 1]
      else
        let ge := not_lt.mp h
        rw [lift_var_ge x ge 1]
        dsimp [subst, liftFvMap]
        exact h_safe x ge
    | null => rfl
    | prod l r =>
      congrArg₂
        prod
        (subst_liftFvMap_lift_general k f l h_safe h_id)
        (subst_liftFvMap_lift_general k f r h_safe h_id)
    | ir l r =>
      congrArg₂
        ir
        (subst_liftFvMap_lift_general k f l h_safe h_id)
        (subst_liftFvMap_lift_general k f r h_safe h_id)
    | full body =>
      congrArg full (subst_liftFvMap_lift_general k f body h_safe h_id)
    | compl body =>
      congrArg compl (subst_liftFvMap_lift_general k f body h_safe h_id)
    | arbIr body =>
      congrArg
        arbIr
        (subst_liftFvMap_lift_general (k + 1) (liftFvMap f) body
          (fun x hx =>
            match x with
            | 0 => (Nat.not_succ_le_zero k hx).elim
            | y + 1 =>
              lift_inv_step
                (k:=k)
                (depth:=0)
                (h_safe y (Nat.le_of_succ_le_succ hx)))
          (fun x hx =>
            match x with
            | 0 => rfl
            | y + 1 => by
              dsimp [liftFvMap]
              rw [h_id y (Nat.lt_of_succ_lt_succ hx)]
              exact lift_var_ge y (Nat.zero_le _) 1))

  theorem lift_subst_eq
    (f: Nat → Expr kind)
    (expr: Expr kind)
  :
    subst (liftFvMap f) expr.lift = (subst f expr).lift
  :=
    subst_liftFvMap_lift_general
      0
      f
      expr
      (fun _ _ => rfl)
      (fun x h => (Nat.not_lt_zero x h).elim)
  
  theorem subst_subst
    (f g: Nat → Expr kind)
    (expr: Expr kind)
  :
    subst f (subst g expr) = subst (fun x => subst f (g x)) expr
  :=
    match expr with
    | const _ _ => rfl
    | var x => rfl
    | null => rfl
    | prod l r =>
      congrArg₂ prod (subst_subst f g l) (subst_subst f g r)
    | ir l r =>
      congrArg₂ ir (subst_subst f g l) (subst_subst f g r)
    | full body => congrArg full (subst_subst f g body)
    | compl body => congrArg compl (subst_subst f g body)
    | arbIr body =>
      congrArg arbIr (by
        rw [subst_subst (liftFvMap f) (liftFvMap g) body]
        apply congrArg (subst · body)
        exact funext fun
        | 0 => rfl
        | n + 1 => lift_subst_eq f (g n))
  
  exposed def freeVarUb
    (expr: Expr kind)
  :
    Nat
  :=
    match expr with
    | .const _ _ => 0
    | .var x => x + 1
    | .null => 0
    | .prod left rite =>
        Nat.max left.freeVarUb rite.freeVarUb
    | .ir left rite =>
        Nat.max left.freeVarUb rite.freeVarUb
    | .full body => body.freeVarUb
    | .compl body => body.freeVarUb
    | .arbIr body => body.freeVarUb - 1
  
  theorem freeVarUb_lift_eq_depth
    (expr: Expr kind)
    (liftBy depth: Nat)
  :
    Eq
      ((expr.lift depth liftBy).freeVarUb - liftBy - depth)
      (expr.freeVarUb - depth)
  :=
    let max_eq {ml mr a b}:
      Nat.max ml mr - a - b = Nat.max (ml - a - b) (mr - a - b)
    := by
      rw [Nat.sub_sub, Nat.sub_sub, Nat.sub_sub]
      rw [←Nat.sub_max_sub_right]
      
    match expr with
    | .const _ _ => Nat.zero_sub _ ▸ rfl
    | .var x => by
      unfold lift freeVarUb
      split_ifs <;> omega
    | .null => Nat.zero_sub _ ▸ rfl
    | .prod l r => by
      show (Nat.max _ _) - _ - _ = _
      rw [max_eq]
      rw [freeVarUb_lift_eq_depth l liftBy depth]
      rw [freeVarUb_lift_eq_depth r liftBy depth]
      show _ = (Nat.max _ _) - _
      rw [←Nat.sub_max_sub_right]
    | .ir l r => by
      show (Nat.max _ _) - _ - _ = _
      rw [max_eq]
      rw [freeVarUb_lift_eq_depth l liftBy depth]
      rw [freeVarUb_lift_eq_depth r liftBy depth]
      show _ = (Nat.max _ _) - _
      rw [←Nat.sub_max_sub_right]
    | .full body =>
      freeVarUb_lift_eq_depth body liftBy depth
    | .compl body =>
      freeVarUb_lift_eq_depth body liftBy depth
    | .arbIr body => by
      let ih :=
        freeVarUb_lift_eq_depth body liftBy (depth + 1)
      show
        Eq
          ((body.lift (depth + 1) liftBy).freeVarUb - 1 - liftBy - depth)
          (body.freeVarUb - 1 - depth)
      omega
  
  theorem freeVarUb_le_lift
    {expr: Expr kind} {liftBy ub}
    (le: expr.freeVarUb ≤ ub)
  :
    (expr.lift 0 liftBy).freeVarUb ≤ ub + liftBy
  :=
    let eq := freeVarUb_lift_eq_depth expr liftBy 0
    Nat.le_add_of_sub_le (eq ▸ le)
  
  theorem freeVarUb_le_of_lift
    {expr: Expr kind} {liftBy ub}
    (le: (expr.lift 0 liftBy).freeVarUb ≤ ub + liftBy)
  :
    expr.freeVarUb ≤ ub
  := by
    let eq := freeVarUb_lift_eq_depth expr liftBy 0
    rw [Nat.sub_zero, Nat.sub_zero] at eq;
    rw [←eq];
    exact Nat.sub_le_of_le_add le
  
  theorem freeVarUb_freeVarLt {x}
    {expr: Expr kind}
    (uses: expr.UsesFreeVar x)
  :
    x < expr.freeVarUb
  :=
    match expr with
    | var _ => uses ▸ Nat.lt_succ_self _
    | prod _ _ =>
      match uses with
      | .inl h =>
        let ih := freeVarUb_freeVarLt h
        ih.trans_le (Nat.le_max_left _ _)
      | .inr h =>
        let ih := freeVarUb_freeVarLt h
        ih.trans_le (Nat.le_max_right _ _)
    | ir _ _ =>
      match uses with
      | .inl h =>
        let ih := freeVarUb_freeVarLt h
        ih.trans_le (Nat.le_max_left _ _)
      | .inr h =>
        let ih := freeVarUb_freeVarLt h
        ih.trans_le (Nat.le_max_right _ _)
    | full body =>
      let uses: body.UsesFreeVar x := uses
      freeVarUb_freeVarLt (expr:=body) uses
    | compl body =>
      let uses: body.UsesFreeVar x := uses
      freeVarUb_freeVarLt (expr:=body) uses
    | arbIr body =>
      let uses: body.UsesFreeVar (x+1) := uses
      let ih := freeVarUb_freeVarLt (expr:=body) uses
      Nat.le_sub_of_add_le ih
  
  theorem freeVarUb_bin_le_elim
    {a b: Expr kind} {n}
    (le: Nat.max a.freeVarUb b.freeVarUb ≤ n)
  :
    a.freeVarUb ≤ n ∧ b.freeVarUb ≤ n
  :=
    Nat.max_le.mp le
  
  theorem freeVarUb_bin_le_elimL
    {a b: Expr kind} {n}
    (le: Nat.max a.freeVarUb b.freeVarUb ≤ n)
  :
    a.freeVarUb ≤ n
  :=
    (freeVarUb_bin_le_elim le).left
  
  theorem freeVarUb_bin_le_elimR
    {a b: Expr kind} {n}
    (le: Nat.max a.freeVarUb b.freeVarUb ≤ n)
  :
    b.freeVarUb ≤ n
  :=
    (freeVarUb_bin_le_elim le).right
  
  theorem freeVarUb_bin_le
    {a b: Expr kind} {n}
    (leA: a.freeVarUb ≤ n)
    (leB: b.freeVarUb ≤ n)
  :
    Nat.max a.freeVarUb b.freeVarUb ≤ n
  :=
    Nat.max_le.mpr ⟨leA, leB⟩
  
  theorem substId_eq
    (expr: Expr kind)
  :
    expr.substId = expr
  :=
    match expr with
    | const _ _ => rfl
    | var _ => rfl
    | null => rfl
    | prod l r =>
      congrArg₂ prod l.substId_eq r.substId_eq
    | ir l r =>
      congrArg₂ ir l.substId_eq r.substId_eq
    | full body => congrArg full body.substId_eq
    | compl body => congrArg compl body.substId_eq
    | arbIr body =>
      let liftEq:
        (liftFvMap fun x => var x) = (fun x => var x)
      :=
        funext fun | 0 => rfl | _+1 => rfl
      congrArg arbIr (liftEq.symm ▸ body.substId_eq)
  
  theorem lift_instantiateVar_eq
    (expr: Expr kind)
    (t: Expr kind)
  :
    expr.lift.instantiateVar t = expr
  := by
    let succEq: substLift.fn 0 1 = Nat.succ := funext fun _ => rfl
    rw [instantiateVar]
    rw [lift_eq_substLift expr 0 1, substLift, succEq]
    rw [←subst_comp_var (instantiateVar.fn t) Nat.succ expr]
    exact substId_eq expr
  
  theorem lift_pos_instantiateVar_eq
    (expr: Expr kind)
    (t: Expr kind)
    (n: Nat)
  :
    (expr.lift 0 n.succ).instantiateVar t = expr.lift 0 n
  := by
    rw [instantiateVar, lift_eq_substLift expr 0 n.succ]
    rw [substLift, ←subst_comp_var]
    rw [lift_eq_substLift expr 0 n]
    rfl
  
  theorem lift_d1_instantiateVar_eq
    (expr: Expr kind)
  :
    (expr.lift 1).instantiateVar (var 0) = expr
  := by
    let fnEq:
      Eq
        (instantiateVar.fn (var (kind := kind) 0))
        (var ∘ (substUnlift.fn 1 1))
    :=
      funext fun x =>
      match x with
      | 0 => rfl
      | n + 1 =>
        show var n = var (n + 1 - 1) by
        rw [Nat.succ_sub_one]
    rw [instantiateVar, fnEq]
    rw [lift_eq_substLift expr 1 1, substLift]
    show substVar (substUnlift.fn 1 1) (substVar (substLift.fn 1 1) expr) = expr
    rw [←substVar_comp]
    rw [substUnlift_comp_substLift]
    exact substId_eq expr
  
  theorem substVar_substUnlift_substLift_eq
    (expr: Expr kind)
    (depth liftBy: Nat)
  :
    Eq
      (substVar
        (substUnlift.fn depth liftBy)
        (substVar (substLift.fn depth liftBy) expr))
      expr
  := by
    rw [←substVar_comp]
    rw [substUnlift_comp_substLift]
    exact substId_eq expr

  theorem substVar_substUnlift_lift_eq
    (expr: Expr kind)
    (depth liftBy: Nat)
  :
    Eq
      (substVar
        (substUnlift.fn depth liftBy)
        (expr.lift depth liftBy))
      expr
  := by
    rw [lift_eq_substLift expr depth liftBy, substLift]
    exact substVar_substUnlift_substLift_eq expr depth liftBy
  
  
  theorem subst_eq_of_freeVarLt
    {expr: Expr kind}
    (bound: Nat)
    (freeVarLt: ∀ x, expr.UsesFreeVar x → x < bound)
    (map: Nat → Expr kind)
    (map_id_lt: ∀ x, x < bound → map x = var x)
  :
    subst map expr = expr
  := by
    induction expr generalizing bound map with
    | const _ _ =>
      rfl
    | var x =>
      let ltBound := freeVarLt x rfl
      show (map x) = var x
      rw [map_id_lt x ltBound]
    | null =>
      rfl
    | prod l r ihL ihR =>
      let varLtL x h := freeVarLt x (Or.inl h)
      let varLtR x h := freeVarLt x (Or.inr h)
      exact congrArg₂ prod
        (ihL bound varLtL map map_id_lt)
        (ihR bound varLtR map map_id_lt)
    | ir l r ihL ihR =>
      let varLtL x h := freeVarLt x (Or.inl h)
      let varLtR x h := freeVarLt x (Or.inr h)
      exact congrArg₂ ir
        (ihL bound varLtL map map_id_lt)
        (ihR bound varLtR map map_id_lt)
    | full body ih =>
      exact congrArg full
        (ih bound (fun x h => freeVarLt x h) map map_id_lt)
    | compl body ih =>
      exact congrArg Expr.compl
        (ih bound (fun x h => freeVarLt x h) map map_id_lt)
    | arbIr body ih =>
      let ihBody:
        subst (liftFvMap map) body = body
      :=
        ih
          (bound + 1)
          (fun
            | 0, _ => Nat.zero_lt_succ _
            | x + 1, h =>
              Nat.succ_lt_succ (freeVarLt x h))
          (liftFvMap map)
          (fun
            | 0, _ => rfl
            | x + 1, lt =>
              let mapId := map_id_lt x (Nat.lt_of_succ_lt_succ lt)
              show lift _ = _ from
              mapId ▸ rfl)
      exact congrArg arbIr ihBody
  
  theorem substVar_eq_of_isClean
    {expr: Expr kind}
    (isClean: Expr.IsClean expr)
    (map: Nat → Nat)
  :
    substVar map expr = expr
  :=
    subst_eq_of_freeVarLt
      0
      (fun x hx => (isClean x hx).elim)
      (var ∘ map)
      (fun x h => (Nat.not_lt_zero x h).elim)
  
end Expr

namespace Expr
  theorem intp_lift_eq_depth
    (expr: Expr kind)
    (lane: kind.Lane)
    (b c: Valuation Pair)
    (fv fvDepth fvLiftBy: List Pair)
  :
    Eq
      (expr.intp lane b c (fvDepth ++ fv))
      ((expr.lift fvDepth.length fvLiftBy.length).intp
        lane
        b
        c
        (fvDepth ++ fvLiftBy ++ fv))
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => by
      show
        Eq
          (intpVar (fvDepth ++ fv) x)
          (intpVar
            (fvDepth ++ fvLiftBy ++ fv)
            (if x < fvDepth.length then x else x + fvLiftBy.length))
      unfold intpVar
      rw [List.append_assoc]
      split_ifs with h1
      · rw [List.getElem?_append_left h1]
        rw [List.getElem?_append_left h1]
      · rw [List.getElem?_append_right (Nat.le_of_not_lt h1)]
        rw [
          List.getElem?_append_right
            (Nat.le_trans (Nat.le_of_not_lt h1) (Nat.le_add_right _ _))]
        rw [List.getElem?_append_right]
        · congr 1
          rw [Nat.sub_sub]
          rw [Nat.add_sub_add_right]
        · rw [
            Nat.le_sub_iff_add_le
              (Nat.le_trans (Nat.le_of_not_lt h1) (Nat.le_add_right _ _))]
          rw [Nat.add_comm fvLiftBy.length fvDepth.length]
          exact Nat.add_le_add_right (Nat.le_of_not_lt h1) fvLiftBy.length
    | .null => rfl
    | .prod l r =>
      eq_intp_prod_of_eq
        (l.intp_lift_eq_depth lane b c fv fvDepth fvLiftBy)
        (r.intp_lift_eq_depth lane b c fv fvDepth fvLiftBy)
    | .ir l r =>
      eq_intp_ir_of_eq
        (l.intp_lift_eq_depth lane b c fv fvDepth fvLiftBy)
        (r.intp_lift_eq_depth lane b c fv fvDepth fvLiftBy)
    | .full body =>
      eq_intp_full_of_eq
        (body.intp_lift_eq_depth lane b c fv fvDepth fvLiftBy)
    | .compl body =>
      eq_intp_compl_of_eq
        (body.intp_lift_eq_depth lane.toggle c b fv fvDepth fvLiftBy)
    | .arbIr body =>
      eq_intp_arbIr_of_eq fun p =>
        body.intp_lift_eq_depth lane b c fv (p :: fvDepth) fvLiftBy
  
  theorem intp_lift_eq
    (expr: Expr kind)
    (lane: kind.Lane)
    (b c: Valuation Pair)
    (fv fvLiftBy: List Pair)
  :
    Eq
      (expr.intp lane b c fv)
      ((expr.lift 0 fvLiftBy.length).intp lane b c (fvLiftBy ++ fv))
  :=
    expr.intp_lift_eq_depth lane b c fv [] fvLiftBy
  
  theorem intp_lift_head_eq
    (expr: Expr kind)
    (lane: kind.Lane)
    (pA pB: Pair)
    (fv: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.lift.intp lane b c (pA :: fv))
      (expr.lift.intp lane b c (pB :: fv))
  :=
    (expr.intp_lift_eq lane b c fv [pA]).symm.trans
      (expr.intp_lift_eq lane b c fv [pB])
  
  
  theorem intp_subst_eq
    {fvMap: Nat → Expr kind}
    {expr: Expr kind}
    {lane b c fvLeft fvRite}
    (fvEq:
      ∀ x,
        expr.UsesFreeVar x →
        intpVar fvLeft x = (fvMap x).intp lane b c fvRite)
    (fvEqCpl:
      ∀ x,
        expr.UsesFreeVar x →
        intpVar fvLeft x = (fvMap x).intp lane.toggle c b fvRite)
  :
    Eq
      (expr.intp lane b c fvLeft)
      ((expr.subst fvMap).intp lane b c fvRite)
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => fvEq x rfl
    | .null => rfl
    | .prod _ _ =>
      eq_intp_prod_of_eq
        (intp_subst_eq
          (fun x h => fvEq x (Or.inl h))
          (fun x h => fvEqCpl x (Or.inl h)))
        (intp_subst_eq
          (fun x h => fvEq x (Or.inr h))
          (fun x h => fvEqCpl x (Or.inr h)))
    | .ir _ _ =>
      eq_intp_ir_of_eq
        (intp_subst_eq
          (fun x h => fvEq x (Or.inl h))
          (fun x h => fvEqCpl x (Or.inl h)))
        (intp_subst_eq
          (fun x h => fvEq x (Or.inr h))
          (fun x h => fvEqCpl x (Or.inr h)))
    | .full body =>
      eq_intp_full_of_eq
        (intp_subst_eq (expr := body) fvEq fvEqCpl)
    | .compl body =>
      eq_intp_compl_of_eq
        (intp_subst_eq
          (expr := body)
          (lane := lane.toggle)
          fvEqCpl
          (fun x h =>
            intp_toggle_toggle_eq (fvMap x) lane _ _ _ ▸ 
            fvEq x h))
    | .arbIr body =>
      let fvMap': Nat → Expr kind := Expr.liftFvMap fvMap
      let fvEqLifted (l: kind.Lane) {b c}
        (hyp:
          ∀ x,
            (arbIr body).UsesFreeVar x →
            intpVar fvLeft x = (fvMap x).intp l b c fvRite)
        (p: Pair)
        (x: Nat)
        (h: body.UsesFreeVar x)
      :
        intpVar (p :: fvLeft) x = (fvMap' x).intp l b c (p :: fvRite)
      :=
        match x with
        | 0 => rfl
        | x + 1 =>
          (fvMap x).intp_lift_eq l b c fvRite [p] ▸ hyp x h
      
      eq_intp_arbIr_of_eq fun p =>
        intp_subst_eq
          (fvEqLifted lane fvEq p)
          (fvEqLifted lane.toggle (b := c) (c := b) fvEqCpl p)
  
  theorem intp_substVar_eq
    {fvMap: Nat → Nat}
    {expr: Expr kind}
    {lane b c fvLeft fvRite}
    (fvEq: ∀ x, expr.UsesFreeVar x → fvLeft[x]? = fvRite[fvMap x]?)
  :
    Eq
      (expr.intp lane b c fvLeft)
      ((expr.substVar fvMap).intp lane b c fvRite)
  :=
    intp_subst_eq
      (fun x hx =>
        congrArg
          (fun | .none => (∅: Set Pair) | .some p => {p})
          (fvEq x hx))
      (fun x hx =>
        congrArg
          (fun | .none => (∅: Set Pair) | .some p => {p})
          (fvEq x hx))
  
  
  theorem intp_instantiateVar_eq
    (expr t: Expr kind)
    {lane b c fv pB}
    (t_eq: t.intp lane b c fv = {pB})
    (t_eq_cpl: t.intp lane.toggle c b fv = {pB})
  :
    Eq
      (expr.intp lane b c (pB :: fv))
      ((expr.instantiateVar t).intp lane b c fv)
  :=
    intp_subst_eq
      (fun
        | 0, _ => t_eq ▸ rfl
        | _ + 1, _ => rfl)
      (fun
        | 0, _ => t_eq_cpl ▸ rfl
        | _ + 1, _ => rfl)
  
  
  theorem intp_clearFreeVars_eq
    (expr: Expr kind)
    {lane b c fv}
  :
    expr.intp lane b c [] = expr.clearFreeVars.intp lane b c fv
  :=
    intp_subst_eq
      (fun _ _ => intp_none_eq_empty ▸ rfl)
      (fun _ _ => intp_none_eq_empty ▸ rfl)
  
  
  theorem intp_bv_append
    {expr: Expr kind}
    {lane b c fv}
    (ubLe: expr.freeVarUb ≤ fv.length)
    (rest: List Pair)
  :
    expr.intp lane b c fv = expr.intp lane b c (fv ++ rest)
  :=
    let eq:
      expr.intp lane b c fv = expr.substId.intp lane b c (fv ++ rest)
    :=
      intp_substVar_eq
        (fun x xUsed =>
          let ltUb := expr.freeVarUb_freeVarLt xUsed
          let ltFv: x < fv.length := ltUb.trans_le ubLe
          (List.getElem?_append_left ltFv).symm)
    by rw [expr.substId_eq] at eq; exact eq
  
end Expr

theorem Expr.IsClean.intp_eq {lane b c fvL fvR}
  {expr: Expr kind}
  (h: Expr.IsClean expr)
:
  expr.intp lane b c fvL = intp expr lane b c fvR
:=
  let nope {P: Nat → Prop}: ∀ x, expr.UsesFreeVar x → P x :=
    fun x hx => (h x hx).elim
  let eqL := intp_subst_eq nope nope
  let eqR := intp_subst_eq nope nope
  let middle := intp expr.clearFreeVars lane b c []
  eqL.trans (b := middle) eqR.symm

namespace DefList
  theorem intp_getDef_eq_fv
    (dl: DefList)
    (x: Nat)
    (lane: Set3.Lane)
    (b c: Valuation Pair)
    (fv0 fv1: List Pair)
  :
    Eq
      ((dl.getDef x).intp lane b c fv0)
      ((dl.getDef x).intp lane b c fv1)
  :=
    (dl.isClean x).intp_eq
  
  theorem triIntp_getDef_eq_fv
    (dl: DefList)
    (x: Nat)
    (b c: Valuation Pair)
    (fv0 fv1: List Pair)
  :
    (dl.getDef x).triIntp b c fv0 = (dl.getDef x).triIntp b c fv1
  :=
    Set3.eq
      (dl.intp_getDef_eq_fv x .defLane b c fv0 fv1)
      (dl.intp_getDef_eq_fv x .posLane b c fv0 fv1)
  
end DefList

namespace DefList
  variable {dl: DefList}
  
  theorem InWfm.of_in_def {x lane fv d}
    (inDef: dl.InWfm (dl.getDef x) lane fv d)
  :
    dl.InWfm (.const () x) lane [] d
  :=
    of_in_def_no_fv <|
    show d ∈ (dl.getDef x).intp lane dl.wfm dl.wfm [] from
    (dl.intp_getDef_eq_fv x lane dl.wfm dl.wfm fv []).symm ▸ inDef
  
  theorem InWfm.in_def {x lane fv d}
    (inVar: dl.InWfm (.const () x) lane [] d)
  :
    dl.InWfm (dl.getDef x) lane fv d
  :=
    show d ∈ (dl.getDef x).intp lane dl.wfm dl.wfm fv from
    (dl.intp_getDef_eq_fv x lane dl.wfm dl.wfm fv []).symm ▸
    in_def_no_fv inVar
  
  -- Like the two lemmas above, but with a `Expr.toLane` conversion.
  theorem InWfm.in_def_toLane {x lane fv d}
    (inConst:
      d ∈ (Expr.const (kind := .lane) lane x).intp () dl.wfm dl.wfm [])
  :
    d ∈ ((dl.getDef x).toLane lane).intp () dl.wfm dl.wfm fv
  :=
    (Expr.toLane_intp (dl.getDef x) lane dl.wfm dl.wfm fv).symm ▸
    (dl.intp_getDef_eq_fv x lane dl.wfm dl.wfm [] fv) ▸
    in_def_no_fv inConst

  theorem InWfm.of_in_def_toLane {x lane fv d}
    (inDef:
      d ∈ ((dl.getDef x).toLane lane).intp () dl.wfm dl.wfm fv)
  :
    d ∈ (Expr.const (kind := .lane) lane x).intp () dl.wfm dl.wfm []
  :=
    of_in_def_no_fv <|
    show d ∈ (dl.getDef x).intp lane dl.wfm dl.wfm [] from
    (dl.intp_getDef_eq_fv x lane dl.wfm dl.wfm fv []).symm ▸
    (Expr.toLane_intp (dl.getDef x) lane dl.wfm dl.wfm fv) ▸
    inDef

end DefList
