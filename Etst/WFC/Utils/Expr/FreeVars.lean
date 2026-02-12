import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.Expr.ConstsVarsSat

namespace Etst

variable {E: Type*}


namespace Expr
  def substVar
    (fvMap: Nat → Nat)
  :
    Expr E → Expr E
  :=
    subst (var ∘ fvMap)
  
  def instantiateVar.fn (t: Expr E): Nat → Expr E
  | 0 => t
  | n + 1 => var n
  
  def instantiateVar
    (expr: Expr E)
    (t: Expr E)
  :
    Expr E
  :=
    expr.subst (instantiateVar.fn t)
  
  def substId {E}: Expr E → Expr E := substVar id  
  
  def substLift.fn (depth liftBy: Nat) :=
    fun x => if x < depth then x else x + liftBy
  
  -- Redefining `lift` using `substVar`, so we can use composition
  -- properties of `substVar` to prove properties of `lift`.
  def substLift
    (expr: Expr E)
    (depth: Nat)
    (liftBy: Nat)
  :
    Expr E
  :=
    expr.substVar (substLift.fn depth liftBy)
  
  
  def liftFvMapVar
    (fvMap: Nat → Nat)
  :
    Nat → Nat
  | 0 => 0
  | n + 1 => (fvMap n) + 1
  
  def lift_var_lt
    (x: Nat)
    {depth} (lt: x < depth)
    (liftBy: Nat)
  :
    (var (E := E) x).lift depth liftBy = var x
  :=
    show var _ = _ from if_pos lt ▸ rfl
  
  def lift_var_ge
    (x: Nat)
    {depth} (ge: depth ≤ x)
    (liftBy: Nat)
  :
    (var (E := E) x).lift depth liftBy = var (x + liftBy)
  :=
    show var _ = _ from if_neg (not_lt.mpr ge) ▸ rfl
  
  def lift_zero_eq
    (expr: Expr E)
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
    | pair l r =>
      congrArg₂
        pair
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
  
  def lift_add_eq
    (expr: Expr E)
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
    | pair l r =>
      congrArg₂
        pair
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
  
  def lift_inj
    {a b: Expr E} {depth liftBy}
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
    | pair al ar, pair bl br => by
      injection eq with eql eqr
      exact congrArg₂ pair (lift_inj eql) (lift_inj eqr)
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
  
  
  def liftFvMapVar_comp
    (f g: Nat → Nat)
  :
    liftFvMapVar (f ∘ g) = (liftFvMapVar f) ∘ (liftFvMapVar g)
  :=
    funext fun
    | 0 => rfl
    | _ + 1 => rfl
  
  def liftFvMap_comp_var
    (f: Nat → Expr E)
    (g: Nat → Nat)
  :
    liftFvMap (f ∘ g) = (liftFvMap f) ∘ (liftFvMapVar g)
  :=
    funext fun
    | 0 => rfl
    | _ + 1 => rfl
  
  def substVar_liftFvMapVar_subst
    (expr: Expr E)
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
        rw [if_neg (not_lt.mpr (Nat.zero_le _))]
    congrArg (subst · expr) mapEq
  
  def subst_comp_var
    (f: Nat → Expr E)
    (g: Nat → Nat)
    (expr: Expr E)
  :
    subst (f ∘ g) expr = subst f (substVar g expr)
  :=
    match expr with
    | const _ _ => rfl
    | var x => rfl
    | null => rfl
    | pair l r =>
      congrArg₂ pair (subst_comp_var f g l) (subst_comp_var f g r)
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
  
  def substVar_comp
    (f g: Nat → Nat)
    (expr: Expr E)
  :
    substVar (f ∘ g) expr = substVar f (substVar g expr)
  :=
    subst_comp_var (var ∘ f) g expr
  
  def liftFvMapVar_substLiftFun {depth liftBy}:
    Eq
      (liftFvMapVar (substLift.fn depth liftBy))
      (substLift.fn (depth + 1) liftBy)
  :=
    funext fun
    | 0 => rfl
    | n + 1 => by
      dsimp [liftFvMapVar, substLift.fn]
      if h : n < depth then
        rw [if_pos h]
        rw [if_pos (Nat.succ_lt_succ h)]
      else
        rw [if_neg h]
        rw [if_neg (not_lt.mpr (Nat.succ_le_succ (not_lt.mp h)))]
        rw [Nat.add_right_comm]
  
  def lift_eq_substLift
    (expr: Expr E)
    (depth: Nat)
    (liftBy: Nat)
  :
    expr.lift depth liftBy = substLift expr depth liftBy
  :=
    match expr with
    | const _ _ => rfl
    | var _ => rfl
    | null => rfl
    | pair l r =>
      congrArg₂ pair (lift_eq_substLift l ..) (lift_eq_substLift r ..)
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
  
  def lift_substVar_eq
    (expr: Expr E)
    (map: Nat → Nat)
  :
    Eq
      (substVar (liftFvMapVar map) (lift expr))
      (substVar map expr).lift
  := by
    rw [expr.lift_eq_substLift 0 1, lift_eq_substLift _ 0 1]
    rw [substLift, substLift]
    rw [←substVar_comp, ←substVar_comp]
    rfl
  
  
  def instantiateVar_lift_eq_depth
    (expr: Expr E)
    (f: Nat → Expr E)
    (depth: Nat)
    (eq_lt: ∀ x, x < depth → f x = var x)
    (eq_ge: ∀ x, depth ≤ x → f x.succ = var x)
  :
    (expr.lift depth 1).subst f = expr
  :=
    match expr with
    | const _ _ => rfl
    | var x =>
      if h: depth ≤ x then
        lift_var_ge x h 1 ▸ eq_ge x h
      else
        let lt := not_le.mp h
        (lift_var_lt x lt 1).symm ▸ eq_lt x lt
    | null => rfl
    | pair l r =>
      congrArg₂
        pair
        (l.instantiateVar_lift_eq_depth f depth eq_lt eq_ge)
        (r.instantiateVar_lift_eq_depth f depth eq_lt eq_ge)
    | ir l r =>
      congrArg₂
        ir
        (l.instantiateVar_lift_eq_depth f depth eq_lt eq_ge)
        (r.instantiateVar_lift_eq_depth f depth eq_lt eq_ge)
    | full body =>
      congrArg
        full
        (body.instantiateVar_lift_eq_depth f depth eq_lt eq_ge)
    | compl body =>
      congrArg
        compl
        (body.instantiateVar_lift_eq_depth f depth eq_lt eq_ge)
    | arbIr body =>
      congrArg
        arbIr
        (body.instantiateVar_lift_eq_depth
          (liftFvMap f)
          depth.succ
          (fun x hx =>
            match x with
            | 0 => rfl
            | x + 1 => by
              show (f x).lift = var (x + 1)
              rw [eq_lt x (Nat.lt_of_succ_lt_succ hx)]
              exact lift_var_ge x (Nat.zero_le _) 1)
          (fun x hx => by
            match x with
            | 0 => exact (Nat.not_succ_le_zero depth hx).elim
            | x + 1 =>
              show (f (x + 1)).lift = var (x + 1)
              rw [eq_ge x (Nat.le_of_succ_le_succ hx)]
              exact lift_var_ge x (Nat.zero_le _) 1))
  
  def instantiateVar_lift_eq
    (expr: Expr E)
    (t: Expr E)
  :
    expr.lift.instantiateVar t = expr
  :=
    expr.instantiateVar_lift_eq_depth
      (fun | 0 => t | x + 1 => var x)
      0
      nofun
      (fun _ _ => rfl)
  
  def freeVarUb
    (expr: Expr E)
  :
    Nat
  :=
    match expr with
    | .const _ _ => 0
    | .var x => x + 1
    | .null => 0
    | .pair left rite =>
        Nat.max left.freeVarUb rite.freeVarUb
    | .ir left rite =>
        Nat.max left.freeVarUb rite.freeVarUb
    | .full body => body.freeVarUb
    | .compl body => body.freeVarUb
    | .arbIr body => body.freeVarUb - 1
  
  def freeVarUb_lift_eq_depth
    (expr: Expr E)
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
    | .pair l r => by
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
      show (body.lift (depth + 1) liftBy).freeVarUb - 1 - liftBy - depth =
        body.freeVarUb - 1 - depth
      omega
  
  def freeVarUb_le_lift
    {expr: Expr E} {liftBy ub}
    (le: expr.freeVarUb ≤ ub)
  :
    (expr.lift 0 liftBy).freeVarUb ≤ ub + liftBy
  :=
    let eq := freeVarUb_lift_eq_depth expr liftBy 0
    Nat.le_add_of_sub_le (eq ▸ le)
  
  def freeVarUb_freeVarLt {x}
    {expr: Expr E}
    (uses: expr.UsesFreeVar x)
  :
    x < expr.freeVarUb
  :=
    match expr with
    | var _ => uses ▸ Nat.lt_succ_self _
    | pair _ _ =>
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
  
  def freeVarUb_bin_le_elim
    {a b: Expr E} {n}
    (le: Nat.max a.freeVarUb b.freeVarUb ≤ n)
  :
    a.freeVarUb ≤ n ∧ b.freeVarUb ≤ n
  :=
    Nat.max_le.mp le
  
  def freeVarUb_bin_le_elimL
    {a b: Expr E} {n}
    (le: Nat.max a.freeVarUb b.freeVarUb ≤ n)
  :
    a.freeVarUb ≤ n
  :=
    (freeVarUb_bin_le_elim le).left
  
  def freeVarUb_bin_le_elimR
    {a b: Expr E} {n}
    (le: Nat.max a.freeVarUb b.freeVarUb ≤ n)
  :
    b.freeVarUb ≤ n
  :=
    (freeVarUb_bin_le_elim le).right
  
  def freeVarUb_bin_le
    {a b: Expr E} {n}
    (leA: a.freeVarUb ≤ n)
    (leB: b.freeVarUb ≤ n)
  :
    Nat.max a.freeVarUb b.freeVarUb ≤ n
  :=
    Nat.max_le.mpr ⟨leA, leB⟩
  
  def substId_eq
    (expr: Expr E)
  :
    expr.substId = expr
  :=
    match expr with
    | const _ _ => rfl
    | var _ => rfl
    | null => rfl
    | pair l r =>
      congrArg₂ pair (l.substId_eq) (r.substId_eq)
    | ir l r =>
      congrArg₂ ir (l.substId_eq) (r.substId_eq)
    | full body => congrArg full (body.substId_eq)
    | compl body => congrArg compl (body.substId_eq)
    | arbIr body =>
      let liftEq:
        (liftFvMap fun x => var (E := E) x) = (fun x => var x)
      :=
        funext fun | 0 => rfl | _+1 => rfl
      congrArg arbIr (liftEq.symm ▸ body.substId_eq)
  
end Expr

namespace SingleLaneExpr
  def intp2_lift_eq_depth
    (expr: SingleLaneExpr)
    (fv fvDepth fvLiftBy: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 (fvDepth ++ fv) b c)
      (SingleLaneExpr.intp2
        (expr.lift fvDepth.length fvLiftBy.length)
        (fvDepth ++ fvLiftBy ++ fv)
        b
        c)
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
    | .pair l r =>
      eq_intp2_pair_of_eq
        (intp2_lift_eq_depth l fv fvDepth fvLiftBy b c)
        (intp2_lift_eq_depth r fv fvDepth fvLiftBy b c)
    | .ir l r =>
      eq_intp2_ir_of_eq
        (intp2_lift_eq_depth l fv fvDepth fvLiftBy b c)
        (intp2_lift_eq_depth r fv fvDepth fvLiftBy b c)
    | .full body =>
      eq_intp2_full_of_eq
        (intp2_lift_eq_depth body fv fvDepth fvLiftBy b c)
    | .compl body =>
      eq_intp2_compl_of_eq
        (intp2_lift_eq_depth body fv fvDepth fvLiftBy c b)
    | .arbIr body =>
      eq_intp2_arbIr_of_eq fun d =>
        intp2_lift_eq_depth body fv (d :: fvDepth) fvLiftBy b c
  
  def intp2_lift_eq
    (expr: SingleLaneExpr)
    (fv fvLiftBy: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      (expr.intp2 fv b c)
      (intp2 (expr.lift 0 fvLiftBy.length) (fvLiftBy ++ fv) b c)
  :=
    intp2_lift_eq_depth expr fv [] fvLiftBy b c
  
  def intp_lift_eq
    (expr: SingleLaneExpr)
    (fv fvLiftBy: List Pair)
    (v: Valuation Pair)
  :
    Eq
      (expr.intp fv v)
      (intp (expr.lift 0 fvLiftBy.length) (fvLiftBy ++ fv) v)
  :=
    intp2_lift_eq expr fv fvLiftBy v v
  
  
  def intp2_subst_eq
    {fvMap: Nat → SingleLaneExpr}
    {expr: SingleLaneExpr}
    {b c: Valuation Pair}
    {fvLeft fvRite}
    (fvEq:
      ∀ x ∈ expr.UsesFreeVar,
        intpVar fvLeft x = (fvMap x).intp2 fvRite b c)
    (fvEqCpl:
      ∀ x ∈ expr.UsesFreeVar,
        intpVar fvLeft x = (fvMap x).intp2 fvRite c b)
  :
    Eq
      (expr.intp2 fvLeft b c)
      (intp2 (expr.subst fvMap) fvRite b c)
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => fvEq x rfl
    | .null => rfl
    | .pair _ _ =>
      eq_intp2_pair_of_eq
        (intp2_subst_eq
          (fun x h => fvEq x (Or.inl h))
          (fun x h => fvEqCpl x (Or.inl h)))
        (intp2_subst_eq
          (fun x h => fvEq x (Or.inr h))
          (fun x h => fvEqCpl x (Or.inr h)))
    | .ir _ _ =>
      eq_intp2_ir_of_eq
        (intp2_subst_eq
          (fun x h => fvEq x (Or.inl h))
          (fun x h => fvEqCpl x (Or.inl h)))
        (intp2_subst_eq
          (fun x h => fvEq x (Or.inr h))
          (fun x h => fvEqCpl x (Or.inr h)))
    | .full body =>
      eq_intp2_full_of_eq
        (intp2_subst_eq (expr := body) fvEq fvEqCpl)
    | .compl body =>
      eq_intp2_compl_of_eq
        (intp2_subst_eq (expr := body) fvEqCpl fvEq)
    | .arbIr body =>
      let fvMap': Nat → SingleLaneExpr := Expr.liftFvMap fvMap
      let fvEqLifted {b c}
        (hyp:
          ∀ x ∈ (arbIr body).UsesFreeVar,
            intpVar fvLeft x = (fvMap x).intp2 fvRite b c)
        (d: Pair)
        (x: Nat)
        (h: x ∈ body.UsesFreeVar)
      :
        intpVar (d :: fvLeft) x = (fvMap' x).intp2 (d :: fvRite) b c
      :=
        match x with
        | 0 => rfl
        | x + 1 =>
          intp2_lift_eq (fvMap x) fvRite [d] b c ▸ hyp x h
      
      eq_intp2_arbIr_of_eq fun d =>
        intp2_subst_eq
          (fvEqLifted fvEq d)
          (fvEqLifted fvEqCpl d)
  
  def intp_subst_eq
    {fvMap: Nat → SingleLaneExpr}
    {expr: SingleLaneExpr}
    {fvLeft fvRite v}
    (fvEq:
      ∀ x ∈ expr.UsesFreeVar,
        intpVar fvLeft x = (fvMap x).intp fvRite v)
  :
    Eq
      (expr.intp2 fvLeft v v)
      (intp2 (expr.subst fvMap) fvRite v v)
  :=
    intp2_subst_eq fvEq fvEq
  
  def intp2_substVar_eq
    {fvMap: Nat → Nat}
    {expr: SingleLaneExpr}
    {b c: Valuation Pair}
    {fvLeft fvRite}
    (fvEq: ∀ x ∈ expr.UsesFreeVar, fvLeft[x]? = fvRite[fvMap x]?)
  :
    Eq
      (expr.intp2 fvLeft b c)
      (intp2 (expr.substVar fvMap) fvRite b c)
  :=
    (fun ab a => ab a a)
      intp2_subst_eq
      (fun x hx =>
        congrArg
          (fun | .none => (∅: Set Pair) | .some d => {d})
          (fvEq x hx))
  
  
  def intp2_instantiateVar_eq
    (expr: SingleLaneExpr)
    (t: SingleLaneExpr)
    {fv b c dB}
    (t_eq: t.intp2 fv b c = {dB})
    (t_eq_c: t.intp2 fv c b = {dB})
  :
    expr.intp2 (dB :: fv) b c = intp2 (expr.instantiateVar t) fv b c
  :=
    intp2_subst_eq
      (fun
        | 0, _ => t_eq ▸ rfl
        | _ + 1, _ => rfl)
      (fun
        | 0, _ => t_eq_c ▸ rfl
        | _ + 1, _ => rfl)
  
  def intp_instantiateVar_eq
    (expr: SingleLaneExpr)
    (t: SingleLaneExpr)
    {fv v dB}
    (t_eq: t.intp fv v = {dB})
  :
    expr.intp (dB :: fv) v = intp (expr.instantiateVar t) fv v
  :=
    intp_subst_eq (fun
      | 0, _ => t_eq ▸ rfl
      | _ + 1, _ => rfl)
  
  
  def intp2_clearFreeVars_eq
    (expr: SingleLaneExpr)
    {fv b c}
  :
    expr.intp2 [] b c = intp2 (expr.clearFreeVars) fv b c
  :=
    intp2_subst_eq
      (fun _ _ => intp2_none_eq_empty ▸ rfl)
      (fun _ _ => intp2_none_eq_empty ▸ rfl)
  
  
  def intp2_bv_append
    {expr: SingleLaneExpr}
    {fv b c} (ubLe: expr.freeVarUb ≤ fv.length)
    (rest: List Pair)
  :
    expr.intp2 fv b c = expr.intp2 (fv ++ rest) b c
  :=
    let eq: expr.intp2 fv b c = intp2 expr.substId (fv ++ rest) b c :=
      intp2_substVar_eq
        (fun x xUsed =>
          let ltUb := expr.freeVarUb_freeVarLt xUsed
          let ltFv: x < fv.length := ltUb.trans_le ubLe
          (List.getElem?_append_left ltFv).symm)
    by rw [expr.substId_eq] at eq; exact eq
  
  def intp_bv_append
    {expr: SingleLaneExpr}
    {fv v} (ubLe: expr.freeVarUb ≤ fv.length)
    (rest: List Pair)
  :
    expr.intp fv v = expr.intp (fv ++ rest) v
  :=
    intp2_bv_append ubLe rest
  
end SingleLaneExpr

namespace BasicExpr
  def toLane_UsesFreeVar
    (expr: BasicExpr)
    (lane: Set3.Lane)
    (x: Nat)
  :
    (expr.toLane lane).UsesFreeVar x ↔ expr.UsesFreeVar x
  :=
    match expr with
    | .const _ => Iff.rfl
    | .var _ => Iff.rfl
    | .null => Iff.rfl
    | .pair l r =>
      Iff.intro
        (fun h => Or.elim h
          (fun hl => Or.inl ((toLane_UsesFreeVar l lane x).mp hl))
          (fun hr => Or.inr ((toLane_UsesFreeVar r lane x).mp hr)))
        (fun h => Or.elim h
          (fun hl => Or.inl ((toLane_UsesFreeVar l lane x).mpr hl))
          (fun hr => Or.inr ((toLane_UsesFreeVar r lane x).mpr hr)))
    | .ir l r =>
      Iff.intro
        (fun h => Or.elim h
          (fun hl => Or.inl ((toLane_UsesFreeVar l lane x).mp hl))
          (fun hr => Or.inr ((toLane_UsesFreeVar r lane x).mp hr)))
        (fun h => Or.elim h
          (fun hl => Or.inl ((toLane_UsesFreeVar l lane x).mpr hl))
          (fun hr => Or.inr ((toLane_UsesFreeVar r lane x).mpr hr)))
    | .full body =>
      Iff.intro
        (fun h => (toLane_UsesFreeVar body lane x).mp h)
        (fun h => (toLane_UsesFreeVar body lane x).mpr h)
    | .compl body =>
      Iff.intro
        (fun h => (toLane_UsesFreeVar body lane.toggle x).mp h)
        (fun h => (toLane_UsesFreeVar body lane.toggle x).mpr h)
    | .arbIr body =>
      Iff.intro
        (fun h => (toLane_UsesFreeVar body lane (x + 1)).mp h)
        (fun h => (toLane_UsesFreeVar body lane (x + 1)).mpr h)
end BasicExpr

open SingleLaneExpr in
def Expr.IsClean.intp2_eq {fvL fvR b c}
  {expr: SingleLaneExpr}
  (h: Expr.IsClean expr)
:
  expr.intp2 fvL b c = intp2 expr fvR b c
:=
  let nope {P: Nat → Prop}: ∀ x ∈ expr.UsesFreeVar, P x :=
    fun x hx => (h x hx).elim
  let eqL: expr.intp2 fvL b c = intp2 expr.clearFreeVars [] b c :=
    intp2_subst_eq nope nope
  let eqR: expr.intp2 fvR b c = intp2 expr.clearFreeVars [] b c :=
    intp2_subst_eq nope nope
  eqL.trans eqR.symm

def Expr.IsClean.toLane
  {expr: BasicExpr}
  (isClean: Expr.IsClean expr)
  (lane: Set3.Lane)
:
  Expr.IsClean (expr.toLane lane)
:=
  fun x isCleanLane =>
    let iff := expr.toLane_UsesFreeVar lane x
    isClean x (iff.mp isCleanLane)

namespace DefList
  def triIntp2_eq_fv_def
    (dl: DefList)
    (x: Nat)
    (fv0 fv1: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      ((dl.getDef x).toDefLane.intp2 fv0 b c)
      ((dl.getDef x).toDefLane.intp2 fv1 b c)
  :=
    ((dl.isClean x).toLane .defLane).intp2_eq
  
  def triIntp2_eq_fv_pos
    (dl: DefList)
    (x: Nat)
    (fv0 fv1: List Pair)
    (b c: Valuation Pair)
  :
    Eq
      ((dl.getDef x).toPosLane.intp2 fv0 b c)
      ((dl.getDef x).toPosLane.intp2 fv1 b c)
  :=
    ((dl.isClean x).toLane .posLane).intp2_eq
  
  def triIntp2_eq_fv
    (dl: DefList)
    (x: Nat)
    (fv0 fv1: List Pair)
    (b c: Valuation Pair)
  :
    (dl.getDef x).triIntp2 fv0 b c = (dl.getDef x).triIntp2 fv1 b c
  :=
    Set3.eq
      (dl.triIntp2_eq_fv_def x fv0 fv1 b c)
      (dl.triIntp2_eq_fv_pos x fv0 fv1 b c)
  
end DefList

namespace SingleLaneExpr
  def InWfm.of_in_def {dl fv x lane d}
    (inDef: InWfm fv dl ((dl.getDef x).toLane lane) d)
  :
    InWfm [] dl (.const lane x) d
  :=
    of_in_def_no_fv
      (match lane with
      | .defLane =>
        let eqDef := dl.triIntp2_eq_fv_def x [] fv dl.wfm dl.wfm
        show intp2 _ _ _ _ _ from
        eqDef ▸ inDef
      | .posLane =>
        let eqPos := dl.triIntp2_eq_fv_pos x [] fv dl.wfm dl.wfm
        show intp2 _ _ _ _ _ from
        eqPos ▸ inDef)
  
  def InWfm.in_def {dl fv x lane d}
    (inVar: InWfm [] dl (.const lane x) d)
  :
    InWfm fv dl ((dl.getDef x).toLane lane) d
  :=
    show intp2 _ _ _ _ _ from
    match lane with
    | .defLane =>
      dl.triIntp2_eq_fv_def x fv [] dl.wfm dl.wfm ▸
      in_def_no_fv inVar
    | .posLane =>
      dl.triIntp2_eq_fv_pos x fv [] dl.wfm dl.wfm ▸
      in_def_no_fv inVar
  
end SingleLaneExpr
