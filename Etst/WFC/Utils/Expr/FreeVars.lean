import Etst.WFC.Ch2_Interpretation
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.InterpretationMono
import Etst.WFC.Utils.Expr.ConstsVarsSat

namespace Etst

variable {E: Type*}


namespace Expr
  def replaceFreeVarsNat
    (fvMap: Nat → Nat)
  :
    Expr E → Expr E
  :=
    replaceFreeVars (var ∘ fvMap)
  
  def instantiateVar
    (expr: Expr E)
    (t: Expr E)
  :
    Expr E
  :=
    expr.replaceFreeVars fun
    | 0 => t
    | n + 1 => var n
  
  def replaceId {E}: Expr E → Expr E := replaceFreeVarsNat id  
  
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
    {depth} (ge: x >= depth)
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
    (depth a b: Nat)
  :
    expr.lift depth (a + b) = (expr.lift depth a).lift depth b
  :=
    match expr with
    | const _ _ => rfl
    | var x => by
      if h: x < depth then
        rw [lift_var_lt x h]
        rw [lift_var_lt x h]
        rw [lift_var_lt x h]
      else
        have ge : x >= depth := not_lt.mp h
        rw [lift_var_ge x ge]
        rw [lift_var_ge x ge]
        rw [lift_var_ge (x + a) (Nat.le_trans ge (Nat.le_add_right _ _))]
        rw [Nat.add_assoc]
    | null => rfl
    | pair l r =>
      congrArg₂
        pair
        (l.lift_add_eq depth a b)
        (r.lift_add_eq depth a b)
    | ir l r =>
      congrArg₂
        ir
        (l.lift_add_eq depth a b)
        (r.lift_add_eq depth a b)
    | full body => congrArg full (body.lift_add_eq depth a b)
    | compl body => congrArg compl (body.lift_add_eq depth a b)
    | arbIr body => congrArg arbIr (body.lift_add_eq depth.succ a b)

  def lift_succ_eq
    (expr: Expr E)
    (depth n: Nat)
  :
    expr.lift depth (n + 1) = (expr.lift depth n).lift depth 1
  :=
    lift_add_eq expr depth n 1
  
  
  def freeVarUb
    (expr: Expr E)
    (depth: Nat := 0)
  :
    Nat
  :=
    match expr with
    | .const _ _ => 0
    | .var x => x + 1 - depth
    | .null => 0
    | .pair left rite =>
        Nat.max (left.freeVarUb depth) (rite.freeVarUb depth)
    | .ir left rite =>
        Nat.max (left.freeVarUb depth) (rite.freeVarUb depth)
    | .full body => body.freeVarUb depth
    | .compl body => body.freeVarUb depth
    | .arbIr body => body.freeVarUb (depth + 1)
  
  def freeVarUb_lift_eq_depth
    (expr: Expr E)
    (liftBy depth liftDepth: Nat)
  :
    Eq
      ((expr.lift liftDepth liftBy).freeVarUb
        (liftBy + depth + liftDepth))
      (expr.freeVarUb (depth + liftDepth))
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => by
        unfold lift freeVarUb
        split_ifs <;> omega
    | .null => rfl
    | .pair l r => by
        unfold lift freeVarUb
        rw [freeVarUb_lift_eq_depth l, freeVarUb_lift_eq_depth r]
    | .ir l r => by
        unfold lift freeVarUb
        rw [freeVarUb_lift_eq_depth l, freeVarUb_lift_eq_depth r]
    | .full body => by
        unfold lift freeVarUb
        rw [freeVarUb_lift_eq_depth body]
    | .compl body => by
        unfold lift freeVarUb
        rw [freeVarUb_lift_eq_depth body]
    | .arbIr body => by
        unfold lift freeVarUb
        rw [Nat.add_assoc (liftBy + depth), Nat.add_assoc depth]
        exact freeVarUb_lift_eq_depth body liftBy depth (liftDepth + 1)

  def freeVarUb_lift_eq
    (expr: Expr E)
    (liftBy depth: Nat)
  :
    Eq
      ((expr.lift 0 liftBy).freeVarUb (liftBy + depth))
      (expr.freeVarUb depth)
  :=
    freeVarUb_lift_eq_depth expr liftBy depth 0
  
  def freeVarUb_freeVarLt {x}
    {expr: Expr E}
    (uses: expr.UsesFreeVar x)
    (depth: Nat)
  :
    x < (expr.freeVarUb depth) + depth
  :=
    match expr with
    | var _ => by unfold freeVarUb; rw [uses]; omega
    | pair left rite =>
      match uses with
      | .inl h =>
        let ih := freeVarUb_freeVarLt h depth
        ih.trans_le (Nat.add_le_add_right (Nat.le_max_left _ _) _)
      | .inr h =>
        let ih := freeVarUb_freeVarLt h depth
        ih.trans_le (Nat.add_le_add_right (Nat.le_max_right _ _) _)
    | ir left rite =>
      match uses with
      | .inl h =>
        let ih := freeVarUb_freeVarLt h depth
        ih.trans_le (Nat.add_le_add_right (Nat.le_max_left _ _) _)
      | .inr h =>
        let ih := freeVarUb_freeVarLt h depth
        ih.trans_le (Nat.add_le_add_right (Nat.le_max_right _ _) _)
    | full body =>
      let uses: body.UsesFreeVar x := uses
      freeVarUb_freeVarLt uses depth
    | compl body =>
      let uses: body.UsesFreeVar x := uses
      freeVarUb_freeVarLt uses depth
    | arbIr body =>
      let uses: body.UsesFreeVar (x+1) := uses
      let ih := freeVarUb_freeVarLt uses (depth + 1)
      Nat.lt_of_add_lt_add_right (Nat.add_assoc _ _ _ ▸ ih)
  
  def freeVarUb_bin_le_elim
    {a b: Expr E} {depth n}
    (le: Nat.max (a.freeVarUb depth) (b.freeVarUb depth) ≤ n)
  :
    a.freeVarUb depth ≤ n ∧ b.freeVarUb depth ≤ n
  :=
    Nat.max_le.mp le
  
  def freeVarUb_bin_le_elimL
    {a b: Expr E} {depth n}
    (le: Nat.max (a.freeVarUb depth) (b.freeVarUb depth) ≤ n)
  :
    a.freeVarUb depth ≤ n
  :=
    (freeVarUb_bin_le_elim le).left
  
  def freeVarUb_bin_le_elimR
    {a b: Expr E} {depth n}
    (le: Nat.max (a.freeVarUb depth) (b.freeVarUb depth) ≤ n)
  :
    b.freeVarUb depth ≤ n
  :=
    (freeVarUb_bin_le_elim le).right
  
  
  def replaceId_eq
    (expr: Expr E)
  :
    expr.replaceId = expr
  :=
    match expr with
    | const _ _ => rfl
    | var _ => rfl
    | null => rfl
    | pair l r =>
      congrArg₂ pair (l.replaceId_eq) (r.replaceId_eq)
    | ir l r =>
      congrArg₂ ir (l.replaceId_eq) (r.replaceId_eq)
    | full body => congrArg full (body.replaceId_eq)
    | compl body => congrArg compl (body.replaceId_eq)
    | arbIr body =>
      let liftEq:
        (liftFvMap fun x => var (E := E) x) = (fun x => var x)
      :=
        funext fun | 0 => rfl | _+1 => rfl
      congrArg arbIr (liftEq.symm ▸ body.replaceId_eq)
  
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
  
  
  def intp2_replaceFreeVars_eq
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
      (intp2 (expr.replaceFreeVars fvMap) fvRite b c)
  :=
    match expr with
    | .const _ _ => rfl
    | .var x => fvEq x rfl
    | .null => rfl
    | .pair _ _ =>
      eq_intp2_pair_of_eq
        (intp2_replaceFreeVars_eq
          (fun x h => fvEq x (Or.inl h))
          (fun x h => fvEqCpl x (Or.inl h)))
        (intp2_replaceFreeVars_eq
          (fun x h => fvEq x (Or.inr h))
          (fun x h => fvEqCpl x (Or.inr h)))
    | .ir _ _ =>
      eq_intp2_ir_of_eq
        (intp2_replaceFreeVars_eq
          (fun x h => fvEq x (Or.inl h))
          (fun x h => fvEqCpl x (Or.inl h)))
        (intp2_replaceFreeVars_eq
          (fun x h => fvEq x (Or.inr h))
          (fun x h => fvEqCpl x (Or.inr h)))
    | .full body =>
      eq_intp2_full_of_eq
        (intp2_replaceFreeVars_eq (expr := body) fvEq fvEqCpl)
    | .compl body =>
      eq_intp2_compl_of_eq
        (intp2_replaceFreeVars_eq (expr := body) fvEqCpl fvEq)
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
        intp2_replaceFreeVars_eq
          (fvEqLifted fvEq d)
          (fvEqLifted fvEqCpl d)
  
  def intp_replaceFreeVars_eq
    {fvMap: Nat → SingleLaneExpr}
    {expr: SingleLaneExpr}
    {fvLeft fvRite v}
    (fvEq:
      ∀ x ∈ expr.UsesFreeVar,
        intpVar fvLeft x = (fvMap x).intp fvRite v)
  :
    Eq
      (expr.intp2 fvLeft v v)
      (intp2 (expr.replaceFreeVars fvMap) fvRite v v)
  :=
    intp2_replaceFreeVars_eq fvEq fvEq
  
  def intp2_replaceFreeVarsNat_eq
    {fvMap: Nat → Nat}
    {expr: SingleLaneExpr}
    {b c: Valuation Pair}
    {fvLeft fvRite}
    (fvEq: ∀ x ∈ expr.UsesFreeVar, fvLeft[x]? = fvRite[fvMap x]?)
  :
    Eq
      (expr.intp2 fvLeft b c)
      (intp2 (expr.replaceFreeVarsNat fvMap) fvRite b c)
  :=
    (fun ab a => ab a a)
      intp2_replaceFreeVars_eq
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
    intp2_replaceFreeVars_eq
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
    expr.intp2 (dB :: fv) v v = intp (expr.instantiateVar t) fv v
  :=
    intp_replaceFreeVars_eq (fun
      | 0, _ => t_eq ▸ rfl
      | _ + 1, _ => rfl)
  
  
  def intp2_clearFreeVars_eq
    (expr: SingleLaneExpr)
    {fv b c}
  :
    expr.intp2 [] b c = intp2 (expr.clearFreeVars) fv b c
  :=
    intp2_replaceFreeVars_eq
      (fun _ _ => intp2_none_eq_empty ▸ rfl)
      (fun _ _ => intp2_none_eq_empty ▸ rfl)
  
  
  def intp2_bv_append
    {expr: SingleLaneExpr}
    {fv b c} (ubLe: expr.freeVarUb ≤ fv.length)
    (rest: List Pair)
  :
    expr.intp2 fv b c = expr.intp2 (fv ++ rest) b c
  :=
    let eq: expr.intp2 fv b c = intp2 expr.replaceId (fv ++ rest) b c :=
      intp2_replaceFreeVarsNat_eq
        (fun x xUsed =>
          let ltUb := expr.freeVarUb_freeVarLt xUsed 0
          let ltFv: x < fv.length := ltUb.trans_le ubLe
          (List.getElem?_append_left ltFv).symm)
    by rw [expr.replaceId_eq] at eq; exact eq
  
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
    intp2_replaceFreeVars_eq nope nope
  let eqR: expr.intp2 fvR b c = intp2 expr.clearFreeVars [] b c :=
    intp2_replaceFreeVars_eq nope nope
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
