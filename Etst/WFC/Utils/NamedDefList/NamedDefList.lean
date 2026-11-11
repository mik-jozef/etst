/-
  A user-friendly way to define individual definition lists (see
  Chapter 1) that
  - allows naming individual variables,
  - type errors on unknown variables rather than silently defaulting
    to a fallback value.
  - does not require specifying all variables upfront, allowing them
    to be named where they are used.
-/
module
public import Mathlib.Data.Set.Defs
public import Etst.WFC.Ch1_ExprDefList
public import Etst.WFC.Utils.DefList
import Etst.BasicUtils
import Lean


namespace Etst

public structure NamedExprTools
  (NamedExpr: (vars consts: List String) → Type)
where
  compile {vars consts}
    (expr: NamedExpr vars consts)
  :
    Expr .basic
  
  compiles_clean {consts}
    (expr: NamedExpr [] consts)
  :
    (compile expr).IsClean
  
  compiles_constsLt {consts}
    (expr: NamedExpr [] consts)
  :
    (compile expr).ConstsLt consts.length


public inductive NamedDefListSection {ExprT}
  (tools: NamedExprTools ExprT)
  (baseConsts ownConsts: List String)
:
  -- This is a bookkeeping device to make `ownConsts` inferable.
  (outerConsts innerConsts: List String) →
  Type
| empty:
    NamedDefListSection tools baseConsts ownConsts ownConsts []
| const
    (const: String)
    {outerConsts innerConsts}
    (body: ExprT [] (baseConsts ++ ownConsts))
    (tail:
      NamedDefListSection tools baseConsts ownConsts
        (outerConsts ++ [const])
        innerConsts)
    (nameUnique: const ∉ outerConsts := by decide)
  :
    NamedDefListSection tools baseConsts ownConsts
      outerConsts
      (const :: innerConsts)

namespace NamedDefListSection
  variable {ExprT}
    {tools: NamedExprTools ExprT}
  
  exposed def toDefs {base own o i}
    (segment: NamedDefListSection tools base own o i)
  :
    List (FiniteDefList.Def ((base ++ own).length))
  :=
    match segment with
    | .empty => []
    | .const (innerConsts:=innerRest) cst body tail _ =>
      let head := {
        name := cst
        expr := tools.compile body
        isClean := tools.compiles_clean body
        constsLt := tools.compiles_constsLt body
      }
      head :: tail.toDefs
  
  public theorem toDefs_length {base own o i}
    (segment: NamedDefListSection tools base own o i)
  :
    segment.toDefs.length = i.length
  :=
    match i, segment with
    | [], .empty => rfl
    | _, .const _ _ tail _ =>
      Nat.succ_inj.mpr (toDefs_length tail)
  
end NamedDefListSection

public inductive NamedDefList {ExprT}
  (tools: NamedExprTools ExprT)
:
  (consts: List String) →
  Type
where
| empty: NamedDefList tools []
| extend {baseConsts childConsts}
    (base: NamedDefList tools baseConsts)
    (segment:
      NamedDefListSection tools baseConsts childConsts [] childConsts)
  :
    NamedDefList tools (baseConsts ++ childConsts)

namespace NamedDefList
  variable {ExprT}
    {tools: NamedExprTools ExprT}
  
  exposed def declare {ExprT}
    (tools: NamedExprTools ExprT)
    {innerConsts}
    (segment: NamedDefListSection tools [] innerConsts [] innerConsts)
  :
    NamedDefList tools innerConsts
  :=
    empty.extend segment
  
  
  exposed def dlWithSize {consts: List String}:
    NamedDefList tools consts →
    { f: FiniteDefList // f.size = consts.length }
  | .empty => ⟨FiniteDefList.empty, rfl⟩
  | .extend (baseConsts := bc) (childConsts := cc) base segment =>
    let ⟨dl, dlSizeEq⟩ := dlWithSize base
    let defs := segment.toDefs
    let ubEq: (bc ++ cc).length = dl.size + defs.length := by
      conv => lhs; rw [List.length_append]
      exact
      congr_arg₂ Nat.add dlSizeEq.symm segment.toDefs_length.symm
    let sizeEq := dl.extend_size defs _ ▸ ubEq.symm
    ⟨dl.extend defs ubEq, sizeEq⟩
  
  exposed def dl {consts}
    (ndl: NamedDefList tools consts)
  :
    FiniteDefList
  :=
    dlWithSize ndl
  
  /-
    Extending a `NamedDefList` with a new section does not change
    the well-founded model at the constants defined in the base.
    A port of `FiniteDefList.extend_wfm_eq_of_lt`.
  -/
  public theorem extend_wfm_eq_of_lt {baseConsts childConsts}
    (base: NamedDefList tools baseConsts)
    (segment:
      NamedDefListSection tools baseConsts childConsts [] childConsts)
    {x: Nat}
    (xLt: x < base.dl.size)
  :
    base.dl.wfm x = (base.extend segment).dl.wfm x
  :=
    FiniteDefList.extend_wfm_eq_of_lt
      base.dl
      (by
      conv => lhs; rw [List.length_append];
      exact
      congr_arg₂ Nat.add
        base.dlWithSize.property.symm
        segment.toDefs_length.symm)
      xLt
  
  exposed noncomputable def val {consts}
    (ndl: NamedDefList tools consts)
    (const: String)
    (_: const ∈ consts := by decide)
  :
    Set3 Pair
  :=
    ndl.dl.wfm (consts.idxOf const)
  
  exposed def consts {consts}
    (_ndl: NamedDefList tools consts)
  :
    List String
  :=
    consts
  
  exposed def const {consts}
    (_ndl: NamedDefList tools consts)
    (const: String)
    (_: const ∈ consts := by decide)
  :
    Nat
  :=
    consts.idxOf const
  
  exposed def getDef {consts}
    (ndl: NamedDefList tools consts)
    (x: String)
    (_: x ∈ consts := by decide)
  :
    Expr .basic
  :=
    ndl.dl.getDef (consts.idxOf x)
  
  
  /-
    Structural equality on expressions. Faster than what the
    "deriving DecidableEq" in Ch1 gives.
  -/
  exposed def Expr.eqBool: Expr .basic → Expr .basic → Bool
  | .const t1 x1, .const t2 x2 => decide (t1 = t2) && decide (x1 = x2)
  | .var x1, .var x2 => decide (x1 = x2)
  | .null, .null => true
  | .prod l1 r1, .prod l2 r2 => eqBool l1 l2 && eqBool r1 r2
  | .ir l1 r1, .ir l2 r2 => eqBool l1 l2 && eqBool r1 r2
  | .full body1, .full body2 => eqBool body1 body2
  | .compl body1, .compl body2 => eqBool body1 body2
  | .arbIr body1, .arbIr body2 => eqBool body1 body2
  | _, _ => false
  
  public theorem Expr.eqBool_eq {a b: Expr .basic}
    (h: Expr.eqBool a b = true)
  :
    a = b
  :=
    match a, b with
    | .const _ _, .const _ _ => congr rfl (decide_eq_true_eq.mp h)
    | .var _, .var _ => congr rfl (decide_eq_true_eq.mp h)
    | .null, .null => rfl
    | .prod _ _, .prod _ _ =>
      let ihL := Expr.eqBool_eq (Bool.and_elim_left h)
      let ihR := Expr.eqBool_eq (Bool.and_elim_right h)
      congr (congr rfl ihL) ihR
    | .ir _ _, .ir _ _ =>
      let ihL := Expr.eqBool_eq (Bool.and_elim_left h)
      let ihR := Expr.eqBool_eq (Bool.and_elim_right h)
      congr (congr rfl ihL) ihR
    | .full _, .full _ => congr rfl (Expr.eqBool_eq h)
    | .compl _, .compl _ => congr rfl (Expr.eqBool_eq h)
    | .arbIr _, .arbIr _ => congr rfl (Expr.eqBool_eq h)
  
  /-
    Checks that the first `n` definitions of the two lists are
    syntactically equal (both being `Expr.none` counts as equal).
  -/
  exposed def defsAgreeBool
    (a b: FiniteDefList)
    (n: Nat)
  :
    Bool
  :=
    (List.range n).all fun y => Expr.eqBool (a.getDef y) (b.getDef y)

  /-
    If `a`'s definitions all agree with `b`'s, then the well-founded
    models agree at every index of `a`.
    
    The set of indices of `a` is closed under `UsesConst` (that is
    `FiniteDefList.constsLt`), which is exactly the closure hypothesis
    of `DefList.eq_defs_eq_vals`.
  -/
  public theorem wfm_eq_of_defsAgreeBool
    (a b: FiniteDefList)
    {x: Nat}
    (agrees: defsAgreeBool a b a.size = true)
    (xLt: x < a.size)
  :
    a.wfm x = b.wfm x
  :=
    let names: Set Nat := { y | y < a.size }
    let defsEq: DefListEq.EqDefsOn a.toDefList b.toDefList id names :=
      fun y yIn =>
        (Expr.mapConst_eq_id _).trans
          (Expr.eqBool_eq
            (List.all_eq_true.mp agrees y (List.mem_range.mpr yIn)))
    let closed: DefListEq.ClosedUnderUses a.toDefList names :=
      fun y _ z zUsed => a.constsLt y z zUsed
    DefList.eq_defs_eq_vals defsEq closed x xLt
  
  /-
    If `l` is a prefix of `m`, then an element of `l` has the same
    index in both, so extending a definition list on the right keeps
    the indices of the base's definitions.
  -/
  theorem idxOf_eq_of_isPrefix {l m: List String} {x: String}
    (pfx: l.isPrefixOf m = true)
    (xIn: x ∈ l)
  :
    m.idxOf x = l.idxOf x
  :=
    let isPrefix: l <+: m := List.isPrefixOf_iff_prefix.mp pfx
    isPrefix.findIdx_eq_of_findIdx_lt_length
      (List.idxOf_lt_length_iff.mpr xIn)
  
  /-
    A decidable witness that the definition named `x` is shared by `a`
    and `b`. Two conditions:
    
    - one list's constants are a prefix of the other's, which makes the
      indices of the shared constants agree;
    - the definitions at that prefix agree.
  -/
  public abbrev DefIsShared {aConsts bConsts}
    (a: NamedDefList tools aConsts)
    (b: NamedDefList tools bConsts)
    (x: String)
  :
    Prop
  :=
    (x ∈ a.consts ∧ a.consts.isPrefixOf b.consts = true ∧
      defsAgreeBool a.dl b.dl a.dl.size = true) ∨
    (x ∈ b.consts ∧ b.consts.isPrefixOf a.consts = true ∧
      defsAgreeBool b.dl a.dl b.dl.size = true)
  
  /-
    A definition shared by two definition lists has the same value in
    both. `shareX` is decidable, so the common case (one list extends
    the other) can be discharged with `by decide`.
  -/
  public theorem extend_wfm_eq {aConsts bConsts}
    (a: NamedDefList tools aConsts)
    (b: NamedDefList tools bConsts)
    (x: String)
    (shareX: DefIsShared a b x := by decide)
  :
    a.dl.wfm (aConsts.idxOf x) = b.dl.wfm (bConsts.idxOf x)
  :=
    match shareX with
    | .inl ⟨xIn, pfx, agrees⟩ =>
      let xInA: x ∈ aConsts := xIn
      let idxLt: aConsts.idxOf x < a.dl.size :=
        (dlWithSize a).property.symm ▸ List.idxOf_lt_length_iff.mpr xInA
      (wfm_eq_of_defsAgreeBool a.dl b.dl agrees idxLt).trans
        (congrArg b.dl.wfm (idxOf_eq_of_isPrefix pfx xInA).symm)
    | .inr ⟨xIn, pfx, agrees⟩ =>
      let xInB: x ∈ bConsts := xIn
      let idxLt: bConsts.idxOf x < b.dl.size :=
        (dlWithSize b).property.symm ▸ List.idxOf_lt_length_iff.mpr xInB
      Eq.symm <|
        (wfm_eq_of_defsAgreeBool b.dl a.dl agrees idxLt).trans
          (congrArg a.dl.wfm (idxOf_eq_of_isPrefix pfx xInB)).symm
  
end NamedDefList
