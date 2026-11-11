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
  
end NamedDefList
