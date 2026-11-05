/-
  A user-friendly way to define individual definition lists (see
  Chapter 1) that
  - allows naming individual variables,
  - type errors on unknown variables rather than silently defaulting
    to a fallback value.
  - does not require specifying all variables upfront, allowing them
    to be named where they are used.
  
  TODO delete `FiniteDefList.lean` and replace its usages with this.
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
    BasicExpr
  
  compiles_clean {consts}
    (expr: NamedExpr [] consts)
  :
    (compile expr).IsClean
  
  compiles_constsLt {consts}
    (expr: NamedExpr [] consts)
  :
    (compile expr).ConstsLt consts.length


public inductive NamedDefListSection {Expr}
  (tools: NamedExprTools Expr)
:
  (outerConsts innerConsts: List String) →
  Type
| empty {outerConsts}: NamedDefListSection tools outerConsts []
| const
    (const: String)
    {outerConsts innerConsts}
    (body: Expr [] (outerConsts ++ (const :: innerConsts)))
    (tail:
      NamedDefListSection tools (outerConsts.concat const) innerConsts)
    (nameUnique: const ∉ outerConsts := by decide)
  :
    NamedDefListSection tools outerConsts (const :: innerConsts)

namespace NamedDefListSection
  variable {Expr}
    {tools: NamedExprTools Expr}
  
  exposed def length {o i}
    (segment: NamedDefListSection tools o i)
  :
    Nat
  :=
    match segment with
    | .empty => 0
    | .const _ _ tail _ => tail.length + 1
  
  public theorem toDefs_ub_rec {cst ub}
    {o i: List String}
    (ubEq: ub = o.length + (cst :: i).length)
  :
    ub = (o.concat cst).length + i.length
  := by
    apply ubEq.trans
    simp only [List.length_cons, List.length_concat]
    omega
  
  exposed def toDefs {o i}
    (segment: NamedDefListSection tools o i)
    (ub: Nat)
    (ubEq: ub = o.length + i.length)
  :
    List (FiniteDefList.Def ub)
  :=
    match segment with
    | .empty => []
    | .const (innerConsts:=innerRest) cst body tail _ =>
      let head := {
        name := cst
        expr := tools.compile body
        isClean := tools.compiles_clean body
        constsLt :=
          let lenEq: ub = (o ++ cst :: innerRest).length := by
            rw [ubEq, List.length_append]
          lenEq ▸
          tools.compiles_constsLt body
      }
      head :: tail.toDefs ub (toDefs_ub_rec ubEq)
  
  public theorem toDefs_length_inner {o i}
    (segment: NamedDefListSection tools o i)
    (ub: Nat)
    (ubEq: ub = o.length + i.length)
  :
    (segment.toDefs ub ubEq).length = i.length
  :=
    match i, segment with
    | [], .empty => rfl
    | _, .const _ _ tail _ =>
      Nat.succ_inj.mpr
        (toDefs_length_inner tail _ (toDefs_ub_rec ubEq))
  
end NamedDefListSection

public inductive NamedDefList {Expr}
  (tools: NamedExprTools Expr)
:
  (outerConsts innerConsts: List String) →
  Type
where
| empty {outerConsts}: NamedDefList tools outerConsts []
| extend {baseConsts childConsts}
    (base: NamedDefList tools [] baseConsts)
    (segment:
      NamedDefListSection tools baseConsts childConsts)
  :
    NamedDefList tools [] (baseConsts ++ childConsts)

namespace NamedDefList
  variable {Expr}
    {tools: NamedExprTools Expr}
  
  exposed def declare {Expr}
    (tools: NamedExprTools Expr)
    {innerConsts}
    (segment: NamedDefListSection tools [] innerConsts)
  :
    NamedDefList tools [] innerConsts
  :=
    empty.extend segment
  
  
  exposed def dlWithSizeExtend {baseConsts childConsts: List String}
      (base: { f: FiniteDefList // f.size = baseConsts.length })
      (segment: NamedDefListSection tools baseConsts childConsts)
    :
      { f: FiniteDefList // f.size = (baseConsts ++ childConsts).length }
  :=
    let defs := segment.toDefs _ rfl
    let lengthEq:
      Eq
        (base.val.size + defs.length)
        (baseConsts.length + childConsts.length)
    :=
      congr
        (congr rfl base.property)
        (segment.toDefs_length_inner _ rfl)
    let dl := base.val.extend defs lengthEq.symm
    let extendEq := base.val.extend_size defs lengthEq.symm
    ⟨dl, extendEq ▸ List.length_append.symm ▸ lengthEq⟩
  
  exposed def dlWithSize {outerConsts innerConsts: List String}:
    NamedDefList tools outerConsts innerConsts →
    { f: FiniteDefList // f.size = innerConsts.length }
  | .empty => ⟨FiniteDefList.empty, rfl⟩
  | .extend base segment => dlWithSizeExtend base.dlWithSize segment
  
  exposed def dl {innerConsts}
    (dl: NamedDefList tools [] innerConsts)
  :
    FiniteDefList
  :=
    dlWithSize dl
  
  theorem extend_dl_eq {baseConsts childConsts}
    (base: NamedDefList tools [] baseConsts)
    (segment: NamedDefListSection tools baseConsts childConsts)
  :
    Eq
      (base.extend segment).dl
      (dlWithSizeExtend base.dlWithSize segment).val
  := by
    show (dlWithSize (base.extend segment)).val = _
    rw [dlWithSize]
  
  /-
    Extending a `NamedDefList` with a new section does not change
    the well-founded model at the constants defined in the base.
    A port of `FiniteDefList.extend_wfm_eq_of_lt`.
  -/
  public theorem extend_wfm_eq_of_lt {baseConsts childConsts}
    (base: NamedDefList tools [] baseConsts)
    (segment: NamedDefListSection tools baseConsts childConsts)
    {x: Nat}
    (xLt: x < base.dl.size)
  :
    base.dl.wfm x = (base.extend segment).dl.wfm x
  :=
    extend_dl_eq base segment ▸
    FiniteDefList.extend_wfm_eq_of_lt
      base.dl
      (congr
        (congr rfl base.dlWithSize.property)
        (segment.toDefs_length_inner _ rfl)).symm
      xLt
  
  exposed noncomputable def val {consts}
    (ndl: NamedDefList tools [] consts)
    (const: String)
    (_: const ∈ consts := by decide)
  :
    Set3 Pair
  :=
    ndl.dl.wfm (consts.idxOf const)
  
  exposed def consts {consts}
    (_ndl: NamedDefList tools [] consts)
  :
    List String
  :=
    consts
  
  exposed def const {consts}
    (_ndl: NamedDefList tools [] consts)
    (const: String)
    (_: const ∈ consts := by decide)
  :
    Nat
  :=
    consts.idxOf const
  
  exposed def getDef {consts}
    (ndl: NamedDefList tools [] consts)
    (x: String)
    (_: x ∈ consts := by decide)
  :
    BasicExpr
  :=
    ndl.dl.getDef (consts.idxOf x)
  
end NamedDefList
