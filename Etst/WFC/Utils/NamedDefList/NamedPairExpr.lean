/-
  Named pair expressions: pair expressions (see Chapter 1) written
  with named variables and constants, compiled into `Expr`s by
  `NamedPairExpr.compile`.
  
  Instantiates the generic machinery of `NamedDefList.lean` via
  `NamedExprTools.pair`, and provides the `p3(...)` term syntax as
  well as the `pairDefList` command for defining whole definition
  lists.
-/
module
public import Etst.WFC.Utils.NamedDefList.NamedDefList
import Etst.WFC.Utils.PairExpr
import Lean


namespace Etst

public inductive NamedPairExprRaw (kind: ExprKind):
  (List String) → Type
where
| ident {vars}
    (tag: kind.ConstTag)
    (x: String)
  :
    NamedPairExprRaw kind vars
| null {vars}:
    NamedPairExprRaw kind vars
| prod {vars}
    (left rite: NamedPairExprRaw kind vars)
  :
    NamedPairExprRaw kind vars
| ir {vars}
    (left rite: NamedPairExprRaw kind vars)
  :
    NamedPairExprRaw kind vars
| full {vars}
    (body: NamedPairExprRaw kind vars)
  :
    NamedPairExprRaw kind vars
| compl {vars}
    (body: NamedPairExprRaw kind vars)
  :
    NamedPairExprRaw kind vars
| arbIr {vars}
    (x: String)
    (body: NamedPairExprRaw kind (x :: vars))
  :
    NamedPairExprRaw kind vars
deriving DecidableEq

exposed def NamedPairExprRaw.vars {kind vars}
  (_: NamedPairExprRaw kind vars)
:=
  vars

exposed def NamedPairExprRaw.IsWF {kind vars}
  (expr: NamedPairExprRaw kind vars)
  (consts: List String)
:=
  match expr with
  | ident _ x => x ∈ vars ∨ x ∈ consts
  | null => True
  | prod left rite => left.IsWF consts ∧ rite.IsWF consts
  | ir left rite => left.IsWF consts ∧ rite.IsWF consts
  | full body => body.IsWF consts
  | compl body => body.IsWF consts
  | arbIr _ body => body.IsWF consts

public abbrev NamedPairExpr kind vars consts :=
  { expr: NamedPairExprRaw kind vars // expr.IsWF consts }

namespace NamedPairExprRaw
  variable {kind vars}
  
  exposed def un
    (l r: NamedPairExprRaw kind vars)
  :
    NamedPairExprRaw kind vars
  :=
    .compl (.ir (.compl l) (.compl r))
  
  exposed def some
    (expr: NamedPairExprRaw kind vars)
  :
    NamedPairExprRaw kind vars
  :=
    .compl (.full (.compl expr))
  
  exposed def arbUn
    (x: String)
    (body: NamedPairExprRaw kind (x :: vars))
  :
    NamedPairExprRaw kind vars
  :=
    compl (.arbIr x (.compl body))
  
  exposed def nat: Nat → NamedPairExprRaw kind vars
  | 0 => .null
  | n+1 => .prod (.nat n) .null
  
end NamedPairExprRaw

namespace NamedPairExpr
  variable {kind vars csts}
  
  exposed def consts
    (_: NamedPairExpr kind vars csts)
  :=
    csts
  
  exposed def ident
    (tag: kind.ConstTag)
    (x: String)
    (isIn: x ∈ vars ∨ x ∈ csts := by decide)
  :
    NamedPairExpr kind vars csts
  :=
    ⟨.ident tag x, isIn⟩
  
  exposed def null: NamedPairExpr kind vars csts :=
    ⟨.null, trivial⟩
  
  exposed def prod
    (l r: NamedPairExpr kind vars csts)
  :
    NamedPairExpr kind vars csts
  :=
    ⟨.prod l r, l.property, r.property⟩
  
  exposed def ir
    (l r: NamedPairExpr kind vars csts)
  :
    NamedPairExpr kind vars csts
  :=
    ⟨.ir l r, l.property, r.property⟩
  
  exposed def full
    (body: NamedPairExpr kind vars csts)
  :
    NamedPairExpr kind vars csts
  :=
    ⟨.full body, body.property⟩
  
  exposed def compl
    (body: NamedPairExpr kind vars csts)
  :
    NamedPairExpr kind vars csts
  :=
    ⟨.compl body, body.property⟩
  
  exposed def arbIr
    (x: String)
    (body: NamedPairExpr kind (x :: vars) csts)
  :
    NamedPairExpr kind vars csts
  :=
    ⟨.arbIr x body, body.property⟩
  
  
  exposed def un
    (l r: NamedPairExpr kind vars csts)
  :
    NamedPairExpr kind vars csts
  := ⟨
    .un l r,
    .intro l.property r.property,
  ⟩
  
  exposed def some
    (body: NamedPairExpr kind vars csts)
  :
    NamedPairExpr kind vars csts
  := ⟨
    .some body,
    body.property
  ⟩
  
  exposed def arbUn
    (x: String)
    (body: NamedPairExpr kind (x :: vars) csts)
  :
    NamedPairExpr kind vars csts
  := ⟨
    .arbUn x body,
    body.property
  ⟩
  
  exposed def nat (n: Nat): NamedPairExpr kind vars csts := ⟨
    .nat n,
    let rec go:
      (m: Nat) → (@NamedPairExprRaw.nat kind vars m).IsWF csts
    | 0 => trivial
    | m+1 => .intro (go m) trivial
    go n,  
  ⟩
  
end NamedPairExpr

namespace NamedPairExprRaw
  exposed def check {kind vars consts}
    (expr: NamedPairExprRaw kind vars)
    (isWf: expr.IsWF consts := by decide)
  :
    NamedPairExpr kind vars consts
  :=
    ⟨expr, isWf⟩
  
  public theorem check_id {kind vars consts}
    (expr: NamedPairExprRaw kind vars)
    {isWF: expr.IsWF consts}
  :
    check expr isWF = expr
  :=
    rfl
  
  exposed def compile {kind vars}
    (expr: NamedPairExprRaw kind vars)
    (consts: List String)
  :
    Expr kind
  :=
    match expr with
    | ident tag x =>
      if x ∈ vars then
        .var (vars.idxOf x)
      else
        .const tag (consts.idxOf x)
    | null => .null
    | prod left rite =>
      .prod (left.compile consts) (rite.compile consts)
    | ir left rite =>
      .ir (left.compile consts) (rite.compile consts)
    | full body => .full (body.compile consts)
    | compl body => .compl (body.compile consts)
    | arbIr _ body => .arbIr (body.compile consts)
  
  public theorem compile_sat_lt {kind vars}
    (expr: NamedPairExprRaw kind vars)
    (consts: List String)
  :
    (compile expr consts).FreeVarsSat (· < vars.length)
  :=
    fun x isUsed =>
    match expr with
    | ident _ x =>
      by unfold compile at isUsed; exact
      match Classical.em (x ∈ vars) with
      | Or.inl xIn => by
        rw [ite_eq_left xIn] at isUsed
        exact isUsed ▸ List.idxOf_lt_length_of_mem xIn
      | Or.inr xNin => by
        rw [ite_eq_right xNin] at isUsed
        exact isUsed.elim
    | null => nomatch isUsed
    | prod left rite =>
      isUsed.elim
        (fun isUsedL => compile_sat_lt left consts x isUsedL)
        (fun isUsedR => compile_sat_lt rite consts x isUsedR)
    | ir left rite =>
      isUsed.elim
        (fun isUsedL => compile_sat_lt left consts x isUsedL)
        (fun isUsedR => compile_sat_lt rite consts x isUsedR)
    | full body =>
      compile_sat_lt body consts x isUsed
    | compl body =>
      compile_sat_lt body consts x isUsed
    | arbIr xB body =>
      Nat.lt_of_succ_lt_succ
        (compile_sat_lt body consts (x + 1) isUsed)
  
  public theorem compile_constsLt {kind vars consts}
    (expr: NamedPairExprRaw kind vars)
    (isWf: expr.IsWF consts)
  :
    (compile expr consts).ConstsLt consts.length
  :=
    fun x isUsed =>
    match expr, isWf with
    | ident _ x, isWf =>
      by unfold compile at isUsed; exact
      match Classical.em (x ∈ vars) with
      | Or.inl xIn => by
        rw [ite_eq_left xIn] at isUsed
        exact isUsed.elim
      | Or.inr xNin => by
        rw [ite_eq_right xNin] at isUsed
        let xInConsts: x ∈ consts := isWf.elim xNin.elim id
        exact isUsed ▸ List.idxOf_lt_length_of_mem xInConsts
    | null, _ => nomatch isUsed
    | prod left rite, ⟨isWfL, isWfR⟩ =>
      isUsed.elim
        (fun isUsedL => compile_constsLt left isWfL x isUsedL)
        (fun isUsedR => compile_constsLt rite isWfR x isUsedR)
    | ir left rite, ⟨isWfL, isWfR⟩ =>
      isUsed.elim
        (fun isUsedL => compile_constsLt left isWfL x isUsedL)
        (fun isUsedR => compile_constsLt rite isWfR x isUsedR)
    | full body, isWf =>
      compile_constsLt body isWf x isUsed
    | compl body, isWf =>
      compile_constsLt body isWf x isUsed
    | arbIr xB body, isWf =>
      compile_constsLt body isWf x isUsed
  
end NamedPairExprRaw

public abbrev NamedExprTools.pair:
  NamedExprTools (NamedPairExpr .basic)
:= {
  compile :=
    fun {vars consts} expr =>
      NamedPairExprRaw.compile expr.val consts
  compiles_clean expr :=
    let satLt := expr.val.compile_sat_lt expr.consts
    let eq: (· < 0) = fun _ => False :=
      funext fun _ => propext (Iff.intro nofun nofun)
    by unfold Expr.IsClean; exact eq ▸ satLt
  compiles_constsLt expr := expr.val.compile_constsLt expr.property
}

public instance NamedPairExprRaw.isWF {kind vars}:
  (e: NamedPairExprRaw kind vars) →
  (consts: List String) →
  Decidable (e.IsWF consts)
| .ident _ x, consts =>
  inferInstanceAs (Decidable (x ∈ vars ∨ x ∈ consts))
| .null, _ => inferInstanceAs (Decidable True)
| .prod l r, consts =>
  match isWF l consts, isWF r consts with
  | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
  | isFalse hl, _ => isFalse fun ⟨h, _⟩ => hl h
  | _, isFalse hr => isFalse fun ⟨_, h⟩ => hr h
| .ir l r, consts =>
  match isWF l consts, isWF r consts with
  | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
  | isFalse hl, _ => isFalse fun ⟨h, _⟩ => hl h
  | _, isFalse hr => isFalse fun ⟨_, h⟩ => hr h
| .full b, consts => isWF b consts
| .compl b, consts => isWF b consts
| .arbIr _ b, consts => isWF b consts

exposed def Pair.toNamedExpr {kind vars consts}:
  Pair → NamedPairExpr kind vars consts
| .null => .null
| .pair l r => .prod l.toNamedExpr r.toNamedExpr

public theorem Pair.toExpr_eq_named
  (p: Pair)
  {kind: ExprKind}
  (vars consts: List String)
:
  let T := NamedPairExpr kind vars consts
  p.toExpr = ((p.toNamedExpr: T)).val.compile consts
:=
  match p with
  | .null => rfl
  | .pair l r =>
    congrArg₂
      Expr.prod
      (l.toExpr_eq_named vars consts)
      (r.toExpr_eq_named vars consts)

namespace Expr
  public theorem inToNamedExpr {kind lane b c fv consts vars}
    (p: Pair)
  :
    let T := NamedPairExpr kind vars consts
    p ∈ ((p.toNamedExpr: T).val.compile consts).intp lane b c fv
  :=
    p.toExpr_eq_named vars consts ▸
    inToExpr p
  
  public theorem inToNamedExprElim {kind lane b c fv consts vars}
    {p pIn: Pair}
    (inExpr:
      let T := NamedPairExpr kind vars consts
      pIn ∈ ((p.toNamedExpr: T).val.compile consts).intp lane b c fv)
  :
    p = pIn
  := by
    rw [←p.toExpr_eq_named vars consts] at inExpr
    exact inToExprElim inExpr
  
  public theorem intp_toNamedExpr_eq_singleton
    {kind lane b c fv consts vars}
    (p: Pair)
  :
    let T := NamedPairExpr kind vars consts
    intp ((p.toNamedExpr: T).val.compile consts) lane b c fv = {p}
  :=
    p.toExpr_eq_named vars consts ▸
    intp_toExpr_eq_singleton p
  
end Expr


declare_syntax_cat p3_expr

-- Expressions
syntax:90 ident : p3_expr
syntax:90 "."ident : p3_expr
syntax:90 ":"ident : p3_expr
syntax:90 num : p3_expr
syntax:90 "(?some " p3_expr ")" : p3_expr
syntax:90 "(?full " p3_expr ")" : p3_expr
syntax:90 "(" p3_expr ")" : p3_expr
syntax:90 "null" : p3_expr
syntax:90 "<[" term "]>" : p3_expr
syntax:80 p3_expr:80 p3_expr:81 : p3_expr
syntax:70 p3_expr:71 " × " p3_expr:70 : p3_expr
syntax:70 " × " p3_expr:71 " × " p3_expr:70 : p3_expr
syntax:60 "!" p3_expr:60 : p3_expr
syntax:50 p3_expr:51 "|" p3_expr:50 : p3_expr
syntax:50 "|" p3_expr:51 "|" p3_expr:50 : p3_expr
syntax:40 p3_expr:41 "&" p3_expr:40 : p3_expr
syntax:40 "&" p3_expr:41 "&" p3_expr:40 : p3_expr
syntax:30 p3_expr:30 "then" p3_expr:31 : p3_expr
syntax:20 p3_expr:21 "->" p3_expr:20 : p3_expr
syntax:10 p3_expr:20 "<->" p3_expr:20 : p3_expr
syntax:00 "Ex " ident+ ", " p3_expr : p3_expr
syntax:00 "Ex " ident ": " p3_expr ", " p3_expr : p3_expr
syntax:00 "All " ident+ ", " p3_expr : p3_expr
syntax:00 "All " ident ": " p3_expr ", " p3_expr : p3_expr

syntax "p3_inner(" p3_expr ")" : term
syntax "p3(" p3_expr ")" : term
syntax "p3(" ident,* ";" p3_expr ")" : term

open Lean in
macro_rules
-- Public entry points: ascribe exactly once, then hand off to the inner rules
| `(p3( $e:p3_expr )) =>
  `((p3_inner($e) : NamedPairExprRaw _ []))
| `(p3( $ids:ident,* ; $e:p3_expr )) => do
  let namesRev : Array (TSyntax `term) :=
    ids.getElems.map fun i => quote i.getId.toString
  `((p3_inner($e) : NamedPairExprRaw _ [$namesRev.reverse,*]))

open Lean in
macro_rules
-- Parentheses removal
| `(p3_inner( ($expr) )) => `(p3_inner($expr))
-- Function application
| `(p3_inner( $fn $arg )) =>
  `(p3_inner( Ex res, $fn & ($arg × res) then res ))
-- Remove leading "|"
| `(p3_inner( | $a | $b )) => `(p3_inner( $a | $b ))
-- Remove leading "&"
| `(p3_inner( & $a & $b )) => `(p3_inner( $a & $b ))
-- Remove leading "×"
| `(p3_inner( × $a × $b )) => `(p3_inner( $a × $b ))
-- Then to some
| `(p3_inner( $a then $b )) => `(p3_inner( (?some $a) & $b ))
-- Implication (->) to disjunction
| `(p3_inner( $a -> $b )) => `(p3_inner( !$a | $b ))
-- Equivalence (<->) to conjunction of implications
| `(p3_inner( $a <-> $b )) => `(p3_inner( ($a -> $b) & ($b -> $a) ))
-- Multi-variable existential quantifier
| `(p3_inner( Ex $x:ident $y:ident $xs:ident*, $body )) =>
  `(p3_inner( Ex $x, Ex $y $xs*, $body ))
-- Bounded existential quantifier
| `(p3_inner( Ex $x:ident: $domain, $body )) =>
  `(p3_inner( Ex $x, $x:ident & $domain then $body ))
-- Multi-variable universal quantifier
| `(p3_inner( All $x:ident $y:ident $xs:ident*, $body )) =>
  `(p3_inner( All $x, All $y $xs*, $body ))
-- Bounded universal quantifier
| `(p3_inner( All $x:ident: $domain, $body )) =>
  `(p3_inner( All $x, (?some ($x:ident & !$domain)) | $body ))
-- Identifiers
| `(p3_inner( $x:ident )) =>
  `(.ident (kind := .basic) () $(quote x.getId.toString))
| `(p3_inner( . $x:ident )) =>
  `(.ident (kind := .lane) Set3.Lane.posLane $(quote x.getId.toString))
| `(p3_inner( : $x:ident )) =>
  `(.ident (kind := .lane) Set3.Lane.defLane $(quote x.getId.toString))
-- Numbers
| `(p3_inner( $n:num )) => `(.nat $n)
-- Null
| `(p3_inner( null )) => `(.null)
-- Escape hatch
| `(p3_inner( <[$t]> )) => pure t
-- Kernel constructors
| `(p3_inner( $a × $b )) => `(.prod p3_inner($a) p3_inner($b))
| `(p3_inner( $a & $b )) => `(.ir p3_inner($a) p3_inner($b))
| `(p3_inner( $a | $b )) => `(.un p3_inner($a) p3_inner($b))
| `(p3_inner( (?some $a) )) => `(.some p3_inner($a))
| `(p3_inner( (?full $a) )) => `(.full p3_inner($a))
| `(p3_inner( ! $a )) => `(.compl p3_inner($a))
| `(p3_inner( Ex $x:ident, $body )) =>
  `(.arbUn $(quote x.getId.toString) p3_inner($body))
| `(p3_inner( All $x:ident, $body )) =>
  `(.arbIr $(quote x.getId.toString) p3_inner($body))


declare_syntax_cat p3_defList
syntax "p3 " ident " := " p3_expr : p3_defList

open Lean in
meta def expandPairDefEntries
  (ents: Array (TSyntax `p3_defList))
  (init: Term)
:
  MacroM Term
:= do
  let mut body := init
  for ent in ents.reverse do
    match ent with
    | `(p3_defList| p3 $x:ident := $e) =>
      body ←
        `(NamedDefListSection.const
            $(quote x.getId.toString) p3_inner($e) $body)
    | _ => Macro.throwUnsupported
  return body

-- pairDefList name ... pairDefList.
syntax declModifiers "pairDefList " ident
  p3_defList* "pairDefList." : command

-- pairDefList name extends base ... pairDefList.
syntax declModifiers "pairDefList " ident " extends " ident
  p3_defList* "pairDefList." : command

macro_rules
| `($mods:declModifiers pairDefList $name:ident
      $ents:p3_defList* pairDefList.) => do
  let body ← expandPairDefEntries ents (← `(NamedDefListSection.empty))
  `($mods:declModifiers def $name :=
      NamedDefList.declare NamedExprTools.pair $body)
| `($mods:declModifiers pairDefList $name:ident extends $base:ident
      $ents:p3_defList* pairDefList.) => do
  let body ← expandPairDefEntries ents (← `(NamedDefListSection.empty))
  `($mods:declModifiers def $name :=
      NamedDefList.extend $base $body)


namespace Examples
  def exampleEmptyList :=
    NamedDefList.declare .pair
    .empty
  
  def example0 :=
    NamedDefList.declare .pair <|
    .const "A" (.prod (.ident () "X") (.ident () "A")) <|
    .const "B" (.prod (.ident () "X") (.ident () "A")) <|
    .const "C" (.prod (.ident () "X") (.ident () "A")) <|
    .const "X" (.prod (.ident () "X") (.ident () "A")) <|
    .const "Y" (.prod (.ident () "X") (.ident () "A")) <|
    .empty
  
  def example1 :=
    example0.extend <|
    .const "Bd" .null <|
    .empty
  
  
  def testStx0 := p3((x) -> A)
  def testStx1 := p3(Ex x y, x × y | A)
  def testStx2 := p3(All x: X, x then x)
  def testStx3 := p3(A <-> !B)
  def testStx4 := p3(f (3 × B))
  def testStx5 :=
    p3(<[NamedPairExprRaw.null (kind := .basic) (vars := [])]>)
  
  public pairDefList exampleStx0
    p3 X := X × A
    p3 A := X × 3
    p3 B := <[testStx3.check]>
  pairDefList.

  @[expose] public pairDefList exampleStx1 extends exampleStx0
    p3 C := A
  pairDefList.
  
end Examples
