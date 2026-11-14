/-
  Named pair expressions: pair expressions (see Chapter 1) written
  with named variables and constants, compiled into `Expr`s by
  `WfNamedPairExpr.compile`.
  
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

public inductive NamedPairExpr (kind: ExprKind):
  (List String) → Type
where
-- TODO refactor, ident should only have a tag if it is a constant
| ident {vars}
    (tag: kind.ConstTag)
    (x: String)
  :
    NamedPairExpr kind vars
| null {vars}:
    NamedPairExpr kind vars
| prod {vars}
    (left rite: NamedPairExpr kind vars)
  :
    NamedPairExpr kind vars
| ir {vars}
    (left rite: NamedPairExpr kind vars)
  :
    NamedPairExpr kind vars
| full {vars}
    (body: NamedPairExpr kind vars)
  :
    NamedPairExpr kind vars
| compl {vars}
    (body: NamedPairExpr kind vars)
  :
    NamedPairExpr kind vars
| arbIr {vars}
    (x: String)
    (body: NamedPairExpr kind (x :: vars))
  :
    NamedPairExpr kind vars
| raw {vars}
    (body: Expr kind)
  :
    NamedPairExpr kind vars
deriving DecidableEq

exposed def NamedPairExpr.vars {kind vars}
  (_: NamedPairExpr kind vars)
:=
  vars

-- Whether all consts used in the expression are in a given list.
exposed def NamedPairExpr.IsWF {kind vars}
  (expr: NamedPairExpr kind vars)
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
  | raw body =>
      And
        (∀ x, body.UsesConst x → x < consts.length)
        (∀ x, body.UsesFreeVar x → x < vars.length)

public abbrev WfNamedPairExpr kind vars consts :=
  { expr: NamedPairExpr kind vars // expr.IsWF consts }

namespace NamedPairExpr
  variable {kind vars}
  
  exposed def un
    (l r: NamedPairExpr kind vars)
  :
    NamedPairExpr kind vars
  :=
    .compl (.ir (.compl l) (.compl r))
  
  exposed def some
    (expr: NamedPairExpr kind vars)
  :
    NamedPairExpr kind vars
  :=
    .compl (.full (.compl expr))
  
  exposed def arbUn
    (x: String)
    (body: NamedPairExpr kind (x :: vars))
  :
    NamedPairExpr kind vars
  :=
    compl (.arbIr x (.compl body))
  
  exposed def nat: Nat → NamedPairExpr kind vars
  | 0 => .null
  | n+1 => .prod (.nat n) .null
  
end NamedPairExpr

namespace WfNamedPairExpr
  variable {kind vars csts}
  
  exposed def consts
    (_: WfNamedPairExpr kind vars csts)
  :=
    csts
  
  exposed def ident
    (tag: kind.ConstTag)
    (x: String)
    (isIn: x ∈ vars ∨ x ∈ csts := by decide)
  :
    WfNamedPairExpr kind vars csts
  :=
    ⟨.ident tag x, isIn⟩
  
  exposed def null: WfNamedPairExpr kind vars csts :=
    ⟨.null, trivial⟩
  
  exposed def prod
    (l r: WfNamedPairExpr kind vars csts)
  :
    WfNamedPairExpr kind vars csts
  :=
    ⟨.prod l r, l.property, r.property⟩
  
  exposed def ir
    (l r: WfNamedPairExpr kind vars csts)
  :
    WfNamedPairExpr kind vars csts
  :=
    ⟨.ir l r, l.property, r.property⟩
  
  exposed def full
    (body: WfNamedPairExpr kind vars csts)
  :
    WfNamedPairExpr kind vars csts
  :=
    ⟨.full body, body.property⟩
  
  exposed def compl
    (body: WfNamedPairExpr kind vars csts)
  :
    WfNamedPairExpr kind vars csts
  :=
    ⟨.compl body, body.property⟩
  
  exposed def arbIr
    (x: String)
    (body: WfNamedPairExpr kind (x :: vars) csts)
  :
    WfNamedPairExpr kind vars csts
  :=
    ⟨.arbIr x body, body.property⟩
  
  
  exposed def un
    (l r: WfNamedPairExpr kind vars csts)
  :
    WfNamedPairExpr kind vars csts
  := ⟨
    .un l r,
    .intro l.property r.property,
  ⟩
  
  exposed def some
    (body: WfNamedPairExpr kind vars csts)
  :
    WfNamedPairExpr kind vars csts
  := ⟨
    .some body,
    body.property
  ⟩
  
  exposed def arbUn
    (x: String)
    (body: WfNamedPairExpr kind (x :: vars) csts)
  :
    WfNamedPairExpr kind vars csts
  := ⟨
    .arbUn x body,
    body.property
  ⟩
  
  exposed def nat (n: Nat): WfNamedPairExpr kind vars csts := ⟨
    .nat n,
    let rec go:
      (m: Nat) → (@NamedPairExpr.nat kind vars m).IsWF csts
    | 0 => trivial
    | m+1 => .intro (go m) trivial
    go n,  
  ⟩
  
end WfNamedPairExpr

namespace NamedPairExpr
  exposed def check {kind vars consts}
    (expr: NamedPairExpr kind vars)
    (isWf: expr.IsWF consts := by decide)
  :
    WfNamedPairExpr kind vars consts
  :=
    ⟨expr, isWf⟩
  
  public theorem check_id {kind vars consts}
    (expr: NamedPairExpr kind vars)
    {isWF: expr.IsWF consts}
  :
    check expr isWF = expr
  :=
    rfl
  
  exposed def compile {kind vars}
    (expr: NamedPairExpr kind vars)
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
    | raw body => body
  
  public theorem IsWF.compile_sat_lt {kind vars consts}
    {expr: NamedPairExpr kind vars}
    (isWf: expr.IsWF consts)
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
        (fun isUsedL => compile_sat_lt isWf.left x isUsedL)
        (fun isUsedR => compile_sat_lt isWf.right x isUsedR)
    | ir left rite =>
      isUsed.elim
        (fun isUsedL => compile_sat_lt isWf.left x isUsedL)
        (fun isUsedR => compile_sat_lt isWf.right x isUsedR)
    | full body =>
      compile_sat_lt (expr := body) isWf x isUsed
    | compl body =>
      compile_sat_lt (expr := body) isWf x isUsed
    | arbIr xB body =>
      Nat.lt_of_succ_lt_succ
        (compile_sat_lt (expr := body) isWf (x + 1) isUsed)
    | raw body => isWf.right x isUsed
  
  public theorem compile_constsLt {kind vars consts}
    {expr: NamedPairExpr kind vars}
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
        (fun isUsedL => compile_constsLt isWfL x isUsedL)
        (fun isUsedR => compile_constsLt isWfR x isUsedR)
    | ir left rite, ⟨isWfL, isWfR⟩ =>
      isUsed.elim
        (fun isUsedL => compile_constsLt isWfL x isUsedL)
        (fun isUsedR => compile_constsLt isWfR x isUsedR)
    | full body, isWf =>
      compile_constsLt (expr := body) isWf x isUsed
    | compl body, isWf =>
      compile_constsLt (expr := body) isWf x isUsed
    | arbIr xB body, isWf =>
      compile_constsLt (expr := body) isWf x isUsed
    | raw body, isWf =>
      isWf.left x isUsed
  
end NamedPairExpr

public abbrev NamedExprTools.pair:
  NamedExprTools (WfNamedPairExpr .basic)
:= {
  compile :=
    fun {vars consts} expr =>
      NamedPairExpr.compile expr.val consts
  compiles_clean expr :=
    let satLt := expr.property.compile_sat_lt
    let eq: (· < 0) = fun _ => False :=
      funext fun _ => propext (Iff.intro nofun nofun)
    by unfold Expr.IsClean; exact eq ▸ satLt
  compiles_constsLt expr := expr.val.compile_constsLt expr.property
}

public instance NamedPairExpr.isWf {kind vars}:
  (e: NamedPairExpr kind vars) →
  (consts: List String) →
  Decidable (e.IsWF consts)
| .ident _ x, consts =>
  inferInstanceAs (Decidable (x ∈ vars ∨ x ∈ consts))
| .null, _ => inferInstanceAs (Decidable True)
| .prod l r, consts =>
  match isWf l consts, isWf r consts with
  | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
  | isFalse hl, _ => isFalse fun ⟨h, _⟩ => hl h
  | _, isFalse hr => isFalse fun ⟨_, h⟩ => hr h
| .ir l r, consts =>
  match isWf l consts, isWf r consts with
  | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
  | isFalse hl, _ => isFalse fun ⟨h, _⟩ => hl h
  | _, isFalse hr => isFalse fun ⟨_, h⟩ => hr h
| .full b, consts => isWf b consts
| .compl b, consts => isWf b consts
| .arbIr _ b, consts => isWf b consts
| .raw b, consts =>
  inferInstanceAs
    (Decidable
      (And
        (b.ConstsLt consts.length)
        (b.FreeVarsSat (· < vars.length))))

exposed def Pair.toNamedExpr {kind vars consts}:
  Pair → WfNamedPairExpr kind vars consts
| .null => .null
| .pair l r => .prod l.toNamedExpr r.toNamedExpr

public theorem Pair.toExpr_eq_named
  (p: Pair)
  {kind: ExprKind}
  (vars consts: List String)
:
  let T := WfNamedPairExpr kind vars consts
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
    let T := WfNamedPairExpr kind vars consts
    p ∈ ((p.toNamedExpr: T).val.compile consts).intp lane b c fv
  :=
    p.toExpr_eq_named vars consts ▸
    inToExpr p
  
  public theorem inToNamedExprElim {kind lane b c fv consts vars}
    {p pIn: Pair}
    (inExpr:
      let T := WfNamedPairExpr kind vars consts
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
    let T := WfNamedPairExpr kind vars consts
    intp ((p.toNamedExpr: T).val.compile consts) lane b c fv = {p}
  :=
    p.toExpr_eq_named vars consts ▸
    intp_toExpr_eq_singleton p
  
end Expr


declare_syntax_cat p3_expr

/-
  Smart quantifier precedence. A quantifier is greedy but only for
  lines that are indented at least as much as the quantifier's first token.
-/
namespace P3Parser
  open Lean Parser
  
  public meta def colGe: Parser :=
    checkColGe "p3 expression is less indented than the enclosing quantifier"
  
  /-- A `p3_expr` that ignores any enclosing indentation context. -/
  public meta def expr: Parser :=
    withoutPosition (categoryParser `p3_expr 0)
  
  /-- A quantifier body: a `p3_expr` bounded by its own indentation. -/
  public meta def body: Parser :=
    withPosition (categoryParser `p3_expr 0)
end P3Parser

-- Expressions
syntax:90 P3Parser.colGe ident : p3_expr
syntax:90 P3Parser.colGe "."ident : p3_expr
syntax:90 P3Parser.colGe ":"ident : p3_expr
syntax:90 P3Parser.colGe num : p3_expr
syntax:90 "(?some " P3Parser.expr ")" : p3_expr
syntax:90 "(?full " P3Parser.expr ")" : p3_expr
syntax:90 "(" P3Parser.expr ")" : p3_expr
syntax:90 P3Parser.colGe "null" : p3_expr
syntax:90 P3Parser.colGe "<[" term "]>" : p3_expr
syntax:80 p3_expr:80 P3Parser.colGe p3_expr:81 : p3_expr
syntax:70 p3_expr:71 P3Parser.colGe " × " p3_expr:70 : p3_expr
syntax:70 " × " p3_expr:71 P3Parser.colGe " × " p3_expr:70 : p3_expr
syntax:60 P3Parser.colGe "!" p3_expr:60 : p3_expr
syntax:50 p3_expr:51 P3Parser.colGe "|" p3_expr:50 : p3_expr
syntax:50 "|" p3_expr:51 P3Parser.colGe "|" p3_expr:50 : p3_expr
syntax:40 p3_expr:41 P3Parser.colGe "&" p3_expr:40 : p3_expr
syntax:40 "&" p3_expr:41 P3Parser.colGe "&" p3_expr:40 : p3_expr
syntax:30 p3_expr:30 P3Parser.colGe "then" p3_expr:31 : p3_expr
syntax:20 p3_expr:21 P3Parser.colGe "->" p3_expr:20 : p3_expr
syntax:10 p3_expr:20 P3Parser.colGe "<->" p3_expr:20 : p3_expr
syntax:90 "Ex " ident+ ", " P3Parser.body : p3_expr
syntax:90 "Ex " ident ": " p3_expr ", " P3Parser.body : p3_expr
syntax:90 "All " ident+ ", " P3Parser.body : p3_expr
syntax:90 "All " ident ": " p3_expr ", " P3Parser.body : p3_expr

syntax "p3_inner(" P3Parser.expr ")" : term
syntax "p3(" P3Parser.expr ")" : term
syntax "p3(" ident,* ";" P3Parser.expr ")" : term

open Lean in
macro_rules
-- Public entry points: ascribe once, then hand off to the inner rules
| `(p3( $e:p3_expr )) =>
  `((p3_inner($e) : NamedPairExpr _ []))
| `(p3( $ids:ident,* ; $e:p3_expr )) => do
  let namesRev : Array (TSyntax `term) :=
    ids.getElems.map fun i => quote i.getId.toString
  `((p3_inner($e) : NamedPairExpr _ [$namesRev.reverse,*]))

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
  `(.ident .basic $(quote x.getId.toString))
| `(p3_inner( . $x:ident )) =>
  `(.ident .posLane $(quote x.getId.toString))
| `(p3_inner( : $x:ident )) =>
  `(.ident .defLane $(quote x.getId.toString))
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
syntax "p3 " ident " := " P3Parser.expr : p3_defList

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
    p3(<[NamedPairExpr.null (kind := .basic) (vars := [])]>)
  
  -- Smart quantifier precedence: a quantifier may occur as an operand, and
  -- its body ends at the first line indented less than its body's start.
  example:
    p3(
      & Ex i, foo × bar
      & All a,
        All b,
        | insideAll
        | butOutsideEx
    ) =
    .ir
      (.arbUn "i" (.prod (.ident () "foo") (.ident () "bar")))
      (.arbIr "a"
        (.arbIr "b"
          (.un (.ident () "insideAll") (.ident () "butOutsideEx"))))
  := rfl
  
  example:
    p3(
      | Ex i, foo
      | bar
    ) =
    .un (.arbUn "i" (.ident () "foo")) (.ident () "bar")
  := rfl

  -- A body on its own line extends across equally indented lines, and a
  -- dedented sibling ends it (even out of several nested quantifiers).
  example:
    p3(
      Ex i,
        Ex j,
          foo
      & bar
    ) =
    .ir (.arbUn "i" (.arbUn "j" (.ident () "foo"))) (.ident () "bar")
  := rfl
  
  public pairDefList exampleStx0
    p3 X := X × A
    p3 A := X × 3
    p3 B := <[testStx3.check]>
  pairDefList.

  @[expose] public pairDefList exampleStx1 extends exampleStx0
    p3 C := A
  pairDefList.
  
end Examples
