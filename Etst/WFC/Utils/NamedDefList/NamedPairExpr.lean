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

public inductive NamedPairExpr (E: Type*) where
| ident (e: E) (x: String)
| null
| prod (left rite: NamedPairExpr E)
| ir (left rite: NamedPairExpr E)
| full (body: NamedPairExpr E)
| compl (body: NamedPairExpr E)
| arbIr (x: String) (body: NamedPairExpr E)
deriving DecidableEq

public abbrev BasicNamedPairExpr := NamedPairExpr Unit

namespace NamedPairExpr
  exposed def un {E} (l r: NamedPairExpr E) : NamedPairExpr E :=
    .compl (.ir (.compl l) (.compl r))
  
  exposed def some {E} (expr: NamedPairExpr E) : NamedPairExpr E :=
    .compl (.full (.compl expr))
  
  exposed def arbUn {E}
    (x: String)
    (body: NamedPairExpr E)
  :=
    NamedPairExpr.compl (.arbIr x (.compl body))
  
  exposed def nat {E}: Nat → NamedPairExpr E
  | 0 => .null
  | n+1 => .prod (.nat n) .null
  
  
  public abbrev IsValid {E}
    (e: NamedPairExpr E)
    (idents: List String)
  :
    Prop
  :=
    match e with
    | ident _ x => x ∈ idents
    | null => True
    | prod left rite => IsValid left idents ∧ IsValid rite idents
    | ir left rite => IsValid left idents ∧ IsValid rite idents
    | full body => IsValid body idents
    | compl body => IsValid body idents
    | arbIr x body => IsValid body (x :: idents)
  
  exposed def compile {E}
    (expr: NamedPairExpr E)
    (consts vars: List String)
  :
    Expr E
  :=
    match expr with
    | ident e x =>
      if x ∈ vars then
        .var (vars.idxOf x)
      else
        .const e (consts.idxOf x)
    | null => .null
    | prod left rite =>
        .prod
          (left.compile consts vars)
          (rite.compile consts vars)
    | ir left rite =>
        .ir
          (left.compile consts vars)
          (rite.compile consts vars)
    | full body => .full (body.compile consts vars)
    | compl body => .compl (body.compile consts vars)
    | arbIr x body => .arbIr (body.compile consts (x :: vars))
  
  public theorem IsValid.compile_sat_lt {E}
    {expr: NamedPairExpr E}
    {consts vars}
    (isValid: IsValid expr (vars ++ consts))
  :
    (compile expr consts vars).FreeVarsSat (· < vars.length)
  :=
    fun x isUsed =>
    match expr with
    | ident _ x =>
      by unfold NamedPairExpr.compile at isUsed; exact
      match Classical.em (x ∈ vars) with
      | Or.inl xIn => by
        rw [ite_eq_left xIn] at isUsed
        exact isUsed ▸ List.idxOf_lt_length_of_mem xIn
      | Or.inr xNin => by
        rw [ite_eq_right xNin] at isUsed
        exact isUsed.elim
    | null => nomatch isUsed
    | prod left rite =>
      let ⟨isValidL, isValidR⟩ := isValid
      isUsed.elim
        (fun isUsedL => isValidL.compile_sat_lt x isUsedL)
        (fun isUsedR => isValidR.compile_sat_lt x isUsedR)
    | ir left rite =>
      let ⟨isValidL, isValidR⟩ := isValid
      isUsed.elim
        (fun isUsedL => isValidL.compile_sat_lt x isUsedL)
        (fun isUsedR => isValidR.compile_sat_lt x isUsedR)
    | full body =>
      let isValid: IsValid body (vars ++ consts) := isValid
      isValid.compile_sat_lt x isUsed
    | compl body =>
      let isValid: IsValid body (vars ++ consts) := isValid
      isValid.compile_sat_lt x isUsed
    | arbIr xB body =>
      let isValid: IsValid body ((xB :: vars) ++ consts) := isValid
      Nat.lt_of_succ_lt_succ (isValid.compile_sat_lt (x + 1) isUsed)
  
  public theorem IsValid.compile_constsLt {E}
    {expr: NamedPairExpr E}
    {consts vars}
    (isValid: IsValid expr (vars ++ consts))
  :
    (compile expr consts vars).ConstsLt consts.length
  :=
    fun x isUsed =>
    match expr with
    | ident _ x =>
      by unfold NamedPairExpr.compile at isUsed; exact
      match Classical.em (x ∈ vars) with
      | Or.inl xIn => by
        rw [ite_eq_left xIn] at isUsed
        exact isUsed.elim
      | Or.inr xNin => by
        rw [ite_eq_right xNin] at isUsed
        let xInConsts: x ∈ consts :=
          (List.mem_append.mp isValid).resolve_left xNin
        exact isUsed ▸ List.idxOf_lt_length_of_mem xInConsts
    | null => nomatch isUsed
    | prod left rite =>
      let ⟨isValidL, isValidR⟩ := isValid
      isUsed.elim
        (fun isUsedL => isValidL.compile_constsLt x isUsedL)
        (fun isUsedR => isValidR.compile_constsLt x isUsedR)
    | ir left rite =>
      let ⟨isValidL, isValidR⟩ := isValid
      isUsed.elim
        (fun isUsedL => isValidL.compile_constsLt x isUsedL)
        (fun isUsedR => isValidR.compile_constsLt x isUsedR)
    | full body =>
      let isValid: IsValid body (vars ++ consts) := isValid
      isValid.compile_constsLt x isUsed
    | compl body =>
      let isValid: IsValid body (vars ++ consts) := isValid
      isValid.compile_constsLt x isUsed
    | arbIr xB body =>
      let isValid: IsValid body ((xB :: vars) ++ consts) := isValid
      isValid.compile_constsLt x isUsed
  
end NamedPairExpr

public abbrev NamedExprTools.pair:
  NamedExprTools BasicNamedPairExpr
:= {
  IsValid := NamedPairExpr.IsValid,
  compile := (NamedPairExpr.compile · · [])
  valid_compiles_clean isValid :=
    let vars := []
    let satLt := isValid.compile_sat_lt (vars := vars)
    let eq: (· < vars.length) = fun _ => False :=
      funext fun _ => propext (Iff.intro nofun nofun)
    by unfold Expr.IsClean; exact eq ▸ satLt
  valid_compiles_constsLt isValid := isValid.compile_constsLt
}

public instance decIsValid {E}:
    (e: NamedPairExpr E) →
    (consts: List String) →
    Decidable (e.IsValid consts)
| .ident _ x, consts => inferInstanceAs (Decidable (x ∈ consts))
| .null, _ => inferInstanceAs (Decidable True)
| .prod l r, consts =>
  match decIsValid l consts, decIsValid r consts with
  | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
  | isFalse hl, _ => isFalse fun ⟨h, _⟩ => hl h
  | _, isFalse hr => isFalse fun ⟨_, h⟩ => hr h
| .ir l r, consts =>
  match decIsValid l consts, decIsValid r consts with
  | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
  | isFalse hl, _ => isFalse fun ⟨h, _⟩ => hl h
  | _, isFalse hr => isFalse fun ⟨_, h⟩ => hr h
| .full b, consts => decIsValid b consts
| .compl b, consts => decIsValid b consts
| .arbIr x b, consts => decIsValid b (x :: consts)

exposed def Pair.toNamedExpr: Pair → BasicNamedPairExpr
| .null => .null
| .pair l r => .prod l.toNamedExpr r.toNamedExpr

public theorem Pair.toExpr_eq_named
  (p: Pair)
  (consts vars: List String)
:
  p.toExpr = p.toNamedExpr.compile consts vars
:=
  match p with
  | .null => rfl
  | .pair l r =>
    congrArg₂
      BasicExpr.prod
      (l.toExpr_eq_named consts vars)
      (r.toExpr_eq_named consts vars)

namespace SingleLaneExpr
  public theorem inToNamedExpr {lane fv b c consts vars}
    (p: Pair)
  :
    let expr := p.toNamedExpr.compile consts vars
    p ∈ (BasicExpr.toLane expr lane).intp2 fv b c
  :=
    p.toExpr_eq_named consts vars ▸
    inToExpr p
  
  public theorem inToNamedExprElim {lane fv b c consts vars}
    {pExpr p: Pair}
    (inExpr:
      let expr := pExpr.toNamedExpr.compile consts vars
      p ∈ (BasicExpr.toLane expr lane).intp2 fv b c)
  :
    pExpr = p
  := by
    rw [←pExpr.toExpr_eq_named consts vars] at inExpr
    exact inToExprElim inExpr
  
  public theorem intp2_toNamedExpr_eq_singleton {lane fv b c consts vars}
    (p: Pair)
  :
    let expr := p.toNamedExpr.compile consts vars
    intp2 (BasicExpr.toLane expr lane) fv b c = {p}
  :=
    p.toExpr_eq_named consts vars ▸
    intp2_toExpr_eq_singleton p
  
end SingleLaneExpr


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


-- p3(expr) elaborates a p3_expr into a NamedPairExpr.
syntax "p3(" p3_expr ")" : term

open Lean in
macro_rules
-- Parentheses removal
| `(p3( ($expr) )) => `(p3($expr))
-- Function application
| `(p3( $fn $arg )) =>
  `(p3( Ex res, $fn & ($arg × res) then res ))
-- Remove leading "|"
| `(p3( | $a | $b )) => `(p3( $a | $b ))
-- Remove leading "&"
| `(p3( & $a & $b )) => `(p3( $a & $b ))
-- Remove leading "×"
| `(p3( × $a × $b )) => `(p3( $a × $b ))
-- Then to some
| `(p3( $a then $b )) => `(p3( (?some $a) & $b ))
-- Implication (->) to disjunction
| `(p3( $a -> $b )) => `(p3( !$a | $b ))
-- Equivalence (<->) to conjunction of implications
| `(p3( $a <-> $b )) => `(p3( ($a -> $b) & ($b -> $a) ))
-- Multi-variable existential quantifier
| `(p3( Ex $x:ident $y:ident $xs:ident*, $body )) =>
  `(p3( Ex $x, Ex $y $xs*, $body ))
-- Bounded existential quantifier
| `(p3( Ex $x:ident: $domain, $body )) =>
  `(p3( Ex $x, $x:ident & $domain then $body ))
-- Multi-variable universal quantifier
| `(p3( All $x:ident $y:ident $xs:ident*, $body )) =>
  `(p3( All $x, All $y $xs*, $body ))
-- Bounded universal quantifier
| `(p3( All $x:ident: $domain, $body )) =>
  `(p3( All $x, (?some ($x:ident & !$domain)) | $body ))
-- Identifiers
| `(p3( $x:ident )) =>
  `(NamedPairExpr.ident () $(quote x.getId.toString))
| `(p3( . $x:ident )) =>
  `(NamedPairExpr.ident Set3.Lane.posLane $(quote x.getId.toString))
| `(p3( : $x:ident )) =>
  `(NamedPairExpr.ident Set3.Lane.defLane $(quote x.getId.toString))
-- Numbers
| `(p3( $n:num )) => `(NamedPairExpr.nat $n)
-- Null
| `(p3( null )) => `(NamedPairExpr.null)
-- Escape hatch
| `(p3( <[$t]> )) => pure t
-- Kernel constructors
| `(p3( $a × $b )) => `(NamedPairExpr.prod p3($a) p3($b))
| `(p3( $a & $b )) => `(NamedPairExpr.ir p3($a) p3($b))
| `(p3( $a | $b )) => `(NamedPairExpr.un p3($a) p3($b))
| `(p3( (?some $a) )) => `(NamedPairExpr.some p3($a))
| `(p3( (?full $a) )) => `(NamedPairExpr.full p3($a))
| `(p3( ! $a )) => `(NamedPairExpr.compl p3($a))
| `(p3( Ex $x:ident, $body )) =>
  `(NamedPairExpr.arbUn $(quote x.getId.toString) p3($body))
| `(p3( All $x:ident, $body )) =>
  `(NamedPairExpr.arbIr $(quote x.getId.toString) p3($body))


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
            $(quote x.getId.toString) p3($e) $body)
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
  def testStx5: BasicNamedPairExpr := p3(<[NamedPairExpr.null]>)
  
  public pairDefList exampleStx0
    p3 X := X × A
    p3 A := X × 3
  pairDefList.

  @[expose] public pairDefList exampleStx1 extends exampleStx0
    p3 B := A
  pairDefList.
  
end Examples
