import Lean
import Lean.Elab
import Lean.Parser.Term

import Utils.PairExpr
import Utils.PairFreeVars
import WFC.Ch5_PairSalgebra

open Lean Elab Command Term Meta Syntax


declare_syntax_cat s3_pair_def
declare_syntax_cat s3_pair_expr

-- Expressions
syntax:70 ident : s3_pair_expr
syntax:70 "(" s3_pair_expr ")" : s3_pair_expr
syntax:70 "null" : s3_pair_expr
syntax:70 "(" s3_pair_expr ", " s3_pair_expr ")" : s3_pair_expr
syntax:60 s3_pair_expr:60 s3_pair_expr:61 : s3_pair_expr
syntax:50 "!" s3_pair_expr:50 : s3_pair_expr
syntax:40 s3_pair_expr:40 "|" s3_pair_expr:41 : s3_pair_expr
syntax:40 "|" s3_pair_expr:41 "|" s3_pair_expr:41 : s3_pair_expr
syntax:30 s3_pair_expr:30 "&" s3_pair_expr:31 : s3_pair_expr
syntax:30 "&" s3_pair_expr:31 "&" s3_pair_expr:31 : s3_pair_expr
syntax:20 s3_pair_expr:20 "then" s3_pair_expr:21 : s3_pair_expr
syntax:10 s3_pair_expr:11 "->" s3_pair_expr:10 : s3_pair_expr
syntax:9 s3_pair_expr:10 "<->" s3_pair_expr:10 : s3_pair_expr
syntax:00 "Ex " ident ", " s3_pair_expr : s3_pair_expr
syntax:00 "Ex " ident ": " s3_pair_expr ", " s3_pair_expr : s3_pair_expr
syntax:00 "All " ident ", " s3_pair_expr : s3_pair_expr
syntax:00 "All " ident ": " s3_pair_expr ", " s3_pair_expr : s3_pair_expr

macro_rules
-- Function application
| `(s3_pair_expr| $fn $arg) =>
  `(s3_pair_expr| Ex res, $fn & ($arg, res) then res)
-- Remove leading "|"
| `(s3_pair_expr| | $a | $b) => `(s3_pair_expr| $a | $b)
-- Remove leading "&"
| `(s3_pair_expr| & $a & $b) => `(s3_pair_expr| $a & $b)
-- Implication (->) to disjunction
| `(s3_pair_expr| $a -> $b) => `(s3_pair_expr| !$a | $b)
-- Equivalence (<->) to conjunction of implications
| `(s3_pair_expr| $a <-> $b) =>
  `(s3_pair_expr| ($a -> $b) & ($b -> $a))
-- Bounded existential quantifier
| `(s3_pair_expr| Ex $x:ident: $domain, $body) =>
  `(s3_pair_expr| Ex $x, $(⟨x.raw⟩) & $domain then $body)
-- Bounded universal quantifier
| `(s3_pair_expr| All $x:ident: $domain, $body) =>
  `(s3_pair_expr| All $x, (!($(⟨x.raw⟩) & $domain) then Any) | $body)


-- Definitions
syntax "s3 " ident " := " s3_pair_expr : s3_pair_def

-- The namespace
syntax (name := pair_def_list)
  "pairDefList" ident s3_pair_def* "pairDefList." : command


def Expr.IsFreeVar.nope_of_eq_zero
  {P: Prop}
  (isFreeVar: x ∈ expr.IsFreeVar boundVars)
  (eq: expr = PairExpr.zeroExpr)
:
  P
:=
  nomatch eq ▸ isFreeVar

namespace pair_def_list
  
  def termStxErr
    (item: String)
  :
    TermElabM T
  :=
    throwError s!"Implementation error: unexpected syntax for {item}."
  
  def cmdStxErr {T} item :=
    liftTermElabM <| termStxErr (T := T) item
  
  
  partial def makeExpr
    (vars: Name → Option Nat)
    (bvi: Nat := 0) -- bound variable index
  :
    Syntax →
    CommandElabM (TSyntax `term)
  |
    `(s3_pair_expr| $name:ident) => do
      match vars name.getId with
      | none =>
        throwErrorAt name (s!"Unknown variable '{name.getId}'")
      | some i => `(Expr.var $(mkNumLit i.repr))
  |
    `(s3_pair_expr| null) => `(PairExpr.zeroExpr)
  |
    `(s3_pair_expr|
      ($a:s3_pair_expr, $b:s3_pair_expr))
    => do
      `(PairExpr.pairExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| ! $a:s3_pair_expr)
    => do `(Expr.cpl $(← makeExpr vars bvi a))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr | $b:s3_pair_expr)
    => do
      `(PairExpr.unExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr & $b:s3_pair_expr)
    => do
      `(PairExpr.irExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| $a:s3_pair_expr then $b:s3_pair_expr)
    => do
      `(PairExpr.ifThenExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| Ex $x:ident, $body:s3_pair_expr)
    =>
      let vars := Function.update vars (x.getId) bvi
      let bviLit := mkNumLit bvi.repr
      do `(Expr.arbUn $bviLit $(← makeExpr vars bvi.succ body))
  |
    `(s3_pair_expr| All $x:ident, $body:s3_pair_expr)
    =>
      let vars := Function.update vars (x.getId) bvi
      let bviLit := mkNumLit bvi.repr
      do `(Expr.arbIr $bviLit $(← makeExpr vars bvi.succ body))
  |
    stx => do
    match ← liftMacroM (Macro.expandMacro? stx) with
    | some stxNew => do
      makeExpr vars bvi stxNew
    | none => cmdStxErr "s3_pair_expr"
  
  
  def getVars
    -- (defs: List (TSyntax `s3_pair_def))
    (defs: List Syntax)
    -- Used to throw error on a subsequent duplicate variable.
    (varsSoFar: Name → Option Nat := fun _ => none)
    (size: Nat := 0)
  :
    CommandElabM (Name → Option Nat)
  :=
    match defs with
    | [] => return varsSoFar
    | df :: defs =>
      match df with
      | `(s3_pair_def| s3 $name:ident := $_) => do
        if varsSoFar name.getId != none then
          throwErrorAt name (s!"Duplicate variable '{name.getId}'")
        else
          getVars
            defs
            (Function.update varsSoFar (name.getId) size)
            (size + 1)
        | _ => cmdStxErr "s3 in pairDefList"
  
  
  def makeGetDef
    (vars: Name → Option Nat)
    -- (defs: List (TSyntax `s3_pair_def))
    (defs: List Syntax)
    (isZeroth: Bool := true)
  :
    CommandElabM (TSyntax `term)
  := do
    let arg0 ← `((n: Nat))
    let arg1 ← `((_: PairExpr.Expr))
    let args := if isZeroth then #[arg0] else #[arg0, arg1]
    
    match defs with
    | [] => `(fun $[$args]* => PairExpr.zeroExpr)
    | df :: defs =>
      -- Why can't I merge these match expressions into one?
      match df with
      | `(s3_pair_def| s3 $_ := $expr) =>
        `(fun $[$args]* =>
          Nat.rec
            $(← makeExpr vars 0 expr)
            $(← makeGetDef vars defs false)
            n)
      | _ =>
        cmdStxErr "s3 in pairDefList"
  
  
  def makeIsFinBounded.makeMatchClause
    (i: Nat)
    (size: Nat)
  :
    CommandElabM (List (TSyntax ``Parser.Term.matchAlt))
  :=
    let sizeLit := mkNumLit size.repr
    let iLit := mkNumLit i.repr
    if i < size then do
      let clause ←
        `(Parser.Term.matchAltExpr|
          | $iLit =>
            match h: Pair.freeVarsLt (getDef $iLit) [] $sizeLit with
            | .isTrue isLe => isLe usedVar
            | .none => PosWitness.noConfusion h)
      
      let rest ← makeMatchClause i.succ size
      return clause :: rest
    else return [
      ← `(Parser.Term.matchAltExpr|
        | n+$sizeLit =>
          Expr.IsFreeVar.nope_of_eq_zero usedVar.property rfl)
    ]
  
  def makeIsFinBounded
    (size: Nat)
  :
    CommandElabM (TSyntax `term)
  := do
    let sizeLit := mkNumLit size.repr
    
    let matchClauses ← makeIsFinBounded.makeMatchClause 0 size
    let matchExpr ← `(match a with $(matchClauses.toArray):matchAlt*)
    
    `(fun _ =>
      let usedVarsLtSize
        {a}
        (usedVar: Expr.IsFreeVar (getDef a) (fun x => x ∈ []))
      :
        usedVar.val < $sizeLit
      :=
        $matchExpr
      
      let hasFinBounds
        {a b}
        (dependsOn: DefList.DependsOn getDef a b)
      :
        b < $sizeLit
      :=
        dependsOn.rec
          (fun aUsesB => usedVarsLtSize ⟨
            _,
            list_mem_empty_eq_set_empty ▸ aUsesB
          ⟩)
          (fun _ _ => id)
      
      ⟨$sizeLit, hasFinBounds⟩)
  
  @[command_elab pair_def_list]
  def pairDefListImpl : CommandElab :=
    Command.adaptExpander fun stx => do
      match stx with
      | `(pairDefList $name $defs* pairDefList.) =>
        let vars ← getVars defs.toList
        let getDef ← makeGetDef vars defs.toList
        
        `(def $name : FinBoundedDL pairSignature :=
          let getDef := $getDef
          {
            getDef,
            isFinBounded := $(← makeIsFinBounded defs.size),
          })
      | _ =>
        cmdStxErr "pairDefList"
end pair_def_list
