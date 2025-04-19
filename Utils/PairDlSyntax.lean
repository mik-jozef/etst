import Lean
import Lean.Elab
import Lean.Parser.Term

import Utils.PairExpr
import Utils.PairFreeVars
import WFC.Ch5_PairSalgebra

open Lean Elab Command Term Meta Syntax


declare_syntax_cat pair_def_list.def
declare_syntax_cat pair_def_list.expr

-- Expressions
syntax:70 ident : pair_def_list.expr
syntax:70 "(" pair_def_list.expr ")" : pair_def_list.expr
syntax:70 "null" : pair_def_list.expr
syntax:70 "(" pair_def_list.expr ", " pair_def_list.expr ")" : pair_def_list.expr
syntax:60 pair_def_list.expr:60 pair_def_list.expr:61 : pair_def_list.expr
syntax:50 "!" pair_def_list.expr:50 : pair_def_list.expr
syntax:40 pair_def_list.expr:40 "|" pair_def_list.expr:41 : pair_def_list.expr
syntax:40 "|" pair_def_list.expr:41 "|" pair_def_list.expr:41 : pair_def_list.expr
syntax:30 pair_def_list.expr:30 "&" pair_def_list.expr:31 : pair_def_list.expr
syntax:30 "&" pair_def_list.expr:31 "&" pair_def_list.expr:31 : pair_def_list.expr
syntax:20 pair_def_list.expr:20 "then" pair_def_list.expr:21 : pair_def_list.expr
syntax:10 pair_def_list.expr:11 "->" pair_def_list.expr:10 : pair_def_list.expr
syntax:9 pair_def_list.expr:10 "<->" pair_def_list.expr:10 : pair_def_list.expr
syntax:00 "Ex " ident ", " pair_def_list.expr : pair_def_list.expr
syntax:00 "Ex " ident ": " pair_def_list.expr ", " pair_def_list.expr : pair_def_list.expr
syntax:00 "All " ident ", " pair_def_list.expr : pair_def_list.expr
syntax:00 "All " ident ": " pair_def_list.expr ", " pair_def_list.expr : pair_def_list.expr

macro_rules
-- Function application
| `(pair_def_list.expr| $fn $arg) =>
  `(pair_def_list.expr| Ex res, $fn & ($arg, res) then res)
-- Remove leading "|"
| `(pair_def_list.expr| | $a | $b) => `(pair_def_list.expr| $a | $b)
-- Remove leading "&"
| `(pair_def_list.expr| & $a & $b) => `(pair_def_list.expr| $a & $b)
-- Implication (->) to disjunction
| `(pair_def_list.expr| $a -> $b) => `(pair_def_list.expr| !$a | $b)
-- Equivalence (<->) to conjunction of implications
| `(pair_def_list.expr| $a <-> $b) =>
  `(pair_def_list.expr| ($a -> $b) & ($b -> $a))
-- Bounded existential quantifier
| `(pair_def_list.expr| Ex $x:ident: $domain, $body) =>
  `(pair_def_list.expr| Ex $x, $(⟨x.raw⟩) & $domain then $body)
-- Bounded universal quantifier
| `(pair_def_list.expr| All $x:ident: $domain, $body) =>
  `(pair_def_list.expr| All $x, (!($(⟨x.raw⟩) & $domain) then Any) | $body)


-- Definitions
syntax "s3 " ident " := " pair_def_list.expr : pair_def_list.def

-- The namespace
syntax (name := pair_def_list.dl)
  "pairDefList" ident pair_def_list.def* "pairDefList." : command


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
    `(pair_def_list.expr| $name:ident) => do
      match vars name.getId with
      | none =>
        throwErrorAt name (s!"Unknown variable '{name.getId}'")
      | some i => `(Expr.var $(mkNumLit i.repr))
  |
    `(pair_def_list.expr| null) => `(PairExpr.zeroExpr)
  |
    `(pair_def_list.expr|
      ($a:pair_def_list.expr, $b:pair_def_list.expr))
    => do
      `(PairExpr.pairExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(pair_def_list.expr| ! $a:pair_def_list.expr)
    => do `(Expr.cpl $(← makeExpr vars bvi a))
  |
    `(pair_def_list.expr|
      $a:pair_def_list.expr | $b:pair_def_list.expr)
    => do
      `(PairExpr.unExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(pair_def_list.expr|
      $a:pair_def_list.expr & $b:pair_def_list.expr)
    => do
      `(PairExpr.irExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(pair_def_list.expr| $a:pair_def_list.expr then $b:pair_def_list.expr)
    => do
      `(PairExpr.ifThenExpr
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(pair_def_list.expr| Ex $x:ident, $body:pair_def_list.expr)
    =>
      let vars := Function.update vars (x.getId) bvi
      let bviLit := mkNumLit bvi.repr
      do `(Expr.arbUn $bviLit $(← makeExpr vars bvi.succ body))
  |
    `(pair_def_list.expr| All $x:ident, $body:pair_def_list.expr)
    =>
      let vars := Function.update vars (x.getId) bvi
      let bviLit := mkNumLit bvi.repr
      do `(Expr.arbIr $bviLit $(← makeExpr vars bvi.succ body))
  |
    stx => do
    match ← liftMacroM (Macro.expandMacro? stx) with
    | some stxNew => do
      makeExpr vars bvi stxNew
    | none => cmdStxErr "pair_def_list.expr"
  
  
  def getVars
    -- (defs: List (TSyntax `pair_def_list.def))
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
      | `(pair_def_list.def| s3 $name:ident := $_) => do
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
    -- (defs: List (TSyntax `pair_def_list.def))
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
      | `(pair_def_list.def| s3 $_ := $expr) =>
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
  
  @[command_elab pair_def_list.dl]
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
