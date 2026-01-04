import Lean
import Lean.Elab
import Lean.Parser.Term

import Etst.Subtyping.Syntax.UsedVarsLt
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.PairExpr

namespace Etst
open Lean Elab Command Term Meta Syntax


def Expr.VarLtSize
  (expr: Expr E)
  (size: Nat)
:=
  ∀ y ∈ expr.UsesVar, y < size

def Expr.noneLtSize
  (size: Nat)
:
  (none (E := E)).VarLtSize size
:=
  nofun

def DefList.DependsOn.toUsesVar {getDef a b}
  (depOn: DependsOn getDef a b)
:
  ∃ x, (getDef x).UsesVar b
:=
  match depOn with
  | Base usesVar => ⟨_, usesVar⟩
  | Rec _ depOn => depOn.toUsesVar


def FiniteDefList.VarLtSize
  (getDef: DefList.GetDef)
  (size: Nat)
:=
  ∀ x, (getDef x).VarLtSize size

def FiniteDefList.isFinBounded_of_varLtSize
  (varLtSize: VarLtSize getDef size)
:
  DefList.IsFinBounded getDef
:=
  fun _ => ⟨
    size,
    fun depOn =>
      let ⟨x, usesVar⟩ := depOn.toUsesVar
      varLtSize x _ usesVar,
  ⟩

structure FiniteDefList extends FinBoundedDL where
  varList: List String
  varLtSize: FiniteDefList.VarLtSize getDef varList.length
  isFinBounded := FiniteDefList.isFinBounded_of_varLtSize varLtSize

def FiniteDefList.size
  (dl: FiniteDefList)
:=
  dl.varList.length

def FiniteDefList.empty: FiniteDefList := {
  getDef := fun _ => Expr.none
  varList := []
  varLtSize := fun _ => Expr.noneLtSize _
  isClean := fun _ => rfl
}

def FiniteDefList.emptySizeZero: empty.size = 0 := rfl

structure FiniteDefList.Def (size: Nat) where
  name: String
  expr: BasicExpr
  varLt: expr.VarLtSize size
  isClean: expr.IsClean

def FiniteDefList.defsGetNth
  (defs: List (Def ub))
  (n: Nat)
:
  Def ub
:=
  defs[n]?.getD {
    name := "«empty»"
    expr := Expr.none
    varLt := Expr.noneLtSize ub
    isClean := rfl
  }

def FiniteDefList.defsToGetDef
  (defs: List (Def ub))
:
  DefList.GetDef
:=
  fun x => (defsGetNth defs x).expr

def FiniteDefList.extend
  (dl: FiniteDefList)
  (defs: List (Def ub))
  (ubEq: ub = dl.size + defs.length)
:
  FiniteDefList
:=
  let getDef :=
    fun x =>
      if x < dl.size
      then dl.getDef x
      else defsToGetDef defs (x - dl.size)
  {
    getDef
    varList := dl.varList ++ defs.map Def.name
    varLtSize :=
      fun x y (usesVar: (getDef x).UsesVar y) => by
        unfold getDef at usesVar
        rw [List.length_append]
        if h: x < dl.size then
          rw [if_pos h] at usesVar
          apply Nat.lt_add_right
          exact dl.varLtSize x y usesVar
        else
          rw [if_neg h] at usesVar
          unfold size at ubEq
          rw [List.length_map, ←ubEq]
          exact (defsGetNth defs (x - dl.size)).varLt _ usesVar
    isClean := by
      intro x
      unfold getDef
      if h: x < dl.size then
        rw [if_pos h]
        exact dl.isClean x
      else
        rw [if_neg h]
        exact (defsGetNth defs (x - dl.size)).isClean
  }

def FiniteDefList.ofDefs
  (defs: List (Def ub))
  (ubEq: ub = defs.length)
:
  FiniteDefList
:=
  empty.extend defs (by
    rw [emptySizeZero, Nat.zero_add];
    exact ubEq)

def FiniteDefList.Prelude: FiniteDefList :=
  FiniteDefList.ofDefs (ub := 2) [
    {
      name := "Any"
      expr := Expr.arbUn (Expr.bvar 0)
      varLt := fun _ h => nomatch h
      isClean := rfl
    },
    {
      name := "None"
      expr := Expr.arbIr (Expr.bvar 0)
      varLt := fun _ h => nomatch h
      isClean := rfl
    }
  ] rfl


declare_syntax_cat s3_pair_def
declare_syntax_cat s3_pair_expr

-- Expressions
syntax:70 ident : s3_pair_expr
syntax:70 "."ident : s3_pair_expr
syntax:70 ":"ident : s3_pair_expr
syntax:70 "(?some " s3_pair_expr ")" : s3_pair_expr
syntax:70 "(?full " s3_pair_expr ")" : s3_pair_expr
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
-- Parentheses removal
| `(s3_pair_expr| ($expr)) => `(s3_pair_expr| $expr)
-- Function application
| `(s3_pair_expr| $fn $arg) =>
  `(s3_pair_expr| Ex res, $fn & ($arg, res) then res)
-- Remove leading "|"
| `(s3_pair_expr| | $a | $b) => `(s3_pair_expr| $a | $b)
-- Remove leading "&"
| `(s3_pair_expr| & $a & $b) => `(s3_pair_expr| $a & $b)
-- Then to condSome
| `(s3_pair_expr| $a then $b) => `(s3_pair_expr| (?some $a) & $b)
-- Implication (->) to disjunction
| `(s3_pair_expr| $a -> $b) => `(s3_pair_expr| !$a | $b)
-- Equivalence (<->) to conjunction of implications
| `(s3_pair_expr| $a <-> $b) =>
  `(s3_pair_expr| ($a -> $b) & ($b -> $a))
-- Bounded existential quantifier
| `(s3_pair_expr| Ex $x:ident: $domain, $body) =>
  `(s3_pair_expr| Ex $x, $(x):ident & $domain then $body)
-- Bounded universal quantifier
| `(s3_pair_expr| All $x:ident: $domain, $body) =>
  `(s3_pair_expr| All $x, (?some ($(x):ident & !$domain)) | $body)


-- Definitions
syntax "s3 " ident " := " s3_pair_expr : s3_pair_def

-- The namespace
syntax (name := pair_def_list)
  "pairDefList " ident (" extends "  ident)?
    s3_pair_def*
  "pairDefList." : command


namespace pair_def_list
  
  def termStxErr {T}
    (stx: Syntax)
    (item: String)
  :
    TermElabM T
  :=
    throwErrorAt
      stx
      s!"Implementation error: unexpected syntax for {item}."
  
  def cmdStxErr {T}
    (stx: Syntax)
    (item: String)
  :
    CommandElabM T
  :=
    throwErrorAt
      stx
      s!"Implementation error: unexpected syntax for {item}."
  
  inductive VarRepr
  | var (x: Nat)
  | bvar (x: Nat)
  deriving DecidableEq
  
  -- Convert `s3_pair_expr` syntax to a Lean term representing `Expr`
  partial def makeExpr
    (vars: String → Option VarRepr)
    (bvi: Nat := 0) -- bound variable index
  :
    Syntax →
    TermElabM (TSyntax `term)
  |
    `(s3_pair_expr| $name:ident) => do
      match vars name.getId.toString with
      | none =>
        throwErrorAt name (s!"Unknown variable '{name.getId}'")
      | some (.var x) => `(Expr.var () $(mkNumLit x.repr))
      | some (.bvar x) => `(Expr.bvar $(mkNumLit x.repr))
  |
    `(s3_pair_expr| .$name:ident) => do
      match vars name.getId.toString with
      | none =>
        throwErrorAt name (s!"Unknown variable '{name.getId}'")
      | some (.var x) => `(SingleLaneExpr.var .posLane $(mkNumLit x.repr))
      | some (.bvar _) =>
        throwErrorAt name (s!"Bound variable cannot have a lane selector.")
  |
    `(s3_pair_expr| :$name:ident) => do
      match vars name.getId.toString with
      | none =>
        throwErrorAt name (s!"Unknown variable '{name.getId}'")
      | some (.var x) => `(SingleLaneExpr.var .defLane $(mkNumLit x.repr))
      | some (.bvar _) =>
        throwErrorAt name (s!"Bound variable cannot have a lane selector.")
  |
    `(s3_pair_expr| null) => `(Expr.null)
  |
    `(s3_pair_expr|
      (?some $body:s3_pair_expr))
    => do
      `(Expr.condSome $(← makeExpr vars bvi body))
  |
    `(s3_pair_expr|
      (?full $body:s3_pair_expr))
    => do
      `(Expr.condFull $(← makeExpr vars bvi body))
  |
    `(s3_pair_expr|
      ($a:s3_pair_expr, $b:s3_pair_expr))
    => do
      `(Expr.pair
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| ! $a:s3_pair_expr)
    => do `(Expr.compl $(← makeExpr vars bvi a))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr | $b:s3_pair_expr)
    => do
      `(Expr.un
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr & $b:s3_pair_expr)
    => do
      `(Expr.ir
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| $a:s3_pair_expr then $b:s3_pair_expr)
    => do
      `(Expr.ifThen
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| Ex $x:ident, $body:s3_pair_expr)
    => do
      let var := some (.bvar bvi)
      let vars := Function.update vars x.getId.toString var
      `(Expr.arbUn $(← makeExpr vars bvi.succ body))
  |
    `(s3_pair_expr| All $x:ident, $body:s3_pair_expr)
    => do
      let var := some (.bvar bvi)
      let vars := Function.update vars x.getId.toString var
      `(Expr.arbIr $(← makeExpr vars bvi.succ body))
  |
    stx => do
    match ← liftMacroM (Macro.expandMacro? stx) with
    | some stxNew => do
      makeExpr vars bvi stxNew
    | none => termStxErr stx "s3_pair_expr"
  
  
  abbrev Vars := List String
  
  def Vars.empty: Vars := []
  
  def Vars.enc (vars: Vars) (x: String): Option VarRepr :=
    match vars.idxOf? x with
    | none => none
    | some n => some (.var n)
  
  def Vars.push
    (vars: Vars)
    (nameStx: TSyntax `ident)
  :
    TermElabM Vars
  := do
    let name := nameStx.getId.toString
    
    if vars.enc name != none then
      throwErrorAt nameStx (s!"Duplicate variable '{name}'.")
    else
      return vars.concat name
  
  -- For a def list named `dl`, generates `def dl.vars.foo: Nat := ...`.
  def Vars.getVarDefs
    (vars: Vars)
    (dlName: Name)
  :
    CommandElabM (TSyntaxArray `command)
  := do
    let mut cmds := #[]
    let mut i := 0
    for name in vars do
      let num := mkNumLit i.repr
      let varName := mkIdent ((dlName.append `vars).append name.toName)
      let valName := mkIdent ((dlName.append `vals).append name.toName)
      let dlIdent := mkIdent dlName
      
      cmds := cmds.push (← `(def $varName := $num))
      cmds := cmds.push (← `(def $valName := ($dlIdent).getDef $num))
      i := i + 1
    return cmds
      
  
  -- Get all variable names defined in the def list.
  def getVars
    (defs: List Syntax)
    (varsSoFar: Vars)
  :
    TermElabM Vars
  :=
    defs.foldlM (init := varsSoFar) fun vars df => do
      match df with
      | `(s3_pair_def| s3 $name:ident := $_) =>
        vars.push name
      | stx => termStxErr stx "s3 in pairDefList"
  
  def getFinDefListVars
    (defListName: Option (TSyntax `ident))
  :
    TermElabM Vars
  :=
    match defListName with
    | none => return Vars.empty
    | some parentName => do
      let name ← resolveGlobalConstNoOverload parentName
      let env ← getEnv
      match env.find? name with
      | none =>
        throwErrorAt parentName s!"Impossible -- we just resolved the name."
      | some parentInfo =>
        let expr ← instantiateValueLevelParams parentInfo []
        let varList ← liftMetaM $ unsafe evalExpr
          (List String)
          (mkApp (.const ``List [0]) (.const ``String []))
          (mkApp
            (.const ``FiniteDefList.varList [])
            expr)
        
        varList.foldlM
          (fun vars name =>
            vars.push (mkIdent name.toName))
          Vars.empty
  
  
  def getDefs
    (vars: Vars)
    (defs: List Syntax)
  :
    TermElabM (TSyntax `term)
  := do
    let defsTerms ← defs.mapM fun df => do
      match df with
      | `(s3_pair_def| s3 $name := $expr) =>
        let expr ← makeExpr vars.enc 0 expr
        let size := mkNumLit vars.length.repr
        `({
          expr := $expr
          name := $(mkStrLit name.getId.toString)
          varLt :=
            fun x isUsed =>
              match h: Pair.usedVarsLt $expr $size with
              | .isTrue isLe => isLe ⟨_, isUsed⟩
              | .none => Witness.noConfusion h
          isClean := rfl
        })
      | stx => termStxErr stx "s3 in pairDefList"
    
    let defsTermsArray := defsTerms.toArray
    `([$defsTermsArray,*])
  
  def getParent
    (parentName: Option (TSyntax `ident))
  :
    CommandElabM (TSyntax `term)
  :=
    match parentName with
    | none => `(FiniteDefList.empty)
    | some parentName => `($parentName)
  
  @[command_elab pair_def_list]
  def pairDefListImpl : CommandElab :=
    Command.adaptExpander fun stx => do
      match stx with
      | `(pairDefList $name $[extends $parentName]?
          $defsArr*
        pairDefList.)
      =>
        let defs := defsArr.toList
        let parentVars ←
          liftTermElabM $ getFinDefListVars parentName
        let vars ←
          liftTermElabM $ getVars defs parentVars
        
        if diagnostics.get (← getOptions) then
          logInfo s!"Declared variables: {repr vars}"
        
        let mainDef ← `(
          def $name : FiniteDefList :=
            let parent := $(← getParent parentName)
            let defs := $(← liftTermElabM $ getDefs vars defs)
            
            FiniteDefList.extend parent defs (by decide)
        )
        
        let varDefs ← vars.getVarDefs name.getId
        return mkNullNode ((#[mainDef] ++ varDefs).map (·.raw))
      | stx => cmdStxErr stx "pairDefList"
  
  -- set_option diagnostics true
  -- Example definition list:
  pairDefList ExampleDL
    s3 X := Ex x, x
    s3 Y := All y, y
    s3 Z := (X, Y) | !(X & Y)
  pairDefList.
  
  pairDefList ExampleDL2 extends ExampleDL
    s3 A := (X, Y)
    s3 B := !(X & Y)
    s3 C := A | B
  pairDefList.
  
  -- #print ExampleDL
  
  example: ExampleDL2.vars.C = 5 := rfl
  
end pair_def_list

open pair_def_list in
elab "s3(" dl:ident ", " expr:s3_pair_expr ")" : term => do
  let vars ← getFinDefListVars (some dl)
  let result ← makeExpr vars.enc 0 expr
  elabTerm result none

set_option pp.rawOnError true
-- Test the new s3 syntax
#check s3(Etst.pair_def_list.ExampleDL, X | Y)
#check s3(pair_def_list.ExampleDL2, C | Y)

#check s3(Etst.pair_def_list.ExampleDL, .X | :Y)
#check s3(pair_def_list.ExampleDL2, :C | :Y)
