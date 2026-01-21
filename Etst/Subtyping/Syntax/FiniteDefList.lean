import Lean
import Lean.Elab
import Lean.Parser.Term

import Etst.Subtyping.Utils.ExprConstsVarsSat
import Etst.WFC.Ch4_S1_AProofSystem
import Etst.WFC.Utils.PairExpr

namespace Etst
open Lean Elab Command Term Meta Syntax


def Expr.noneLtSize {E: Type*}
  (size: Nat)
:
  (none (E := E)).ConstsLt size
:=
  nofun

def DefList.DependsOn.toUsesConst {getDef a b}
  (depOn: DependsOn getDef a b)
:
  ∃ x, (getDef x).UsesConst b
:=
  match depOn with
  | Base usesVar => ⟨_, usesVar⟩
  | Rec _ depOn => depOn.toUsesConst


def FiniteDefList.ConstsLt
  (getDef: DefList.GetDef)
  (size: Nat)
:=
  ∀ x, (getDef x).ConstsLt size

def FiniteDefList.isFinBounded_of_constsLt {getDef size}
  (constsLt: ConstsLt getDef size)
:
  DefList.IsFinBounded getDef
:=
  fun _ => ⟨
    size,
    fun depOn =>
      let ⟨x, usesVar⟩ := depOn.toUsesConst
      constsLt x _ usesVar,
  ⟩

structure FiniteDefList extends FinBoundedDL where
  constNames: List String
  constsLt: FiniteDefList.ConstsLt getDef constNames.length
  isFinBounded := FiniteDefList.isFinBounded_of_constsLt constsLt

def FiniteDefList.size
  (dl: FiniteDefList)
:=
  dl.constNames.length

def FiniteDefList.empty: FiniteDefList := {
  getDef := fun _ => Expr.none
  constNames := []
  constsLt := fun _ => Expr.noneLtSize _
  isClean := fun _ => by decide
}

def FiniteDefList.emptySizeZero: empty.size = 0 := rfl

structure FiniteDefList.Def (size: Nat) where
  name: String
  expr: BasicExpr
  constsLt: expr.ConstsLt size
  isClean: expr.IsClean

def FiniteDefList.defsGetNth {ub} 
  (defs: List (Def ub))
  (n: Nat)
:
  Def ub
:=
  defs[n]?.getD {
    name := "«empty»"
    expr := Expr.none
    constsLt := Expr.noneLtSize ub
    isClean := by decide
  }

def FiniteDefList.defsToGetDef {ub}
  (defs: List (Def ub))
:
  DefList.GetDef
:=
  fun x => (defsGetNth defs x).expr

def FiniteDefList.extend {ub}
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
    constNames := dl.constNames ++ defs.map Def.name
    constsLt :=
      fun x y (usesVar: (getDef x).UsesConst y) => by
        unfold getDef at usesVar
        rw [List.length_append]
        if h: x < dl.size then
          rw [if_pos h] at usesVar
          apply Nat.lt_add_right
          exact dl.constsLt x y usesVar
        else
          rw [if_neg h] at usesVar
          unfold size at ubEq
          rw [List.length_map, ←ubEq]
          exact (defsGetNth defs (x - dl.size)).constsLt _ usesVar
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

def FiniteDefList.ofDefs {ub}
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
      expr := Expr.arbUn (Expr.var 0)
      constsLt := fun _ h => nomatch h
      isClean := by decide
    },
    {
      name := "None"
      expr := Expr.arbIr (Expr.var 0)
      constsLt := fun _ h => nomatch h
      isClean := by decide
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
-- Then to some
| `(s3_pair_expr| $a then $b) => `(s3_pair_expr| (?some $a) & $b)
-- Implication (->) to disjunction
| `(s3_pair_expr| $a -> $b) => `(s3_pair_expr| !$a | $b)
-- Equivalence (<->) to conjunction of implications
| `(s3_pair_expr| $a <-> $b) =>
  `(s3_pair_expr| ($a -> $b) & ($b -> $a))
-- Bounded existential quantifier
| `(s3_pair_expr| Ex $x:ident: $domain, $body) =>
  `(s3_pair_expr| Ex $x, $x:ident & $domain then $body)
-- Bounded universal quantifier
| `(s3_pair_expr| All $x:ident: $domain, $body) =>
  `(s3_pair_expr| All $x, (?some ($x:ident & !$domain)) | $body)


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
  
  inductive Ident
  | const (x: Nat)
  | var (x: Nat)
  deriving DecidableEq
  
  -- Convert `s3_pair_expr` syntax to a Lean term representing `Expr`
  partial def makeExpr
    (idents: String → Option Ident)
    (varDepth: Nat := 0) -- how many quantifiers we've gone under
  :
    Syntax →
    TermElabM (TSyntax `term)
  |
    `(s3_pair_expr| $name:ident) => do
      match idents name.getId.toString with
      | none =>
        throwErrorAt name (s!"Unknown identifier '{name.getId}'")
      | some (.const x) => `(Expr.const () $(mkNumLit x.repr))
      | some (.var x) => `(Expr.var $(mkNumLit x.repr))
  |
    `(s3_pair_expr| .$name:ident) => do
      match idents name.getId.toString with
      | none =>
        throwErrorAt name (s!"Unknown identifier '{name.getId}'")
      | some (.const x) => `(SingleLaneExpr.const .posLane $(mkNumLit x.repr))
      | some (.var _) =>
        throwErrorAt name (s!"Bound variable cannot have a lane selector.")
  |
    `(s3_pair_expr| :$name:ident) => do
      match idents name.getId.toString with
      | none =>
        throwErrorAt name (s!"Unknown identifier '{name.getId}'")
      | some (.const x) => `(SingleLaneExpr.const .defLane $(mkNumLit x.repr))
      | some (.var _) =>
        throwErrorAt name (s!"Bound variable cannot have a lane selector.")
  |
    `(s3_pair_expr| null) => `(Expr.null)
  |
    `(s3_pair_expr|
      (?some $body:s3_pair_expr))
    => do
      `(Expr.some $(← makeExpr idents varDepth body))
  |
    `(s3_pair_expr|
      (?full $body:s3_pair_expr))
    => do
      `(Expr.full $(← makeExpr idents varDepth body))
  |
    `(s3_pair_expr|
      ($a:s3_pair_expr, $b:s3_pair_expr))
    => do
      `(Expr.pair
        $(← makeExpr idents varDepth a)
        $(← makeExpr idents varDepth b))
  |
    `(s3_pair_expr| ! $a:s3_pair_expr)
    => do `(Expr.compl $(← makeExpr idents varDepth a))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr | $b:s3_pair_expr)
    => do
      `(Expr.un
        $(← makeExpr idents varDepth a)
        $(← makeExpr idents varDepth b))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr & $b:s3_pair_expr)
    => do
      `(Expr.ir
        $(← makeExpr idents varDepth a)
        $(← makeExpr idents varDepth b))
  |
    `(s3_pair_expr| $a:s3_pair_expr then $b:s3_pair_expr)
    => do
      `(Expr.ifThen
        $(← makeExpr idents varDepth a)
        $(← makeExpr idents varDepth b))
  |
    `(s3_pair_expr| Ex $x:ident, $body:s3_pair_expr)
    => do
      let ident := some (.var varDepth)
      let idents := Function.update idents x.getId.toString ident
      `(Expr.arbUn $(← makeExpr idents varDepth.succ body))
  |
    `(s3_pair_expr| All $x:ident, $body:s3_pair_expr)
    => do
      let ident := some (.var varDepth)
      let idents := Function.update idents x.getId.toString ident
      `(Expr.arbIr $(← makeExpr idents varDepth.succ body))
  |
    stx => do
    match ← liftMacroM (Macro.expandMacro? stx) with
    | some stxNew => do
      makeExpr idents varDepth stxNew
    | none => termStxErr stx "s3_pair_expr"
  
  
  abbrev DefNames := List String
  
  def DefNames.empty: DefNames := []
  
  def DefNames.enc (names: DefNames) (x: String): Option Ident :=
    match names.idxOf? x with
    | none => none
    | some n => some (.const n)
  
  def DefNames.push
    (names: DefNames)
    (nameStx: TSyntax `ident)
  :
    TermElabM DefNames
  := do
    let name := nameStx.getId.toString
    
    if names.enc name != none then
      throwErrorAt nameStx (s!"Duplicate identifier '{name}'.")
    else
      return names.concat name
  
  /-
    For a def list named `dl`, generates syntax for
    
    ```
      def dl.consts.foo := [foo's index]
      def dl.vals.foo := dl.getDef [foo's index]
      ...
    ```
  -/
  def DefNames.mkAccessors
    (names: DefNames)
    (dlName: Name)
  :
    CommandElabM (TSyntaxArray `command)
  := do
    let mut cmds := #[]
    let mut i := 0
    for name in names do
      let num := mkNumLit i.repr
      let defName := mkIdent ((dlName.append `consts).append name.toName)
      let valName := mkIdent ((dlName.append `vals).append name.toName)
      let dlIdent := mkIdent dlName
      
      cmds := cmds.push (← `(def $defName := $num))
      cmds := cmds.push (← `(def $valName := ($dlIdent).getDef $num))
      i := i + 1
    return cmds
      
  
  def DefNames.appendNames
    (names: DefNames)
    (toAppend: List Syntax)
  :
    TermElabM DefNames
  :=
    toAppend.foldlM (init := names) fun names df => do
      match df with
      | `(s3_pair_def| s3 $name:ident := $_) =>
        names.push name
      | stx => termStxErr stx "s3 in pairDefList"
  
  def getFinDlDefNames
    (defListName: Option (TSyntax `ident))
  :
    TermElabM DefNames
  :=
    match defListName with
    | none => return DefNames.empty
    | some parentName => do
      let name ← resolveGlobalConstNoOverload parentName
      let env ← getEnv
      match env.find? name with
      | none =>
        throwErrorAt parentName s!"Impossible -- we just resolved the name."
      | some parentInfo =>
        let expr ← instantiateValueLevelParams parentInfo []
        let constNames ← liftMetaM $ unsafe evalExpr
          (List String)
          (mkApp (.const ``List [0]) (.const ``String []))
          (mkApp
            (.const ``FiniteDefList.constNames [])
            expr)
        
        constNames.foldlM
          (fun names name =>
            names.push (mkIdent name.toName))
          DefNames.empty
  
  
  def processDefs
    (names: DefNames)
    (defs: List Syntax)
  :
    TermElabM (TSyntax `term)
  := do
    let defTerms ← defs.mapM fun df => do
      match df with
      | `(s3_pair_def| s3 $name := $expr) =>
        let expr ← makeExpr names.enc 0 expr
        let size := mkNumLit names.length.repr
        `({
          expr := $expr
          name := $(mkStrLit name.getId.toString)
          constsLt := (by decide: ($expr).ConstsLt $size)
          isClean := by decide
        })
      | stx => termStxErr stx "s3 in pairDefList"
    
    let defTermsArray := defTerms.toArray
    `([$defTermsArray,*])
  
  def getParentName
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
        let parentDefNames ←
          liftTermElabM $ getFinDlDefNames parentName
        let names ←
          liftTermElabM $ parentDefNames.appendNames defs
        
        if diagnostics.get (← getOptions) then
          logInfo s!"Declared identifiers: {repr names}"
        
        let mainDef ← `(
          def $name : FiniteDefList :=
            let parent := $(← getParentName parentName)
            let defs := $(← liftTermElabM $ processDefs names defs)
            
            FiniteDefList.extend parent defs rfl
        )
        
        let accessors ← names.mkAccessors name.getId
        return mkNullNode ((#[mainDef] ++ accessors).map (·.raw))
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
  
  example: ExampleDL2.consts.C = 5 := rfl
  
end pair_def_list

open pair_def_list in
elab "s3(" dl:ident ", " expr:s3_pair_expr ")" : term => do
  let names ← getFinDlDefNames (some dl)
  let result ← makeExpr names.enc 0 expr
  elabTerm result none

-- Test the new s3 syntax
example:
  Eq
    s3(Etst.pair_def_list.ExampleDL, X | Y)
    (.un (.const () 0) (.const () 1))
:=
  rfl

example:
  Eq
    s3(pair_def_list.ExampleDL2, C | Y)
    (.un (.const () 5) (.const () 1))
:=
  rfl

example:
  Eq
    s3(Etst.pair_def_list.ExampleDL, .X | :Y)
    (.un (.const .posLane 0) (.const .defLane 1))
:=
  rfl

example:
  Eq
    s3(pair_def_list.ExampleDL2, :C | :Y)
    (.un (.const .defLane 5) (.const .defLane 1))
:=
  rfl
