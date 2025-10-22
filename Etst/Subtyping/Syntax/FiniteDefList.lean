import Lean
import Lean.Elab
import Lean.Parser.Term

import Etst.Subtyping.Syntax.UsedVarsLt
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.PairExpr

namespace Etst
open Lean Elab Command Term Meta Syntax


def Expr.VarLtSize
  (expr: Expr E sig)
  (size: Nat)
:=
  ∀ y ∈ expr.UsesVar, y < size

def Expr.noneLtSize
  {sig: Signature}
  (size: Nat)
:
  (none (E := E) (sig := sig)).VarLtSize size
:=
  nofun

def DefList.DependsOn.toUsesVar
  {getDef: GetDef sig}
  (depOn: DependsOn getDef a b)
:
  ∃ x, (getDef x).UsesVar b
:=
  -- Why this no work. TODO investigate finally
  -- match depOn with
  -- | Base usesVar => ⟨_, usesVar⟩
  -- | Rec usesVar depOn => depOn.toUsesVar
  depOn.rec (fun usesVar => ⟨_, usesVar⟩) (fun _ _ => id)


def FiniteDefList.VarLtSize
  (getDef: DefList.GetDef sig)
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

structure FiniteDefList
  (sig: Signature)
extends
  FinBoundedDL sig
where
  varList: List String
  varLtSize: FiniteDefList.VarLtSize getDef varList.length
  isFinBounded := FiniteDefList.isFinBounded_of_varLtSize varLtSize

def FiniteDefList.size
  (dl: FiniteDefList sig)
:=
  dl.varList.length

def FiniteDefList.empty: FiniteDefList sig := {
  getDef := fun _ => Expr.none
  varList := []
  varLtSize := fun _ => Expr.noneLtSize _
}

def FiniteDefList.emptySizeZero:
  (empty (sig := sig)).size = 0
:=
  rfl

structure FiniteDefList.Def (sig: Signature) (size: Nat) where
  name: String
  expr: BasicExpr sig
  varLt: expr.VarLtSize size

def FiniteDefList.defsGetNth
  (defs: List (Def sig ub))
  (n: Nat)
:
  Def sig ub
:=
  defs[n]?.getD {
    name := "«empty»"
    expr := Expr.none
    varLt := Expr.noneLtSize ub
  }

def FiniteDefList.defsToGetDef
  (defs: List (Def sig ub))
:
  DefList.GetDef sig
:=
  fun x => (defsGetNth defs x).expr

def FiniteDefList.extend
  (dl: FiniteDefList sig)
  (defs: List (Def sig ub))
  (ubEq: ub = dl.size + defs.length)
:
  FiniteDefList sig
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
  }

def FiniteDefList.ofDefs
  (defs: List (Def sig ub))
  (ubEq: ub = defs.length)
:
  FiniteDefList sig
:=
  empty.extend defs (by
    rw [emptySizeZero, Nat.zero_add];
    exact ubEq)


declare_syntax_cat s3_pair_def
declare_syntax_cat s3_pair_expr

-- Expressions
syntax:70 ident : s3_pair_expr
syntax:70 "."ident : s3_pair_expr
syntax:70 ":"ident : s3_pair_expr
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

def s3IdentOfIdent
  (ident: TSyntax `ident)
:
  TSyntax `s3_pair_expr
:= {
  raw :=
    match ident.raw.getInfo? with
    | some srcInfo =>
      Syntax.node srcInfo `s3_pair_expr_ #[ident]
    | none => missing
}

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
-- Implication (->) to disjunction
| `(s3_pair_expr| $a -> $b) => `(s3_pair_expr| !$a | $b)
-- Equivalence (<->) to conjunction of implications
| `(s3_pair_expr| $a <-> $b) =>
  `(s3_pair_expr| ($a -> $b) & ($b -> $a))
-- Bounded existential quantifier
| `(s3_pair_expr| Ex $x:ident: $domain, $body) =>
  `(s3_pair_expr| Ex $x, $(s3IdentOfIdent x) & $domain then $body)
-- Bounded universal quantifier
| `(s3_pair_expr| All $x:ident: $domain, $body) =>
  `(s3_pair_expr|
    All $x,
    (!($(s3IdentOfIdent x) & $domain) then
    $(s3IdentOfIdent <| mkIdent `Any)) | $body)


-- Definitions
syntax "s3 " ident " := " s3_pair_expr : s3_pair_def

-- The namespace
syntax (name := pair_def_list)
  "pairDefList " ident (" extends "  ident)?
    s3_pair_def*
  "pairDefList." : command


namespace pair_def_list
  
  def termStxErr
    (stx: Syntax)
    (item: String)
  :
    TermElabM T
  :=
    throwErrorAt
      stx
      s!"Implementation error: unexpected syntax for {item}."
  
  def cmdStxErr
    (stx: Syntax)
    (item: String)
  :
    CommandElabM T
  :=
    throwErrorAt
      stx
      s!"Implementation error: unexpected syntax for {item}."
  
  structure ReservedName where
    stx: TSyntax `s3_pair_def
    name: String
    descr: String
  
  def getReservedNames:
    CommandElabM (List ReservedName)
  := do
    let anyDef ← `(s3_pair_def| s3 $(mkIdent `Any) := Ex x, x)
    let noneDef ← `(s3_pair_def| s3 $(mkIdent `None) := All x, x)
    return [
      ⟨anyDef, "Any", "universal"⟩,
      ⟨noneDef, "None", "empty"⟩,
    ]
  
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
    `(s3_pair_expr| null) => `(PairExpr.null)
  |
    `(s3_pair_expr|
      ($a:s3_pair_expr, $b:s3_pair_expr))
    => do
      `(PairExpr.pair
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| ! $a:s3_pair_expr)
    => do `(Expr.compl $(← makeExpr vars bvi a))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr | $b:s3_pair_expr)
    => do
      `(PairExpr.un
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr|
      $a:s3_pair_expr & $b:s3_pair_expr)
    => do
      `(PairExpr.ir
        $(← makeExpr vars bvi a)
        $(← makeExpr vars bvi b))
  |
    `(s3_pair_expr| $a:s3_pair_expr then $b:s3_pair_expr)
    => do
      `(PairExpr.ifThen
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
    (reservedNames: List ReservedName)
    (nameStx: TSyntax `ident)
  :
    TermElabM Vars
  := do
    let resName name val :=
      s!"'{name}' is a reserved variable name denoting the {val} type."
    
    let name := nameStx.getId.toString
    
    if vars.enc name != none then
      let filter := (ReservedName.name · == name)
      match reservedNames.find? filter with
      | some ⟨_, _, descr⟩ =>
        throwErrorAt nameStx (resName name descr)
      | _ =>
        throwErrorAt nameStx (s!"Duplicate variable '{name}'.")
    else
      return vars.concat name
  
  -- For a def list named `dl`, generates `def dl.vars.foo: Nat := ...`.
  def Vars.getVarDefs
    (vars: Vars)
    (dlName: Name)
    (list: List String := vars)
  :
    CommandElabM (TSyntaxArray `command)
  := do
    match list with
    | [] => return #[]
    | name :: list =>
      let num :=
        ← match vars.indexesOf name with
        | [] => throwError "Implementation error; Vars.getVarDefs"
        | _::_::_ => throwError "Implementation error; Vars.getVarDefs"
        | [num] => return mkNumLit num.repr
      
      let var ← `(
        def $(mkIdent ((dlName.append `vars).append name.toName)) :=
          $num
      )
      let val ← `(
        def $(mkIdent ((dlName.append `vals).append name.toName)) :=
          ($(mkIdent dlName)).getDef $num
      )
      return #[ var, val ].append (← vars.getVarDefs dlName list)
      
  
  -- Get all variable names defined in the def list.
  def getVars
    (reservedNames: List ReservedName)
    (defs: List Syntax)
    (varsSoFar: Vars)
  :
    TermElabM Vars
  :=
    match defs with
    | [] => return varsSoFar
    | df :: defs =>
      match df with
      | `(s3_pair_def| s3 $name:ident := $_) => do
        let varsSoFar ← varsSoFar.push reservedNames name
        getVars reservedNames defs varsSoFar
      | stx => termStxErr stx "s3 in pairDefList"
  
  def getFinDefListVars
    (reservedNames: List ReservedName)
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
          (mkApp2
            (.const ``FiniteDefList.varList [0, 0])
            (.const ``pairSignature [])
            expr)
        
        varList.foldlM
          (fun vars name =>
            vars.push reservedNames (mkIdent name.toName))
          Vars.empty
  
  
  def getDefs
    (vars: Vars)
    (defs: List Syntax)
  :
    TermElabM (TSyntax `term)
  := do
    match defs with
    | [] => `([])
    | df :: defs =>
      -- Why can't I merge these match expressions into one?
      match df with
      | `(s3_pair_def| s3 $name := $expr) =>
        let expr ← makeExpr vars.enc 0 expr
        let size ← `($(mkNumLit vars.length.repr))
        let df ← `({
          expr := $expr
          name := $(mkStrLit name.getId.toString)
          varLt :=
            fun x isUsed =>
              match h: Pair.usedVarsLt $expr $size with
              | .isTrue isLe => isLe ⟨_, isUsed⟩
              | .none => Witness.noConfusion h
        })
        `($df :: $(← getDefs vars defs))
      | stx =>
        termStxErr stx "s3 in pairDefList"
  
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
        let reservedNames ← getReservedNames
        let reservedDefs :=
          match parentName with
          | none => reservedNames.map ReservedName.stx
          | some _ => []
        
        let defs := reservedDefs ++ defsArr.toList
        let parentVars ←
          liftTermElabM $ getFinDefListVars reservedNames parentName
        let vars ←
          liftTermElabM $ getVars reservedNames defs parentVars
        
        if diagnostics.get (← getOptions) then
          logInfo s!"Declared variables: {repr vars}"
        
        let output ← `(
          def $name : FiniteDefList pairSignature :=
            let parent := $(← getParent parentName)
            let defs := $(← liftTermElabM $ getDefs vars defs)
            
            FiniteDefList.extend parent defs (by decide)
          
          def a := 4 -- TODO if you delete this, .vars stop working
        )
        
        -- TODO try creating a new root node instead of this
        match output.raw with
        | Syntax.node _ kind args =>
          let varDefs ← vars.getVarDefs name.getId
          return Syntax.node .none kind (args.append varDefs)
        | _ =>
          throwError "Implementation error, output not node; pairDefListImpl"
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
  
  -- equals 7 because of Any and None.
  example: ExampleDL2.vars.C = 7 := rfl
  
end pair_def_list

open pair_def_list in
elab head:("s3(" <|> "s3:(") dl:ident ", " expr:s3_pair_expr ")" : term => do
  let vars ← getFinDefListVars [] dl
  let result ← makeExpr vars.enc 0 expr
  let expectedType ←
    match head.raw with
    | node _ _ #[atom _ "s3("]  => ``(BasicPairExpr)
    | node _ _ #[atom _ "s3:("] => ``(SingleLanePairExpr)
    | _ => throwError "Implementation error: impossible head syntax"
  let expectedTypeExpr ← elabTerm expectedType none
  elabTerm result (some expectedTypeExpr)

set_option pp.rawOnError true
-- Test the new s3 syntax
#check s3(Etst.pair_def_list.ExampleDL, X | Y)
#check s3(pair_def_list.ExampleDL2, C | Y)

#check s3:(Etst.pair_def_list.ExampleDL, .X | :Y)
#check s3:(pair_def_list.ExampleDL2, :C | :Y)
