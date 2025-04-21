import Lean
import Lean.Elab
import Lean.Parser.Term

import Utils.DependsOnRefl
import Utils.PairExpr
import Utils.PairFreeVars
import WFC.Ch5_PairSalgebra

open Lean Elab Command Term Meta Syntax


def Expr.VarLtSize
  (expr: Expr sig)
  (size: Nat)
:=
  ∀ y ∈ expr.IsFreeVar, y < size

def Expr.IsFreeVar.nopeNone
  {P: Prop}
  (isFree: noneExpr.IsFreeVar (sig := sig) bv x)
:
  P
:=
  let ⟨_, ninBvNorEqZero⟩ := isFree
  absurd (.inr rfl) ninBvNorEqZero

def Expr.noneLtSize
  {sig: Signature}
  (size: Nat)
:
  (noneExpr (sig := sig)).VarLtSize size
:=
  fun _ isFree => isFree.nopeNone (sig := sig)


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
      let ⟨x, isFree⟩ := depOn.toIsFree
      varLtSize x _ isFree,
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
  getDef := fun _ => Expr.noneExpr
  varList := []
  varLtSize := fun _ => Expr.noneLtSize _
}

def FiniteDefList.emptySizeZero:
  (empty (sig := sig)).size = 0
:=
  rfl

structure FiniteDefList.Def (sig: Signature) (size: Nat) where
  name: String
  expr: Expr sig
  varLt: expr.VarLtSize size

def FiniteDefList.defsGetNth
  (defs: List (Def sig ub))
  (n: Nat)
:
  Def sig ub
:=
  defs[n]?.getD {
    name := "«empty»"
    expr := Expr.noneExpr
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
      fun x y (isFree: (getDef x).IsFreeVar _ y) => by
        unfold getDef at isFree
        rw [List.length_append]
        if h: x < dl.size then
          rw [if_pos h] at isFree
          apply Nat.lt_add_right
          exact dl.varLtSize x y isFree
        else
          rw [if_neg h] at isFree
          unfold size at ubEq
          rw [List.length_map, ←ubEq]
          exact (defsGetNth defs (x - dl.size)).varLt _ isFree
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


def Expr.IsFreeVar.nope_of_eq_zero
  {P: Prop}
  (isFreeVar: x ∈ expr.IsFreeVar boundVars)
  (eq: expr = PairExpr.zeroExpr)
:
  P
:=
  nomatch eq ▸ isFreeVar

namespace pair_def_list
  
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
  
  def getReservedNames (opt: Option T):
    CommandElabM (List ReservedName)
  := do
    match opt with
    | some _ => return []
    | none =>
      let anyDef ← `(s3_pair_def| s3 $(mkIdent `Any) := Ex x, x)
      let noneDef ← `(s3_pair_def| s3 $(mkIdent `None) := All x, x)
      return [
        ⟨anyDef, "Any", "universal"⟩,
        ⟨noneDef, "None", "empty"⟩,
      ]
  
  
  partial def makeExpr
    (vars: String → Option Nat)
    (bvi: Nat := 0) -- bound variable index
  :
    Syntax →
    CommandElabM (TSyntax `term)
  |
    `(s3_pair_expr| $name:ident) => do
      match vars name.getId.toString with
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
      let vars := Function.update vars x.getId.toString bvi
      let bviLit := mkNumLit bvi.repr
      do `(Expr.arbUn $bviLit $(← makeExpr vars bvi.succ body))
  |
    `(s3_pair_expr| All $x:ident, $body:s3_pair_expr)
    =>
      let vars := Function.update vars x.getId.toString bvi
      let bviLit := mkNumLit bvi.repr
      do `(Expr.arbIr $bviLit $(← makeExpr vars bvi.succ body))
  |
    stx => do
    match ← liftMacroM (Macro.expandMacro? stx) with
    | some stxNew => do
      makeExpr vars bvi stxNew
    | none => cmdStxErr stx "s3_pair_expr"
  
  
  abbrev Vars := List String
  
  def Vars.empty: Vars := []
  def Vars.enc (vars: Vars) (x: String): Option Nat := vars.idxOf? x
  
  def Vars.push
    (vars: Vars)
    (reservedNames: List ReservedName)
    (nameStx: TSyntax `ident)
  :
    CommandElabM Vars
  :=
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
        ← match vars.enc name with
        | some num => return mkNumLit num.repr
        | none => throwError "Implementation error; Vars.getVarDefs"
      
      let var ← `(
        def $(mkIdent ((dlName.append `vars).append name.toName)) :=
          $num
      )
      let val ← `(
        def $(mkIdent ((dlName.append `vals).append name.toName)) :=
          ($(mkIdent dlName)).getDef $num
      )
      return #[ var, val ].append (← vars.getVarDefs dlName list)
      
  
  def getVars
    (reservedNames: List ReservedName)
    (defs: List Syntax)
    (varsSoFar: Vars)
  :
    CommandElabM Vars
  :=
    match defs with
    | [] => return varsSoFar
    | df :: defs =>
      match df with
      | `(s3_pair_def| s3 $name:ident := $_) => do
        let varsSoFar ← varsSoFar.push reservedNames name
        getVars reservedNames defs varsSoFar
      | stx => cmdStxErr stx "s3 in pairDefList"
  
  def getParentVars
    (reservedNames: List ReservedName)
    (parentName: Option (TSyntax `ident))
  :
    CommandElabM Vars
  :=
    match parentName with
    | none => return Vars.empty
    | some parentName => do
      let env ← getEnv
      match env.find? parentName.getId with
      | none =>
        let name := parentName.getId
        throwErrorAt parentName s!"Unknown identifier {name}."
      | some parentInfo =>
        let expr ← liftCoreM $ instantiateValueLevelParams parentInfo []
        let varList ← liftTermElabM $ liftMetaM $ unsafe evalExpr
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
    CommandElabM (TSyntax `term)
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
            fun x isFree =>
              match h: Pair.freeVarsLt $expr [] $size with
              | .isTrue isLe => isLe ⟨_, isFree.toIsFreeEmptyList⟩
              | .none => PosWitness.noConfusion h
        })
        `($df :: $(← getDefs vars defs))
      | stx =>
        cmdStxErr stx "s3 in pairDefList"
  
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
        -- Note: these are empty lists if we're extending.
        let reservedNames ← getReservedNames parentName
        let reservedDefs := reservedNames.map ReservedName.stx
        
        let defs := reservedDefs ++ defsArr.toList
        let parentVars ← getParentVars reservedNames parentName
        let vars ← getVars reservedNames defs parentVars
        
        logInfo (repr vars)
        
        let output ← `(
          def $name : FiniteDefList pairSignature :=
            let parent := $(← getParent parentName)
            let defs := $(← getDefs vars defs)
            
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
end pair_def_list
