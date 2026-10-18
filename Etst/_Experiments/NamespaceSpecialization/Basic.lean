import Lean

/-!
  Registry of specialized namespaces and the `specialized_namespace`
  attribute. See `Etst._Experiments.NamespaceSpecialization.NamespaceSpecialization`.
-/

namespace Etst.SpecializedNs
open Lean Meta Elab Term


/--
  A namespace whose declarations are found by dot notation on values
  whose type is an instance of `pattern`.
-/
structure Entry where
  ns: Name
  -- Head constant of the body of `pattern`.
  head: Name
  levelParams: List Name
  -- A closed `fun xs => head args`.
  pattern: Expr
  -- Declared using `namespace (T)` rather than the attribute.
  bare: Bool
deriving Inhabited

initialize ext: SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

def getEntries (env: Environment): Array Entry := ext.getState env


def Entry.instantiate (e: Entry): MetaM Expr := do
  let us ← e.levelParams.mapM fun _ => mkFreshLevelMVar
  let (_, _, body) ← lambdaMetaTelescope (e.pattern.instantiateLevelParams e.levelParams us)
  return body

-- Does not assign metavariables of `type`.
def Entry.matches (e: Entry) (type: Expr): MetaM Bool :=
  withNewMCtxDepth do withReducible do isDefEq (← e.instantiate) type

-- Every instance of `a` is an instance of `b`.
def Entry.le (a b: Entry): MetaM Bool :=
  lambdaTelescope a.pattern fun _ body => b.matches body

def Entry.equiv (a b: Entry): MetaM Bool := do
  return (← a.le b) && (← b.le a)

def mkEntry
  (ns: Name)
  (xs: Array Expr)
  (type: Expr)
  (bare: Bool)
:
  TermElabM Entry
:= do
  let type ← instantiateMVars type
  unless ← isType type do
    throwError "Expected a type, got{indentExpr type}"
  let body ← whnfR type
  let .const head _ := body.getAppFn |
    throwError "Expected a type of the form `C ...` where `C` is a constant, got{indentExpr type}"
  let pattern ← Term.levelMVarToParam (← instantiateMVars (← mkLambdaFVars xs body))
  if pattern.hasMVar then
    throwError "Could not infer all parts of the namespace pattern{indentExpr pattern}"
  let levelParams := (collectLevelParams {} pattern).params.toList
  return { ns, head, levelParams, pattern, bare }


/--
  Makes the namespace of an abbreviation a specialized namespace: dot
  notation on any value whose type is an instance of the abbreviation
  (up to reducible unfolding) looks into it.
  
  ```
  @[specialized_namespace] abbrev BasicExpr (sig: Signature) := Expr sig Unit
  def BasicExpr.intp2 ... := ...
  example (e: Expr sig Unit) := e.intp2 ...
  ```
-/
initialize registerBuiltinAttribute {
  name := `specialized_namespace
  descr := "Dot notation on instances of this abbreviation looks into its namespace."
  add := fun decl _ kind => do
    unless kind == .global do
      throwError "`specialized_namespace` must be global"
    let info ← getConstInfo decl
    let some value := info.value? |
      throwError "`specialized_namespace` requires an `abbrev`"
    unless (← getReducibilityStatus decl) == .reducible || info.hints.isAbbrev do
      throwError "`specialized_namespace` requires an `abbrev`, as patterns are \
        matched up to reducible unfolding"
    let entry ← MetaM.run' <| TermElabM.run' do
      lambdaTelescope (← etaExpand value) fun xs body => mkEntry decl xs body false
    modifyEnv (ext.addEntry · entry)
}

end Etst.SpecializedNs
