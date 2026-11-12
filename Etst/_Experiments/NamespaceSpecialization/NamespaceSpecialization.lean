import Etst._Experiments.NamespaceSpecialization.Basic

/-!
# Specialized namespaces

Lean's dot notation `x.f` looks for `C.f`, where `C` is the head constant of
the type of `x`. This means that functions that only make sense for some
instantiations of a generic type (eg. `Expr sig Unit`, but not `Expr sig E`)
must either live in the generic namespace `C`, or in the namespace of an
abbreviation, in which case they are only found when the type of `x` is
syntactically that abbreviation.

This file adds *specialized namespaces*: namespaces attached to an
instantiation pattern of a type. Dot notation on a value whose type is an
instance of the pattern looks into the namespace, regardless of how the type
is spelled.

Named version (the namespace of an abbreviation):
```
@[specialized_namespace] abbrev BasicExpr (sig: Signature) := Expr sig Unit
def BasicExpr.intp ... := ...
```

Bare version (an anonymous namespace `C.«(T)»`, where `C` is the head of `T`):
```
namespace {sig} (Expr sig Unit)
  def intp ... := ...
end (Expr sig Unit)

namespace {sig} (Expr sig Unit) in
def intp ... := ...

open {sig} (Expr sig Unit)
```

Both make `x.intp` work for any `x: Expr sig Unit`, and `(Expr sig Unit).intp`
refers to the declaration without calling it.

`P.(h args)` qualifies the head `h` by the namespace `P` when `P` is an
identifier (`Foo.(Bar Nat)` is `Foo.Bar Nat`), and otherwise looks up `h`
in the namespaces of the type `P`. So `Foo.(Bar Nat).(Baz X).boo` is
`((Foo.Bar Nat).Baz X).boo`. This syntax can be used wherever `(T)` can.

## Lookup rules

For `x.f`, the head-unfolding chain of `x`'s type is walked (like Lean does).
At each step with head `C`:
1. specialized namespaces of `C` whose pattern matches the type and that
   declare `f` are collected. If there is one, it is used. If there are
   several, the access is ambiguous (an error), even if one pattern is more
   specific than the others.
2. otherwise, if `C` is not itself a specialized namespace and `C.f` exists,
   Lean's builtin resolution is used (the abbreviation convention: the
   namespace of the type as written wins).

Patterns are matched up to reducible unfolding, so `abbrev`s are transparent
and `def`s are not (consistent with instance resolution).

`(T).f`, where `T` is a type, resolves `f` the same way, without a receiver,
instantiating the implicit parameters of `f` according to `T`. Unless `T`
has the form `P.(U)`, this only applies when `f` is declared in some
specialized namespace. `.f` with an expected type also takes specialized
namespaces into account.

## Implementation

Lean's field resolution is not extensible, so this file adds term
elaborators for the syntax kinds that can contain field accesses. They give
up (`throwUnsupportedSyntax`) unless a field name is declared in some
specialized namespace, so other code is elaborated by Lean as usual.
Field accesses that do not resolve to a specialized namespace are delegated
to Lean's builtin elaborators. A delaborator prints calls into specialized
namespaces as `recv.f args` when that elaborates back to the same function.

## Limitations

- Dot completion (`x.|`) does not list declarations of specialized
  namespaces; that needs a hook in Lean's completion.
- Not supported: `x.f.{u}`, overloaded heads (`x` resolving to several
  constants), receivers that are functions only via `CoeFun`, and
  hygienic (macro-generated) names in `P.(…)`.
- For specialized field names only: elaboration is postponed while the
  receiver type has metavariables (which may apply default instances
  earlier than Lean would), and specialized declarations shadow structure
  fields of the same name.
- Bare namespace names are produced by the pretty printer, so they may
  change between Lean versions. Refer to them as `(T).f`, not by name.
- There is no inline `def (T).f` form: Lean keeps the error-recovery
  messages of `def`/`theorem`/... parsers even when another parser wins,
  so it would always report a spurious parse error. Use `namespace (T) in`.

## Performance

Measured on this repository (Lean v4.30.0-rc2): importing this module into
every file costs about 2% of elaboration time. Declaring the 30 most common
field names of the repository in a specialized namespace, so that most
field accesses take the slow path and fall back to Lean, cost the same.

## Maintenance

This relies on Lean internals that may change between versions, so re-run
`NamespaceSpecialization/Test.lean` after toolchain upgrades:
- copies of the private `consumeImplicits` and `addLValArg` of
  `Lean.Elab.App` (they may drift from Lean's behaviour),
- the signature of `resolveName'` and the number of arguments of
  `Parser.Term.pipeProj` (gained an optional universe suffix),
- `Core.Context` fields being stored redundantly (`optionFlags` must be
  set with `Context.setOptions`),
- custom elaborators for `ident`/`app`/`proj` being tried before the
  builtin ones,
- the structure of `Scope` (the bare `namespace`/`end`) and of `cmd in cmd`.

A hook in Lean's `resolveLValAux` and dot completion would remove the
elaborator overrides; that is the route for upstreaming.
-/

namespace Etst.SpecializedNs
open Lean Meta Elab Term Command


def auxDecls (lctx: LocalContext): Std.TreeMap FVarId Name (Name.quickCmp ·.name ·.name) :=
  lctx.auxDeclToFullName

-- Cheap check whether `ns.field` might be declared.
def isDeclared (env: Environment) (lctx: LocalContext) (full: Name): Bool :=
  env.contains full || env.contains (mkPrivateName env full) ||
    (auxDecls lctx).any fun _ n => privateToUserName n == full

def isSpecField (env: Environment) (lctx: LocalContext) (field: String): Bool :=
  (getEntries env).any fun e => isDeclared env lctx (.str e.ns field)

def fieldString? (stx: Syntax): Option String :=
  match stx.getId.eraseMacroScopes with
  | .str .anonymous s => some s
  | _ => none

def isSpecFieldStx (stx: Syntax): TermElabM Bool := do
  let some s := fieldString? stx | return false
  return isSpecField (← getEnv) (← getLCtx) s


-- Resolves `ns.field` the way Lean's dot notation resolves `C.field`.
def resolveIn? (ns: Name) (field: String): TermElabM (Option Expr) := do
  let full := Name.str ns field
  -- Recursive references to the declaration being defined.
  for (fvarId, n) in auxDecls (← getLCtx) do
    if privateToUserName n == full then return some (mkFVar fvarId)
  let cands ←
    withTheReader Core.Context ({ · with currNamespace := .anonymous }) do
      resolveGlobalName full
  match cands.filter (·.2.isEmpty) |>.map (·.1) with
  | [] => return none
  | [n] => return some (← Term.mkConst n)
  | cands =>
    let cands := MessageData.joinSep (cands.map (m!"`{.ofConstName ·}`")) ", "
    throwError "Field name `{field}` is ambiguous: `{full}` has possible interpretations {cands}"

def resolveDirect? (c: Name) (field: String): TermElabM (Option Expr) := do
  let order ←
    if isStructure (← getEnv) c then getStructureResolutionOrder c else pure #[c]
  for s in order do
    if let some fn ← resolveIn? (privateToUserName s) field then return some fn
  return none

def unique?
  (cands: Array (Entry × Expr))
  (field: String)
:
  MetaM (Option (Entry × Expr))
:= do
  if cands.size ≤ 1 then return cands[0]?
  let names := cands.toList.map fun (e, _) => m!"`{.ofConstName (.str e.ns field)}`"
  throwError m!"Ambiguous field `{field}`: it is declared in several specialized \
    namespaces matching this type: {MessageData.joinSep names ", "}"

inductive Hit where
| spec (fn: Expr)
-- `C.field` for a head `C` of the unfolding chain that is not specialized.
| direct (fn: Expr)
| none

partial def lookup (type: Expr) (field: String): TermElabM Hit := do
  let entries := getEntries (← getEnv)
  let rec loop (t: Expr): TermElabM Hit := do
    let t ← whnfCore t
    let .const c _ := t.getAppFn | return .none
    let mut cands := #[]
    for e in entries do
      -- The same bare namespace may be registered by several modules.
      if e.head == c && !cands.any (·.1.ns == e.ns)
        && isDeclared (← getEnv) (← getLCtx) (.str e.ns field)
      then
        if ← e.matches t then
          if let some fn ← resolveIn? e.ns field then
            cands := cands.push (e, fn)
    if let some (_, fn) ← unique? cands field then
      return .spec fn
    unless entries.any (·.ns == c) do
      if let some fn ← resolveDirect? c field then return .direct fn
    match ← unfoldDefinition? t with
    | some t => loop t
    | none => return .none
  loop type

-- Whether a specialized namespace of a head in the unfolding chain of `type` declares `field`.
partial def mayBeSpec (type: Expr) (field: String): TermElabM Bool := do
  let t ← whnfCore type
  let .const c _ := t.getAppFn | return false
  let env ← getEnv
  let lctx ← getLCtx
  if (getEntries env).any fun e => e.head == c && isDeclared env lctx (.str e.ns field) then
    return true
  match ← unfoldDefinition? t with
  | some t => mayBeSpec t field
  | none => return false

-- Postpones while the type has metavariables, as they could change the result.
def lookupPostponing (type: Expr) (field: String): TermElabM Hit := do
  let type ← instantiateMVars type
  tryPostponeIfMVar type
  if type.getAppFn.isMVar then return .none
  if type.hasExprMVar && (← mayBeSpec type field) then
    tryPostpone
    synthesizeSyntheticMVarsUsingDefault
  lookup (← instantiateMVars type) field


-- Copy of the private `Lean.Elab.Term.consumeImplicits`.
partial def consumeImplicits
  (stx: Syntax)
  (e eType: Expr)
  (hasArgs: Bool)
:
  TermElabM (Expr × Expr)
:= do
  let eType ← whnfCore eType
  match eType with
  | .forallE _ d b bi =>
    if bi.isImplicit || (hasArgs && bi.isStrictImplicit) then
      let mvar ← mkFreshExprMVar d
      registerMVarErrorHoleInfo mvar.mvarId! stx
      consumeImplicits stx (mkApp e mvar) (b.instantiate1 mvar) hasArgs
    else if bi.isInstImplicit then
      let mvar ← mkInstMVar d
      let r := mkApp e mvar
      registerMVarErrorImplicitArgInfo mvar.mvarId! stx r
      consumeImplicits stx r (b.instantiate1 mvar) hasArgs
    else match d.getOptParamDefault? with
      | some defVal => consumeImplicits stx (mkApp e defVal) (b.instantiate1 defVal) hasArgs
      | _ => return (e, eType)
  | _ => return (e, eType)

/-
  Like the private `Lean.Elab.Term.addLValArg`: passes `recv` as the first
  parameter whose type has the same head as `recvType`, positionally if
  possible.
-/
def addReceiver
  (recv recvType fn: Expr)
  (args: Array Arg)
  (namedArgs: Array NamedArg)
  (explicit: Bool)
:
  TermElabM (Array Arg × Array NamedArg)
:= do
  let some head := (← whnfR recvType).getAppFn.constName? |
    throwError "Unexpected receiver type{indentExpr recvType}"
  let isRecvType (ty: Expr): MetaM Bool := do
    let ty := ty.cleanupAnnotations
    return ty.isAppOf head || (← whnfR ty).isAppOf head
  forallTelescopeReducing (← inferType fn) fun xs _ => do
    let mut argIdx := 0
    let mut remaining := namedArgs.map (·.name)
    let mut unusable := remaining
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if remaining.contains decl.userName then
        remaining := remaining.erase decl.userName
        continue
      let isExplicit := explicit || decl.binderInfo.isExplicit
      if ← isRecvType decl.type then
        if h: argIdx ≤ args.size then
          if isExplicit then
            return (args.insertIdx argIdx (.expr recv), namedArgs)
        if unusable.contains decl.userName then
          throwError "Invalid field notation: the parameter `{decl.userName}` of \
            `{fn}` cannot be referred to by name"
        return (args, namedArgs.push { name := decl.userName, val := .expr recv })
      if isExplicit then argIdx := argIdx + 1
      unusable := unusable.push decl.userName
    throwError "Invalid field notation: `{fn}` does not have a parameter of \
      type `{head} ...` for which to substitute{indentExpr recv}"

def elabFnArgs
  (fn: Expr)
  (recv?: Option (Expr × Expr))
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let (namedArgs, args, ellipsis) ← expandArgs args
  let (args, namedArgs) ← match recv? with
    | some (recv, recvType) => addReceiver recv recvType fn args namedArgs explicit
    | none => pure (args, namedArgs)
  elabAppArgs fn namedArgs args expectedType? explicit ellipsis

-- Like `exprToSyntax`, which would wrap `e` in implicit lambdas if its type starts with `∀ {x}`.
def embedExpr (e: Expr): TermElabM Term := withFreshMacroScope do
  let result ← `(?m)
  let mvar ← elabTerm result (← inferType e) (implicitLambda := false)
  mvar.mvarId!.assign e
  return result

-- Elaborates `‹e›.field args` using Lean's builtin elaborators.
def elabBuiltinStep
  (e: Expr)
  (field: Syntax)
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= withRef field do
  let eStx ← embedExpr e
  let proj ← `($(eStx).$(⟨field⟩):ident)
  let fn: Syntax :=
    if explicit then mkNode ``Parser.Term.explicit #[mkAtom "@", proj] else proj
  if !args.isEmpty then
    Term.elabApp (mkNode ``Parser.Term.app #[fn, mkNullNode args]) expectedType?
  else if explicit then
    Term.elabExplicit fn expectedType?
  else
    Term.elabProj fn expectedType?

def addFieldInfo (field: Syntax) (fn: Expr): TermElabM Expr :=
  addTermInfo (mkNode Parser.Term.identProjKind #[field]) fn

/-
  If `field` resolves to a specialized namespace for `f`, returns the
  receiver (with leading implicit arguments applied), its type and the
  resolved function.
-/
def trySpec?
  (f: Expr)
  (field: Syntax)
  (hasArgs: Bool)
:
  TermElabM (Option (Expr × Expr × Expr))
:= do
  let some name := fieldString? field | return none
  unless isSpecField (← getEnv) (← getLCtx) name do return none
  let saved ← saveState
  let (recv, recvType) ← consumeImplicits field f (← inferType f) hasArgs
  if let .spec fn ← lookupPostponing recvType name then
    return some (recv, recvType, fn)
  saved.restore
  return none

/-
  Elaborates `f.field₁.field₂... args`, where `args` belong to the last
  field.
-/
partial def elabChain
  (f: Expr)
  (fields: List Syntax)
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let field :: rest := fields | elabFnArgs f none args explicit expectedType?
  let last := rest.isEmpty
  let stepArgs := if last then args else #[]
  let stepExplicit := last && explicit
  let stepExpectedType? := if last then expectedType? else none
  let r ← match ← trySpec? f field (!args.isEmpty) with
    | some (recv, recvType, fn) =>
      addDotCompletionInfo field f expectedType?
      let fn ← addFieldInfo field fn
      elabFnArgs fn (some (recv, recvType)) stepArgs stepExplicit stepExpectedType?
    | none => elabBuiltinStep f field stepArgs stepExplicit stepExpectedType?
  if last then return r else elabChain r rest args explicit expectedType?

/-
  Instantiates the leading implicit parameters of `fn` so that the type of
  its first explicit parameter, or else its result type, is `type`, provided
  they have the same head.
-/
def instantiateFor (ref: Syntax) (fn type: Expr): TermElabM Expr := do
  let some head := (← whnfR type).getAppFn.constName? | return fn
  let (fn, fnType) ← consumeImplicits ref fn (← inferType fn) true
  -- The metavariables of the explicit parameters are discarded.
  let (xs, bis, result) ← forallMetaTelescopeReducing fnType
  let firstExplicit := (xs.zip bis).find? (·.2.isExplicit) |>.map (·.1)
  let targets ← firstExplicit.toList.mapM fun x => inferType x
  for target in targets ++ [result] do
    if (← whnfR target).isAppOf head then
      if ← isDefEq target type then break
  return fn

-- `(T).field₁.field₂... args`
def elabStatic
  (type: Expr)
  (fields: List Syntax)
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let field :: rest := fields | throwUnsupportedSyntax
  let some name := fieldString? field | throwUnsupportedSyntax
  let fn ← withRef field do
    match ← lookupPostponing type name with
    | .spec fn | .direct fn => addFieldInfo field fn
    | .none => throwError "Unknown field `{name}` of type{indentExpr type}"
  let fn ← if explicit then pure fn else instantiateFor field fn type
  if rest.isEmpty then
    elabFnArgs fn none args explicit expectedType?
  else
    elabChain (← elabFnArgs fn none #[] false none) rest args explicit expectedType?

def elabIdent
  (id: Syntax)
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let env ← getEnv
  let lctx ← getLCtx
  let comps := id.getId.eraseMacroScopes.components
  let isSpec (n: Name) := match n with
    | .str .anonymous s => isSpecField env lctx s
    | _ => false
  unless comps.drop 1 |>.any isSpec do throwUnsupportedSyntax
  let cands ←
    try pure (← resolveName' id [] expectedType?).2
    catch _ => throwUnsupportedSyntax
  let [(f, fIdent, fields, _)] := cands | throwUnsupportedSyntax
  unless ← fields.anyM isSpecFieldStx do throwUnsupportedSyntax
  checkDeprecated fIdent f
  let f ← addTermInfo fIdent f expectedType?
  elabChain f fields args explicit expectedType?

/-
  `P.(h args)`. If `P` is an identifier, it qualifies the head `h`, so
  `Foo.(Bar Nat)` is `Foo.Bar Nat`. Otherwise, `P` is a type, and `h` is
  looked up in its namespaces, so `Foo.(Bar Nat).(Baz X)` is
  `(Foo.Bar Nat).Baz X`.
-/
syntax:max (name := nsPath) term:max noWs ".(" term ")" : term

def isNsPath (stx: Syntax): Bool := stx.isOfKind ``nsPath

def elabProjLike
  (base field: Syntax)
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let fields := field.identComponents
  if isNsPath base then
    return ← elabStatic (← elabType base) fields args explicit expectedType?
  unless ← fields.anyM isSpecFieldStx do throwUnsupportedSyntax
  let b ← elabTerm base none
  if (← whnfR (← inferType b)).isSort then
    elabStatic b fields args explicit expectedType?
  else
    elabChain b fields args explicit expectedType?

partial def lookupResultType (t: Expr) (field: String): TermElabM Hit := do
  let t ← whnfCore (← instantiateMVars t)
  if t.isForall then
    forallTelescope t fun _ b => lookupResultType b field
  else
    lookupPostponing t field

def elabDotIdent
  (id: Syntax)
  (args: Array Syntax)
  (explicit: Bool)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let some name := fieldString? id | throwUnsupportedSyntax
  unless isSpecField (← getEnv) (← getLCtx) name do throwUnsupportedSyntax
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType := expectedType? | throwUnsupportedSyntax
  let .spec fn ← lookupResultType expectedType name | throwUnsupportedSyntax
  let fn ← addTermInfo id fn (force := true)
  elabFnArgs fn none args explicit expectedType?

def annotateIfRec (stx: Syntax) (e: Expr): TermElabM Expr := do
  if (← read).saveRecAppSyntax then
    if let .fvar fvarId := e.getAppFn then
      if (← fvarId.getDecl).isAuxDecl then
        return mkRecAppWithSyntax e stx
  return e

def elabApp
  (stx fn: Syntax)
  (args: Array Syntax)
  (expectedType?: Option Expr)
:
  TermElabM Expr
:= do
  let (fn, explicit) :=
    if fn.isOfKind ``Parser.Term.explicit then (fn[1], true) else (fn, false)
  let onNsPath := fn.isOfKind ``Parser.Term.proj && isNsPath fn[0]
  if !onNsPath && (getEntries (← getEnv)).isEmpty then throwUnsupportedSyntax
  let e ← match fn with
    | `($id:ident) => elabIdent id args explicit expectedType?
    | `($(base).$field:ident) => elabProjLike base field args explicit expectedType?
    | `(.$id:ident) => elabDotIdent id args explicit expectedType?
    | _ => throwUnsupportedSyntax
  annotateIfRec stx e

@[term_elab app] def elabAppSpec: TermElab := fun stx expectedType? =>
  universeConstraintsCheckpoint do
    elabApp stx stx[0] stx[1].getArgs expectedType?

@[term_elab ident] def elabIdentSpec: TermElab := fun stx expectedType? =>
  elabApp stx stx #[] expectedType?

@[term_elab proj] def elabProjSpec: TermElab := fun stx expectedType? =>
  elabApp stx stx #[] expectedType?

@[term_elab dotIdent] def elabDotIdentSpec: TermElab := fun stx expectedType? =>
  elabApp stx stx #[] expectedType?

@[term_elab explicit] def elabExplicitSpec: TermElab := fun stx expectedType? =>
  elabApp stx stx #[] expectedType?

@[term_elab pipeProj] def elabPipeProjSpec: TermElab := fun stx expectedType? => do
  if !isNsPath stx[0] && (getEntries (← getEnv)).isEmpty then throwUnsupportedSyntax
  match stx with
  | `($base |>.$field:ident $args*) =>
    universeConstraintsCheckpoint do
      elabProjLike base field args false expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab nsPath] def elabNsPath: TermElab := fun stx expectedType? => do
  let (lhs, t) := (stx[0], stx[2])
  let (head, args) ←
    if t.isIdent then pure (t, #[])
    else if t.isOfKind ``Parser.Term.app && t[0].isIdent then pure (t[0], t[1].getArgs)
    else throwErrorAt t "Expected a term of the form `C args`, where `C` is an identifier"
  if lhs.isIdent then
    let head := mkIdentFrom head (lhs.getId ++ head.getId) (canonical := true)
    let t: Syntax :=
      if args.isEmpty then head else mkNode ``Parser.Term.app #[head, mkNullNode args]
    elabTerm t expectedType?
  else
    elabStatic (← elabType lhs) head.identComponents args false expectedType?


section Delab
open PrettyPrinter Delaborator SubExpr

/-
  The index of the receiver among the first `numArgs` parameters of `fnType`,
  and its position among the explicit ones. Same rule as `addReceiver`.
-/
def receiverIndex?
  (entry: Entry)
  (fnType: Expr)
  (numArgs: Nat)
:
  MetaM (Option (Nat × Nat))
:=
  forallTelescopeReducing fnType fun xs _ => do
    let mut pos := 0
    for h: i in [0:xs.size] do
      if numArgs ≤ i then return none
      let decl ← xs[i].fvarId!.getDecl
      if decl.binderInfo.isExplicit then
        let ty := decl.type.cleanupAnnotations
        if ty.isAppOf entry.ns || (← whnfR ty).isAppOf entry.head then
          return some (i, pos)
        pos := pos + 1
    return none

/-
  Prints `recv.f args` for functions of specialized namespaces, provided it
  elaborates back to the same function.
-/
@[delab app] def delabSpecApp: Delab :=
  whenPPOption getPPFieldNotation <| whenPPOption getPPFieldNotationGeneralized do
    let e ← getExpr
    let .const c _ := e.getAppFn | failure
    let .str ns field := c | failure
    let some entry := (getEntries (← getEnv)).find? (·.ns == ns) | failure
    let args := e.getAppArgs
    let some (idx, pos) ← receiverIndex? entry (← inferType e.getAppFn) args.size | failure
    let roundtrips ← try
        match ← (lookup (← inferType args[idx]!) field).run' with
        | .spec fn => pure (fn.isConstOf c)
        | _ => pure false
      catch _ => pure false
    unless roundtrips do failure
    let stx ← delabApp
    let isPositional (arg: Syntax) :=
      !arg.isOfKind ``Parser.Term.namedArgument && !arg.isOfKind ``Parser.Term.ellipsis
    let fn := stx.raw[0]
    let stxArgs := stx.raw[1].getArgs
    unless stx.raw.isOfKind ``Parser.Term.app && fn.isIdent
      && pos < stxArgs.size && stxArgs.all isPositional
    do return stx
    let fieldStx := mkIdentFrom fn (.mkSimple field)
    let proj ← `($(⟨stxArgs[pos]!⟩).$fieldStx:ident)
    let rest := stxArgs.eraseIdx! pos
    if rest.isEmpty then return proj
    return ⟨mkNode ``Parser.Term.app #[proj, mkNullNode rest]⟩

end Delab


/-
  Binders of a bare specialized namespace. A binder must be followed by
  another binder or the namespace, so that `(T)` is not parsed as a binder.
-/
syntax specBinders :=
  (atomic(bracketedBinder lookahead("(" <|> "{" <|> "[" <|> "⦃" <|> ident)))*

-- `(T)` or `P.(T)`, optionally followed by `.(U)`s.
syntax nsTarget := lookahead((ident noWs ".(") <|> "(") term:max

/--
  Opens the specialized namespace of the type pattern `T`. Dot notation on
  any value whose type is an instance of `T` looks into it. The binders
  become section variables.
  
  ```
  namespace {sig} (Expr sig Unit)
    def intp ... := ...
  end (Expr sig Unit)
  ```
  
  The namespace is a real namespace named `C.«(T)»`, where `C` is the head
  of `T`, so the names of `C` are visible inside it.
-/
syntax (name := nsCmd) "namespace " specBinders nsTarget : command

/-- Closes a namespace opened by `namespace (T)`. -/
syntax (name := endCmd) "end " nsTarget : command

/--
  Opens an existing bare specialized namespace, like `open` does for
  ordinary namespaces.
  
  ```
  open {sig} (Expr sig Unit)
  open Foo.(Bar Nat) in ...
  ```
-/
syntax (name := openCmd) "open " specBinders nsTarget : command

def mkBareNsName (head: Name) (seg: String) (entries: Array Entry): Name := Id.run do
  let mut name := Name.str head seg
  let mut i := 2
  while entries.any (·.ns == name) do
    name := Name.str head s!"{seg}_{i}"
    i := i + 1
  return name

def subscript (n: Nat): String :=
  (toString n).map fun c => Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)

/-
  The name segment of a bare namespace, independent of parameter names and
  the context, so that modules that do not import each other agree on it.
-/
def canonicalSegment (entry: Entry): MetaM String :=
  lambdaTelescope entry.pattern fun _ body => do
    let params := (collectFVars {} body).fvarIds
    let mut lctx ← getLCtx
    for h: i in [0:params.size] do
      lctx := lctx.setUserName params[i] (.mkSimple s!"x{subscript (i + 1)}")
    let fmt ←
      withLCtx lctx (← getLocalInstances) do
      withTheReader Core.Context (fun ctx => { (ctx.setOptions {}) with
        currNamespace := entry.head.getPrefix, openDecls := [] }) do
        ppExpr body
    return s!"({fmt.pretty 10000})"

/-
  The bare namespace of `typeStx` (with the binders in scope), and whether
  it already exists. Parameter names are irrelevant, as existing namespaces
  are found up to equivalence of patterns.
-/
def elabBareEntry (typeStx: Syntax): TermElabM (Entry × Bool) := do
  let type ← Term.elabType typeStx
  Term.synthesizeSyntheticMVarsNoPostponing
  let xs := (← getLCtx).getFVars
  let entry ← mkEntry .anonymous xs type true
  let entries := getEntries (← getEnv)
  for e in entries do
    if e.bare && e.head == entry.head then
      if ← entry.equiv e then return (e, true)
  let seg ← canonicalSegment entry
  return ({ entry with ns := mkBareNsName entry.head seg entries }, false)

def targetType (stx: Syntax): Syntax := stx[0]

@[command_elab nsCmd] def elabNamespace: CommandElab := fun stx => do
  let binders := stx[1][0].getArgs
  let (entry, exists_) ← runTermElabM fun _ =>
    Term.elabBinders binders fun _ => elabBareEntry (targetType stx[2])
  unless exists_ do
    modifyEnv (ext.addEntry · entry)
  modify fun s => { s with
    env := s.env.registerNamespace entry.ns
    scopes :=
      { s.scopes.head! with header := entry.ns.getString!, currNamespace := entry.ns }
        :: s.scopes
  }
  pushScope
  for p in entry.ns.components.foldl (fun acc c => acc.push (acc.back?.getD .anonymous ++ c)) #[] do
    activateScoped p
  unless binders.isEmpty do
    elabCommand (← `(variable $(binders.map (⟨·⟩))*))

@[command_elab endCmd] def elabEnd: CommandElab := fun stx => do
  let scope ← getScope
  let some entry := (getEntries (← getEnv)).find? fun e =>
      e.bare && e.ns == scope.currNamespace && e.ns.getString! == scope.header
    | throwError "Invalid `end (…)`: the current scope is not a specialized namespace"
  let (found, _) ← runTermElabM fun _ => elabBareEntry (targetType stx[1])
  unless found.ns == entry.ns do
    throwErrorAt stx[1] "Invalid `end (…)`: expected the current namespace `{entry.ns.getString!}`"
  modify fun s => { s with scopes := s.scopes.drop 1 }
  popScope

@[command_elab openCmd] def elabOpen: CommandElab := fun stx => do
  let binders := stx[1][0].getArgs
  let (entry, exists_) ← runTermElabM fun _ =>
    Term.elabBinders binders fun _ => elabBareEntry (targetType stx[2])
  unless exists_ do
    throwErrorAt stx[2] "Unknown specialized namespace `{entry.ns.getString!}`"
  elabCommand (← `(open $(mkIdent entry.ns):ident))

@[macro Lean.Parser.Command.in] def expandIn: Macro := fun stx => do
  unless stx[0].isOfKind ``nsCmd do Macro.throwUnsupported
  return mkNullNode #[stx[0], stx[2], mkNode ``endCmd #[mkAtom "end", stx[0][2]]]

end Etst.SpecializedNs
