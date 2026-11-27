module
public import Etst.WFC.Utils.Trisets.TrisetFn.TrisetFn
public import Etst.WFC.Utils.Trisets.TrisetFn.Ops.ImplicitConversion

public section
namespace Etst

/-
The goal of this file is to define

- a basic set of operations (`TrisetFnExpr`)
- with an interpretation function on them `TrisetFnExpr.intp`
- and a `DefList` analogue for `TrisetFn` expressions, with semantics.

However, I am not thrilled about how much work it appears to require.
Would be great if there was a simpler approach. I want to commit
a snapshot before taking a turn though (need to fix `toBasicExprOp`),
and hopefully reduce the amount of (near-)duplication.

Here's my reasoning for my current choices:
- **The semantics of a deflist / what a `const` expression reads.**
  A list of TrisetFn codes. The most straightforward option. Using
  encoding families (see below) would add unnecessary data.
- **Why use encoding families** (ie. indices representing
  `List Pair → TrisetFn`). A naive approach might try to define an
  `intp: TrisetExpr → (consts fv: List TrisetFnCode) → TrisetFnCode`,
  but then defining the `arbUn` branch hits a problem -- we can define
  ```
    let domainIntp := intp domain consts fv
    let bodyIntp: Set TrisetFnCode := {
      c |
      ∃ cD ∈ domainIntp, intp body consts (cD :: fv)
    }
  ```
  but we cannot turn `bodyIntp` into a `TrisetFn` code representing it.
  Encoding families are a solution to this problem -- instead of
  computing bare codes, compute functions from free variables to codes.
  Arbitrary unions then become WFC-definable from those functions.
- **WTF is toBasicExprOp and toBasicExprOpDl?** A poor attempt at defining
  the code of `TrisetFnExpr.univ`. However, I believe something like it
  in spirit is both possible and necessary :/
- **preIntpFam** An interpretation function working on encoding families.
  Probably a necessary middle-step, see above.
- **preIntp** An interpretation function working on `TrisetFn` codes.
  Will probably need to reference `preIntpFam` somehow, see "Why encoding
  families".
- **intp** A **preIntp** version lifted to `TrisetFn`.
- **toBasicExpr** an expression version of the interpretation functions
  necessary (???) for the definition of deflist semantics. (Or maybe
  the `TrisetFnExpr.univ` construction can be reused, TODO explore.)

Other notes:
- Since I have not tried implementing at least one branch of each of
  these functions, I am not really sure if there are hidden obstacles
  that would break this approach.
- I am also not sure whether some of the obstacles I see cannot be worked
  around in a better way. This really is just a best-effort snapshot.
-/

exposed def NamedPairExpr.encoding {varsIn varsOut}
  (expr: NamedPairExpr .basic varsIn)
  (consts: List String)
  (_isWf: expr.IsWF consts := by decide)
:
  NamedPairExpr .basic varsOut
:=
  (expr.compile consts).encoding.toNamedExpr

exposed def NamedPairExpr.rawEncoding {vars}
  (expr: NamedPairExpr .basic vars)
  (consts: List String)
  (_isWf: expr.IsWF consts := by decide)
:
  Expr .basic
:=
  (expr.compile consts).encoding.toExpr

exposed def NamedPairExpr.wfEncoding {varsIn varsOut constsOut}
  (expr: NamedPairExpr .basic varsIn)
  (constsIn: List String)
  (_isWf: expr.IsWF constsIn := by decide)
:
  WfNamedPairExpr .basic varsOut constsOut
:=
  (expr.compile constsIn).encoding.toWfNamedExpr


-- Given a list of pairs, returns an index of the list of those pairs.
exposed def uniSetMapIndex.packList
  (list: List Pair)
:
  Pair
:=
  .pair .null <|
  .pair (Pair.listEncoding list) <|
  Expr.encoding <|
  list.foldrIdx
    (fun i _ acc => .prod (.var i) acc)
    .null

-- The argument is expected to evaluate to a singleton triset.
exposed def uniSetMapIndex.singletonExpr
  (expr: Expr .basic)
:
  Expr .basic
:=
  .prod .null <|
  .prod (.prod expr .null) <|
  (Expr.var 0).encoding.toExpr


/-
  Defines a set of operations on TrisetFn. It can be understood as
  syntactic sugar over WFC, see `toBasicExpr`, `preIntpFam` and `preIntp`.
  `TrisetFn.intp` is the one working on the TrisetFn level.
  
  TODO notes:
  - `arbIr domain body` should contain those codes that
    - are in `body` exactly for some element of `domain`
    - are in `body` up to bisimilarity for all other elements of `domain`
    - this mirrors the binary `ir`
    - this means arbIr with an empty domain ought to be empty.
  - the domain of all `fn` values is all pairs (or all valid codes if need be)
  - `app f arg` uses fuzzy match on inputs if `f` is a set.
  - `univ` must only contain valid (saturated, bisimilarity preserving
    codes. The hope is that the fixed point of `toBasicExprOp` only
    contains those.)
-/
inductive TrisetFnExpr
| const (x: Nat)
| var (x: Nat)
| empty
| univ
| singleton (elem: TrisetFnExpr)
| ite (set elem pos neg: TrisetFnExpr)
| un (left rite: TrisetFnExpr)
| arbIr (domain: TrisetFnExpr) (body: TrisetFnExpr)
| arbUn (domain: TrisetFnExpr) (body: TrisetFnExpr)
| fn (body: TrisetFnExpr)
| app (f arg: TrisetFnExpr)

namespace TrisetFnExpr
  
  -- `fs` constructs a *finite set* from a list of elements.
  exposed def fs: List TrisetFnExpr → TrisetFnExpr
  | [] => empty
  | elem :: [] => singleton elem
  | elem :: rest => un (singleton elem) (fs rest)
  
  exposed def ifThen (set elem res: TrisetFnExpr): TrisetFnExpr :=
    ite set elem res empty
  
  exposed def ifElse (set elem res: TrisetFnExpr): TrisetFnExpr :=
    ite set elem empty res
  
  exposed def ifNonempty (set res: TrisetFnExpr): TrisetFnExpr :=
    ifThen (set.arbUn .univ) empty res
  
  exposed def ir (left rite: TrisetFnExpr): TrisetFnExpr :=
    un
      (left.arbUn (rite.ifThen (var 0) (var 0)))
      (rite.arbUn (left.ifThen (var 0) (var 0)))
  
  exposed def diff (left rite: TrisetFnExpr): TrisetFnExpr :=
    left.arbUn (rite.ifElse (var 0) (var 0))
  
  exposed def flatten (expr: TrisetFnExpr): TrisetFnExpr :=
    arbUn expr (var 0)
  
  /-
    A pair value `(a, b)` is encoded as the set
    
    ```
      {
        {{}, {a}},
        {{{}}, {{b}}}
      }
    ```
    
    The Kuratowski definition of a pair is not well-behaved for
    non-classical trisets.
  -/
  exposed def pair (left rite: TrisetFnExpr): TrisetFnExpr :=
    fs [
      fs [empty, singleton left],
      fs [singleton empty, singleton (singleton rite)]
    ]
  
  exposed def zth (pair: TrisetFnExpr): TrisetFnExpr :=
    -- For each element E of the pair encoding, if it contains the
    -- empty set, then return the union of E.
    pair.arbUn (ifThen (var 0) empty (flatten (var 0)))
  
  exposed def fst (pair: TrisetFnExpr): TrisetFnExpr :=
    -- For each element E of the pair encoding, if it contains `{{}}`,
    -- then return the union of the union of E.
    pair.arbUn <|
    ifThen (var 0) (fs [ empty ]) (flatten (flatten (var 0)))
  
end TrisetFnExpr


namespace TrisetFn
  /-
    ## Section: code families
    
    TODO move to own files.
    
    A code family is a `uniSetMap` index that represents a function
    (callable with `Expr/Set3.call`) from lists of free variables to
    `TrisetFn` codes.
  -/
  
  /-
    `consts` is expected to be a `uniSetMap` index of a list of `TrisetFn`
    codes (not code families).
  -/
  exposed def constCodeFam (consts x: Pair): Pair :=
    let expr :=
      p3(consts, x; Ex fv, fv × getNth (uniSetMap consts) x)
    uniSetMapIndex
      opFixHelpersDl.dl.toDefList
      opFixHelpersDl.dl.size
      [x, consts]
      (expr.compile uniSetMapDl.consts)
  
  exposed def constCodeFamExpr
    (dlEnc consts x: Expr .basic)
  :
    Expr .basic
  :=
    .prod dlEnc <|
    .prod (.prod x (.prod consts .null)) <|
    let expr := p3(consts, x;
      Ex fv,
      × fv
      × getNth (uniSetMap consts) x
    )
    expr.rawEncoding uniSetMapDl.consts
  
  exposed def varCodeFamExpr (dlEnc x: Expr .basic): Expr .basic :=
    .prod dlEnc <|
    .prod (.prod x .null) <|
    p3(x; Ex fv, fv × getNth fv x).rawEncoding uniSetMapDl.consts
  
  exposed def varCodeFam (x: Pair): Pair :=
    uniSetMapIndex
      opFixHelpersDl.dl.toDefList
      opFixHelpersDl.dl.size
      [x]
      (p3(x; Ex fv, fv × getNth fv x).compile uniSetMapDl.consts)
  
  exposed def emptyCodeFam: Pair :=
    uniSetMapIndex
      FiniteDefList.empty.toDefList
      FiniteDefList.empty.size
      [uniSetMapIndex.emptyIndex]
      (.prod .any (.prod (.nat 0) (.var 0)))
  
  exposed def emptyCodeFamExpr: Expr .basic :=
    emptyCodeFam.toExpr
  
  exposed def singletonCodeFamExpr
    (dlEnc body: Expr .basic)
  :
    Expr .basic
  :=
    .prod dlEnc <|
    .prod (.prod body .null) <|
    let expr := p3(body;
      Ex fv,
      × fv
      × 0 -- the tag of sets (not functions).
      × null
      × (uniSetMap body fv × null)
      × 2 × 0 -- encodes `Expr.var 0`.
    )
    expr.rawEncoding uniSetMapDl.consts
  
  def arbUnCodeFamExpr
    (dlEnc domain body: Expr .basic)
  :
    Expr .basic
  :=
    .prod dlEnc <|
    .prod (.prod body (.prod domain .null)) <|
    let expr := p3(domain, body;
      Ex fv,
      × fv
      × 0
      × ofhDlEnc
      × (fv × body × domain × null)
      -- don't forget to implicitly convert functions to sets as in
      -- `ImplicitConversion.lean`.
      × null -- TODO
    )
    expr.rawEncoding opFixDl.consts
  
  /-
    Given an index of a code family, returns an index of the
    code at `fv`. Expects the `uniSetMap` const to be available.
  -/
  def codeFamAt
    (codeFamExpr fv: Expr .basic)
  :
    Expr .basic
  :=
    uniSetMapIndex.singletonExpr
      ((Expr.uniSetMapConst.call codeFamExpr).call fv)
  
end TrisetFn


-- TODO prove the fixed point only contains valid codes.
-- (Semantic uniqueness would also be nice if it holds, I guess.
-- only as a follow-up.)
open TrisetFn in
def TrisetFnExpr.toBasicExprOp := p3(
  ofhDlEnc;
  Ex self,
  × self
  × (
    -- const
    | Ex x,
      × (0 × x)
      -- var 2 = ofhDlEnc, var 1 = self, var 0 = x
      -- TODO bug: we're passing self to consts, we should be
      -- passing lists of codes instead.
      × <[.raw <| constCodeFamExpr (.var 2) (.var 1) (.var 0)]>
    -- var
    | Ex x, (1 × x) × <[.raw <| varCodeFamExpr (.var 2) (.var 0)]>
    -- empty
    | (2 × null) × <[ emptyCodeFam.toNamedExpr ]>
    -- univ
    | × (3 × null)
      × ofhDlEnc
      × (self × null)
      × <[
        let expr := p3(self;
          Ex fv expr,
          × fv
          × 0
          × null
            -- Call `self` with `expr`, dereference, and call with an
            -- empty fv list. `2 × 0` encodes `Expr.var 0`.
          × (uniSetMap (uniSetMap self expr) null × null)
          × 2 × 0
        )
        expr.encoding uniSetMapDl.consts
      ]>
    -- singleton
    | Ex body,
      × (4 × body)
      × <[ .raw <| singletonCodeFamExpr (.var 2) (.var 0) ]>
    --ite
    | Ex set elem pos neg,
      × (5 × set × elem × pos × neg)
      × TODO
    -- un
    | Ex left rite,
      × (6 × left × rite)
      × TODO
    -- arbIr
    | Ex domain body,
      × (7 × domain × body)
      × TODO
    -- arbUn
    | Ex domain body,
      × (8 × domain × body)
      × <[ .raw <| arbUnCodeFamExpr (.var 3) (.var 1) (.var 0) ]>
    -- fn
    | Ex body,
      × (9 × body)
      × TODO
    -- app
    | Ex body,
      × (10 × body)
      × TODO
  )
)

pairDefList TrisetFnExpr.toBasicExprDl extends opFixDl
  -- Signature, up to encoding (`[T]` means "index of T"):
  -- `TrisetFnExpr → [(fv: List Pair) → TrisetFn]`
  p3 toBasicExpr := indexFix (
    × null
    × (ofhDlEnc × null)
    × <[toBasicExprOp.wfEncoding (uniSetMapDl.consts ++ ["TODO"])]>
  )

pairDefList.


/-
  Compiles a `TrisetFnExpr` to an expression that represents the
  corresponding code family.
  
  Used by `TODO_name` to compile `TrisetFn` definition lists into
  `DefList`.
-/
open TrisetFn in
exposed def TrisetFnExpr.toBasicExpr
  (consts: Expr .basic)
:
  TrisetFnExpr → Expr .basic
| .const x => constCodeFamExpr opFixDl.ofhDlEncConst consts (.nat x)
| .var x => varCodeFamExpr opFixDl.ofhDlEncConst (.nat x)
| .empty => emptyCodeFamExpr
| .univ =>
  -- TODO is this correct?
  ((toBasicExprDl.constExpr () "toBasicExpr").call
    (.prod (.nat 3) .null))
| .singleton elem =>
  singletonCodeFamExpr
    opFixDl.ofhDlEncConst
    (elem.toBasicExpr consts)
| .ite set elem pos neg => sorry
| .un left rite => sorry
| .arbIr domain body => sorry
| .arbUn domain body => sorry
| .fn body => sorry
| .app f arg => sorry

/-
  Interpretation of TrisetFn expressions on the level of TrisetFn codes.
  Returns a code family rather than a bare code in order to make
  quantifiers definable (we cannot turn an arbitrary set of bare codes
  into a `uniSetMap` index of their union, unless that set itself is
  WFC-definable).
  
  TODO perhaps merge `preIntpFam` and `preIntp` into one function
  that returns a struct?
-/
exposed def TrisetFnExpr.preIntpFam
  (expr: TrisetFnExpr)
  (consts: List Pair.PreTrisetFn)
:
  Pair
:=
  sorry

exposed def TrisetFnExpr.preIntp
  (expr: TrisetFnExpr)
  (consts: List Pair.PreTrisetFn)
  (fv: List Pair.PreTrisetFn)
:
  Pair.PreTrisetFn
:=
  sorry

-- Interpretation of TrisetFn expressions. A lift of `preIntp`.
exposed def TrisetFnExpr.intp
  (expr: TrisetFnExpr)
  (consts: List Pair.TrisetFn)
  (fv: List Pair.TrisetFn)
:
  Pair.TrisetFn
:=
  sorry


exposed def TrisetFnExpr.packCodes
  (list: List Pair.PreTrisetFn)
:
  Pair
:=
  uniSetMapIndex.packList (list.map Pair.PreTrisetFn.toPair)

open uniSetMapIndex in
theorem TrisetFnExpr.toBasicExpr_eq_preIntpFam {lane b c fv}
  (expr: TrisetFnExpr)
  (consts: List Pair.PreTrisetFn)
:
  Eq
    (Expr.intp
      (expr.toBasicExpr (packCodes consts).toExpr)
      lane
      b
      c
      fv)
    {expr.preIntpFam consts}
:=
  match expr with
  | .const x => sorry
  | .var x => sorry
  | .empty => sorry
  | .univ => sorry
  | .singleton elem => sorry
  | .ite set elem pos neg => sorry
  | .un left rite => sorry
  | .arbIr domain body => sorry
  | .arbUn domain body => sorry
  | .fn body => sorry
  | .app f arg => sorry

open uniSetMapIndex in
theorem TrisetFnExpr.preIntpFam_eq_preIntp {lane}
  (expr: TrisetFnExpr)
  (consts: List Pair.PreTrisetFn)
  (fv: List Pair.PreTrisetFn)
:
  Eq
    (Set3.getLane
      ((uniSetMap.call (expr.preIntpFam consts)).call (packCodes fv))
      lane)
    {(expr.preIntp consts fv).toPair}
:=
  match expr with
  | .const x => sorry
  | .var x => sorry
  | .empty => sorry
  | .univ => sorry
  | .singleton elem => sorry
  | .ite set elem pos neg => sorry
  | .un left rite => sorry
  | .arbIr domain body => sorry
  | .arbUn domain body => sorry
  | .fn body => sorry
  | .app f arg => sorry


structure TrisetFnDefList where
  defs: List TrisetFnExpr

namespace TrisetFnDefList
  exposed def size (dl: TrisetFnDefList) := dl.defs.length
  
  /-
    An expression representing an operator on `uniSetMap` indices.
    The index encodes a list of TrisetFn codes.
  -/
  exposed def opExpr (dl: TrisetFnDefList) := p3(
    Ex iOp,
    × iOp
    × <[ opFixDl.ofhDlEnc.toNamedExpr ]>
    × (iOp × null)
    × <[
      let expr: Expr .basic :=
        dl.defs.foldr
          (fun expr acc =>
            .prod
              (TrisetFn.codeFamAt (expr.toBasicExpr (.var 0)) .null)
              acc)
          .null
      expr.encoding.toNamedExpr
    ]>
  )
  
  exposed def op (dl: TrisetFnDefList): Pair :=
    ((opExpr dl).compile []).encoding
  
  exposed def wfm (dl: TrisetFnDefList): Pair :=
    indexFixIndex (op dl)
  
  exposed def wfmAt
    (dl: TrisetFnDefList)
    (x: Nat)
  :
    Pair.TrisetFn
  :=
    -- TODO from `uniSetMap dl.wfm`, extract the x-th index.
    -- Will require showing existence and uniqueness, looks like.
    sorry
  
end TrisetFnDefList

/-
  TODO proofs of correctness:
  - All the code families are actual functions, ie. one output
    for each input.
  - All the operations respect bisimilarity, are liftable from encodings
    to TrisetFn operations.
  - All definable TrisetFn encodings are saturated - ie. operations
    on their corresponding TrisetFn instances are WFC-computable on
    the encodings. (is this a sub-requirement of the previous one?)
  
  Though I guess most or all of this will be forced when implementing
  `TrisetFn.impl`.
-/


/-
For reference, I'm also attaching an older approach here:
-//-
module
public import Etst.WFC.Utils.Trisets.TrisetMembership
public import Etst.WFC.Utils.Trisets.TrisetFn.TrisetFn
import Mathlib.Data.List.Basic

public section
namespace Etst

/-
  TODO: this is an earlier, unfinished, and buggy implementation and I
  changed my approach, continuing in TrisetFnExpr. This file can serve
  as (an unreliable) documentation of intent, but needs to be rewritten
  (probably to just import the main results from the utility files, once
  they are complete).
  
  # Chapter 8: Trisets of Trisets of Trisets...
  
  Up until now, we have been working with trisets *of* some domain D.
  In this chapter, we introduce trisets as a data type that contains
  other trisets as elements.
  
  (We may refer to "trisets of pairs" as TfP, or just trisets.)
  
  ## Trisets
  As Chapter 6 shows, within WFC one can represent any definable triset
  of pairs using a single pair. This allows us to interpret trisets of
  pairs as being "trisets of trisets of pairs", or recursively even deeper,
  as pure trisets of trisets of trisets, and so on.
  
  Working with codes directly is a hassle. So we want to go one step
  further, and abstract the codes away.
  
  Concretely:
  - We have a WFC-definable `uniSetMap: Set3 Pair` such that any definable
    TfP equals `uniSetMap.call i` for some index `i: Pair`.
  - For two pairs `p q: Pair`, we define
        p ∈def q ↔ p ∈ (uniSetMap.call q).defMem
        p ∈pos q ↔ p ∈ (uniSetMap.call q).posMem
  - Then we quotient the set of pairs by bisimilarity wrt. this membership
    relation. A triset is an element of this quotient, ie. an equivalence
    class of pairs.
  
  Quotienting by bisimilarity guarantees that our trisets are extensional.
  
  ## Functions
  Pure trisets as defined above have one drawback: they cannot define
  functions that would take a triset T as an argument, and return a triset
  defined in terms of that exact T. (Excercise: try defining the identity
  function. It must satisfy `id X = X` for X being the empty set, and the
  the undetermined set. And WFC guarantees that the empty set responds
  "maybe" to the question "Are you the undetermined set?".)
  
  > Aside: Functions and functions application are definable using pure
  trisets as long as their domains are classical. Which means one can
  choose a large enough classical triset to be their universe of discourse
  and work with functions inside it. The disadvantage is that this requires
  defining any function of interest once per each universe one wishes to
  apply it in.
  
  To overcome this limitation, we accept a compromise: we define a data
  type `TrisetFn`, whose values are either trisets, or functions from
  values to values. On the level of pairs (codes), we have either
  - (0, c) representing the triset `uniSetMap.call c`
  - (1, c) a function whose graph is given by `uniSetMap.call c`.
  See the file `TrisetFn.lean` for more details.
  
  We also define operations on `TrisetFn` (such as union, function
  application, and so on), as syntax sugars for operations on pairs
  (guaranteeing they are WFC-definable), and prove that they respect
  the structure of `TrisetFn`.
  
  
  
  
  
  
  
  
  
  Note: the chapter itself was originally written with the expectation
  we'd have trisets only, and most of the file still reflects that.
  ## Original description (to be deleted)
  
  Up until now, we have been working with trisets *of* some domain D.
  Here we work with trisets -- objects that contain other
  trisets as elements. (We may refer to "trisets of pairs" as TfP, or just
  trisets.)
  
  A triset is, most abstractly, a data structure with a three-valued
  membership relation. Our particular implementation of trisets is as
  follows:
  - Recall that we have `uniSetMap` from Chapter 6 -- a WFC-definable
    enumeration of WFC-definable trisets of pairs. Concretely, any
    definable TfP equals `uniSetMap.call i` for some index `i: Pair`.
  - For two pairs `p q: Pair`, we may define
        p ∈def q ↔ p ∈ (uniSetMap.call q).defMem
        p ∈pos q ↔ p ∈ (uniSetMap.call q).posMem
  - Then we quotient the set of pairs by bisimilarity wrt. this
    membership relation. A triset is an element of this quotient, ie.
    an equivalence class of pairs.
  
  In this chapter, we define operations for trisets (such as union,
  taking the singleton, etc.) as syntax sugars for operations on
  pairs (guaranteeing they are WFC-definable), and prove that they
  respect the triset structure.
-/


-- ## Section: Preliminaries

/-
  Turns a list of `uniSetMap` indices into the lossless product
  of their trisets.
-/
def uniSetMapIndex.packListExpr {T}
  (exprSrcs: List T)
  (toExpr: T → BasicExpr)
:
  BasicExpr
:=
  exprSrcs.foldr
    (fun elem acc =>
      .losslessProdCons
        (.call
          (.const () uniSetMapDl.consts.uniSetMap)
          (toExpr elem))
        acc)
    .null

/-
  Turns a list of `uniSetMap` indices into an index of the
  lossless product of their trisets.
-/
def uniSetMapIndex.packList
  (indices: List Pair)
:
  Pair
:=
  uniSetMapIndex
    uniSetMapDl.toDefList
    uniSetMapDl.size
    []
    (packListExpr indices Pair.toExpr)

def uniSetMapIndex.unpackListAt
  (index: Pair)
  (n: Nat)
:
  Pair
:=
  uniSetMapIndex
    uniSetMapDl.toDefList
    uniSetMapDl.size
    []
    (.losslessProdAt
      n
      (.call
        (.const () uniSetMapDl.consts.uniSetMap)
        index.toExpr))

theorem uniSetMapIndex.unpackListAt_packList_triset_eq
  (indices: List Pair)
  (n: Nat)
:
  Eq
    (uniSetMap.call (unpackListAt (packList indices) n))
    (uniSetMap.call (indices.getD n emptyIndex))
:=
  sorry

theorem uniSetMapIndex.unpackListAt_packList_bisim
  (indices: List Pair)
  (n: Nat)
:
  Pair.PreTrisetFn.IsBisim
    (unpackListAt (packList indices) n)
    (indices.getD n emptyIndex)
:=
  Pair.PreTrisetFn.isBisim_of_uniSetMap_call_eq
    (unpackListAt_packList_triset_eq indices n)


-- ## Section: Triset Expressions and Interpretation

/-
  Represents the basic operations on trisets.
  
  Unlike `Expr`, does not contain `compl`. Instead, we have
  all the duals so that we may define complements as a syntax sugar.
  This is because (I suppose, TODO verify) that double complements
  would not cancel out, since they'd get represented as
  `[~(uniSetMap [~X])]` instead of `[~~X]` (in the latter, the
  conversion to negation normal form would eliminate the double
  complement).
  
  (Tbh, with non-monotonic constructors like `singleton` and `isIn`,
  I'm not really sure whether dualizing them instead of defining
  their complemented versions is a good idea (eg. not sure whether
  I should have `singletonDual = compl ∘ singleton ∘ compl` or
  `complSingleton = compl ∘ singleton`). But I had to make some
  choice. If it turns out not to be a good one, we can adjust later.)
  
  (Empty and full are also definable as `let A = A`, but it's convenient
  not to need a deflist for having them definable.)
  
  TODO should I just cut the complement versions and keep a single
  complement? I get the fear of losing the dualities, *and* WFC looks
  just so pretty with them all, but first of all singleton and isIn
  aren't monotonic so dualizing them might not have a point in the
  first place, and second of all they just look so dumb.
-/
inductive TrisetFnExpr
| var (x: Nat)
| const (x: Nat)
| empty
| univ
| singleton (elem: TrisetFnExpr)
| isIn (set elem: TrisetFnExpr)
-- TODO switch to this?
-- | isIn (elem set res: TrisetFnExpr)
| ir (left rite: TrisetFnExpr)
| un (left rite: TrisetFnExpr)
| diff (left rite: TrisetFnExpr)
| arbIr (domain: TrisetFnExpr) (body: TrisetFnExpr)
| arbUn (domain: TrisetFnExpr) (body: TrisetFnExpr)
-- TODO is this necessary?
-- | ifThen (cond res: TrisetFnExpr)
-- TODO should functions have domains?
| fn (domain: TrisetFnExpr) (body: TrisetFnExpr)
| app (fn arg: TrisetFnExpr)

-- def TrisetFnExpr.compl: TrisetFnExpr → TrisetFnExpr
-- | var x => complVar x
-- | complVar x => var x
-- | const x => complConst x
-- | complConst x => const x
-- | empty => univ
-- | univ => empty
-- | singleton elem => singletonDual (compl elem)
-- | singletonDual elem => singleton (compl elem)
-- | isIn set elem => isInDual (compl set) (compl elem)
-- | isInDual set elem => isIn (compl set) (compl elem)
-- | ir left rite => un (compl left) (compl rite)
-- | un left rite => ir (compl left) (compl rite)
-- | arbIr domain body => arbUn domain (compl body)
-- | arbUn domain body => arbIr domain (compl body)

-- TODO: verify these are defined right. Probably should move to
-- a separate file.

-- `fs` constructs a *finite set* from a list of elements.
exposed def TrisetFnExpr.fs: List TrisetFnExpr → TrisetFnExpr
| [] => empty
| elem :: [] => singleton elem
| elem :: rest => un (singleton elem) (fs rest)

exposed def TrisetFnExpr.ifThen (cond res: TrisetFnExpr): TrisetFnExpr :=
  arbUn cond res

exposed def TrisetFnExpr.ifElse (cond res: TrisetFnExpr): TrisetFnExpr :=
  sorry

exposed def TrisetFnExpr.flatten (expr: TrisetFnExpr): TrisetFnExpr :=
  arbUn expr (var 0)

exposed def TrisetFnExpr.pair (a b: TrisetFnExpr): TrisetFnExpr :=
  fs [
    fs [empty, singleton a],
    fs [singleton empty, singleton (singleton b)]
  ]

exposed def TrisetFnExpr.zth (pair: TrisetFnExpr): TrisetFnExpr :=
  arbUn
    pair
    (ifThen
      -- (ir (var 0) (singleton empty))
      (isIn (var 0) empty)
      (flatten (var 0)))

exposed def TrisetFnExpr.fst (pair: TrisetFnExpr): TrisetFnExpr :=
  arbUn
    pair
    (ifThen
      -- (ir (var 0) (singleton (singleton empty)))
      (isIn (var 0) (singleton empty))
      (flatten (flatten (var 0))))

exposed def TrisetFnExpr.prod (a b: TrisetFnExpr): TrisetFnExpr :=
  sorry

-- TODO analogous to `Expr.call`.
exposed def TrisetFnExpr.call (fn arg: TrisetFnExpr): TrisetFnExpr :=
  arbUn fn (ifThen (ir (zth (var 0)) arg) (fst (var 0)))


-- `freeVarsExpr 0 n` returns `var 0 × var 1 × ... × var n`.
-- https://www.cs.utexas.edu/~EWD/transcriptions/EWD08xx/EWD831.html
exposed def TrisetFnExpr.toBasicExpr.freeVarsExpr
  (currentVar varLength: Nat)
:
  BasicExpr
:=
  if currentVar < varLength then
    .prod
      (.var currentVar)
      (freeVarsExpr varLength currentVar.succ)
  else
    .null

exposed def TrisetFnExpr.toBasicExpr.indexExpr
  (dl: FiniteDefList)
  (varLength: Nat)
  (expr: BasicExpr)
:
  BasicExpr
:=
  .prod
    (dl.prefixEncoding dl.size).toExpr
    (.prod
      (toBasicExpr.freeVarsExpr 0 varLength)
      expr.encoding.toExpr)

exposed def uniSetMapCallLift
  (expr: BasicExpr)
:
  BasicExpr
:=
  .call (.const () uniSetMapDl.consts.uniSetMap) expr.lift

open TrisetFnExpr.toBasicExpr in
exposed def TrisetFnExpr.toBasicExpr (varLength: Nat): TrisetFnExpr → BasicExpr
| var x =>
    if x < varLength then
      .var x
    else
      Pair.PreTrisetFn.empty.toExpr
| const x =>
    indexExpr
      uniSetMapDl
      varLength.succ
      -- note: we need to lift the variable index by x+1 because of how
      -- `losslessProdAt` is implemented.
      -- TODO are the parentheses around `x + 1` worth it?
      (.losslessProdAt x (uniSetMapCallLift (.var (varLength + (x + 1)))))
| empty => Pair.PreTrisetFn.empty.toExpr
| univ => sorry
| singleton elem =>
    -- uniSetMapIndex
    --   opFixDl.toDefList
    --   opFixDl.size
    --   []
    --   (.call
    --     (.const () opFixDl.consts.encodeAsExpr)
    --     (elem.preIntp fv consts).toExpr)
    sorry
| isIn set elem => sorry
| ir left rite =>
    -- TODO incorrect, we need triset intersection not TfP intersection.
    -- uniSetMapIndex
    --   uniSetMapDl.toDefList
    --   uniSetMapDl.size
    --   []
    --   (.ir
    --     (.call
    --       (.const () uniSetMapDl.consts.uniSetMap)
    --       (left.preIntp fv consts).toExpr)
    --     (.call
    --       (.const () uniSetMapDl.consts.uniSetMap)
    --       (rite.preIntp fv consts).toExpr))
    sorry
| un left rite =>
    -- uniSetMapIndex
    --   uniSetMapDl.toDefList
    --   uniSetMapDl.size
    --   []
    --   (.un
    --     (.call
    --       (.const () uniSetMapDl.consts.uniSetMap)
    --       (left.preIntp fv consts).toExpr)
    --     (.call
    --       (.const () uniSetMapDl.consts.uniSetMap)
    --       (rite.preIntp fv consts).toExpr))
    sorry
| diff left rite => sorry
| arbIr domain body => sorry
| arbUn domain body => sorry
| fn domain body => sorry
| app f arg => sorry

def TrisetFnExpr.preIntp
  (expr: TrisetFnExpr)
  (fv consts: List Pair.PreTrisetFn)
:
  Pair.PreTrisetFn
:=
  uniSetMapIndex
    FiniteDefList.empty.toDefList
    FiniteDefList.empty.size
    (fv.concat (uniSetMapIndex.packList consts))
    (expr.toBasicExpr fv.length)

theorem TrisetFnExpr.preIntp_respects_bisim
  (expr: TrisetFnExpr)
  (fv0 fv1 consts0 consts1: List Pair.PreTrisetFn)
  (fvEquiv:
    ∀ x,
      Pair.PreTrisetFn.IsBisim
        (fv0.getD x Pair.PreTrisetFn.empty)
        (fv1.getD x Pair.PreTrisetFn.empty))
  (constsEquiv:
    ∀ x,
      Pair.PreTrisetFn.IsBisim
        (consts0.getD x Pair.PreTrisetFn.empty)
        (consts1.getD x Pair.PreTrisetFn.empty))
:
  (expr.preIntp fv0 consts0).IsBisim (expr.preIntp fv1 consts1)
:=
  match expr with
  | var x => sorry
  | const x =>
      sorry
  | empty => sorry
  | univ => sorry
  | singleton elem => sorry
  | isIn set elem => sorry
  | ir left rite => sorry
  | un left rite => sorry
  | diff left rite => sorry
  | arbIr domain body => sorry
  | arbUn domain body => sorry
  | fn domain body => sorry
  | app f arg => sorry

exposed def TrisetFnExpr.intp
  (expr: TrisetFnExpr)
  (fv consts: List Pair.Triset)
:
  Pair.Triset
:=
  sorry

-- TODO `intp (.inter a b) = inter (intp a) (intp b)` style proofs

/-
  Converts a `TrisetFnExpr` to the corresponding `BasicExpr` that
  works on `uniSetMap` indices.
  
  Assumes the returned expression will be used in a context with
  `varLength + 1` variables, and the outermost variable is the one
  that represents the constants. This allows using `toBasicExpr`
  together with `indexFix` from Chapter 7. For example, we'd want to represent
  
  TODO indexFix was good for pure trisets, but for TrisetFn we need
  a new representation - we need to operate on codes of singletons of
  codes. If `[p]` means the code of `p`, the empty TrisetFn would be
  `[{(0, [{}])}]` - a code for the singleton of a pair of zero and the
  code of an empty triset.
  Wait, but that may still work with indexFix.
  
  ```
    s3 A = { A }
  ```
  
  as
  
  ```
    s3 DlT := Ex T, T × "{ T }".toBasicExpr
    
    s3 A := indexFix [DlT]
  ```
  
  (Note the above example is simplified to expect only a single
  definition as input. Below we expect multiple definitions, which
  we fold into a single one using lossless products.)
  
  TODO also figure out whether taking a singleton is dualizable
  at all, and ensure the negation normal form (if it exists in the
  first place) has the same semantics.
-/
-- open TrisetFnExpr.toBasicExpr in
-- def TrisetFnExpr.toBasicExpr (varLength: Nat): TrisetFnExpr → BasicExpr
-- | var x =>
--   if x < varLength then
--     .var x
--   else
--     Pair.PreTrisetFn.empty.toExpr
-- | complVar x =>
--   sorry
-- | const x =>
--   indexExpr
--     uniSetMapDl
--     varLength.succ
--     -- note: we need to lift the variable index by x+1 because of how
--     -- `losslessProdAt` is implementated.
--     (.losslessProdAt x (uniSetMapCallExpr (.var (varLength + (x + 1)))))
-- | complConst x =>
--   indexExpr
--     uniSetMapDl
--     varLength.succ
--     (.compl (.nth x (uniSetMapCallExpr (.var (varLength + x)))))
-- | singleton elem =>
--   -- Given an expression `elem` that evaluates to a singleton TfP
--   -- `{ i }`, return an expression that evaluates to an index `j` such
--   -- that `uniSetMap.call j = { i }`.
--   indexExpr
--     opFixDl
--     varLength.succ
--     (.call
--       (.const () opFixDl.consts.encodeAsExpr)
--       (elem.toBasicExpr varLength).lift)
-- | singletonDual elem =>
--   sorry
-- | ir left rite =>
--   -- An index for `uniSetMap iLeft & uniSetMap iRight`.
--   -- TODO this is wrong because we need to treat bisimilar
--   -- sets as same even if they are coded by different pairs.
--   indexExpr
--     uniSetMapDl
--     varLength.succ
--     (.ir
--       (uniSetMapCallExpr (left.toBasicExpr varLength))
--       (uniSetMapCallExpr (rite.toBasicExpr varLength)))
-- | un left rite =>
--   -- An index for `uniSetMap iLeft | uniSetMap iRight`.
--   -- TODO is this correct?
--   indexExpr
--     uniSetMapDl
--     varLength.succ
--     (.un
--       (uniSetMapCallExpr (left.toBasicExpr varLength))
--       (uniSetMapCallExpr (rite.toBasicExpr varLength)))
-- | arbIr domain body =>
--   -- Should increment the variable length at the right places.
--   -- Support for domain needs to be implemented here.
--   -- Sth like: `All t, (?some t & ~uniSetMap iBody) | uniSetMap iDomain`?
--   sorry
-- | arbUn domain body =>
--   -- Sth like: `Ex t, (?some t & uniSetMap iBody) & uniSetMap iDomain`
--   sorry
-- | isIn set elem =>
--   -- See `isInDl.IsIn` in `TrisetMembership.lean`.
--   sorry
-- | isInDual set elem =>
--   sorry

theorem TrisetFnExpr.toBasicExpr_contains_preIntp
  (expr: TrisetFnExpr)
  -- Does not matter, `toBasicExpr` has no constants.
  (metaVal: Valuation Pair)
  (fv consts: List Pair.PreTrisetFn)
:
  Set.Mem
    (Set3.defMem
      ((expr.toBasicExpr fv.length).triIntp
        (fv.concat (uniSetMapIndex.packList consts))
        metaVal))
    (expr.preIntp fv consts)
:=
  match expr with
  | var x => sorry
  | const x => sorry
  | empty => sorry
  | univ => sorry
  | singleton elem => sorry
  | isIn set elem => sorry
  | ir left rite => sorry
  | un left rite => sorry
  | diff left rite => sorry
  | arbIr domain body => sorry
  | arbUn domain body => sorry
  | fn domain body => sorry
  | app f arg => sorry

theorem TrisetFnExpr.toBasicExpr_contains_only_preIntp
  {expr: TrisetFnExpr}
  {metaVal fv consts p}
  (isPos:
    Set.Mem
      (Set3.posMem
        ((expr.toBasicExpr fv.length).triIntp
          (fv.concat (uniSetMapIndex.packList consts))
          metaVal))
      p)
:
  p = expr.preIntp fv consts
:=
  match expr with
  | var x => sorry
  | const x => sorry
  | empty => sorry
  | univ => sorry
  | singleton elem => sorry
  | isIn set elem => sorry
  | ir left rite => sorry
  | un left rite => sorry
  | diff left rite => sorry
  | arbIr domain body => sorry
  | arbUn domain body => sorry
  | fn domain body => sorry
  | app f arg => sorry

theorem TrisetFnExpr.toBasicExpr_eq_preIntp
  (expr: TrisetFnExpr)
  -- Does not matter, `toBasicExpr` has no constants.
  (metaVal: Valuation Pair)
  (consts: List Pair.PreTrisetFn)
  (fv: List Pair.PreTrisetFn)
:
  Eq
    ((expr.toBasicExpr fv.length).triIntp
      (fv.concat (uniSetMapIndex.packList consts))
      metaVal)
    (Set3.just (expr.preIntp fv consts))
:=
  Set3.eq4
    sorry
    sorry
    sorry
    sorry


-- ## Section: Triset Definition Lists

structure TrisetDef where
  expr: TrisetFnExpr

def TrisetDef.toBasicExpr (df: TrisetDef): BasicExpr :=
  df.expr.toBasicExpr 0 


exposed def TrisetDl := List TrisetDef

def TrisetDl.toDefExpr (dl: TrisetDl): BasicExpr :=
  uniSetMapIndex.packListExpr dl TrisetDef.toBasicExpr

def TrisetDl.opIndex (dl: TrisetDl): Pair :=
  uniSetMapIndex
    FiniteDefList.empty.toDefList
    FiniteDefList.empty.size
    []
    (.arbUn (.prod (.var 0) dl.toDefExpr))

def TrisetDl.wfmIndex (dl: TrisetDl): Pair :=
  indexFixIndex (opIndex dl)

def TrisetDl.wfm
  (dl: TrisetDl)
  (x: Fin dl.length)
:
  Pair.Triset
:=
  ⟦uniSetMapIndex.unpackListAt dl.wfmIndex x⟧

def TrisetDl.intp
  (dl: TrisetDl)
  (expr: TrisetFnExpr)
:
  Pair.Triset
:=
  expr.intp [] (List.ofFn dl.wfm)

theorem TrisetDl.wfm_is_model
  (dl: TrisetDl)
  (x: Fin dl.length)
:
  dl.wfm x = dl.intp (dl.get x).expr
:=
  sorry

/-
  TODO sanity check -- do these have the expected semantics?
  To be proven later.
  
  s3 Empty := Empty
  s3 Univ := ~Empty
  
  s3 Singleton := Ex T: Univ, {T}
  
  s3 A := { A } -- the quine atom?
  s3 B := {} | { B } -- ???
  s3 C := B & ~A -- maybe the hereditarily subsingletons?
  
  is A a subset of B?
  
  Can I define the (classical) triset of all (classical) hereditarily
  finite sets?
  
  TODO Can we prove (is it true) that without pairs (ie. working with
  trisets only), it would be impossible to define pairs as Kuratowski
  pairs, because the projection operators are not WFC definable?
  
  TODO Can we prove Trisets are as capable as TrisetPair without
  having to declare all the operations of Triset plus the pair operations
  on TrisetPair?
  - probably, if we can encode/simulate WFC within Trisets. Since
    WFC can simulate Trisets (fingers crossed), this would demonstrate
    equal expressive power.
-/
-/
