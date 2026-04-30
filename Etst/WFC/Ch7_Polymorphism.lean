/-
  # Chapter 7: Polymorphism
  
  Used syntax sugars:
  
  - named variables: Eg. `Ex x, x` instead of `arbUn (var 0)`
  - function calls: `f x`, see `Expr.call` in `PairExpr.lean`
    for syntax, and `Set3.call` for a restricted semantic
    version.
  - parameters: `s3 Foo (x: Bar) := [body]` instead of
    `s3 Foo := Ex x, (some x & Bar) & (x, [body])`
  
  Function calls and parameters work together just as one would expect:
  for `s3 Foo n := (n, null)`, the expression `Foo x` evaluates to the
  same value as `(x, null)`.
  
  ## The what
  
  WFC does not "natively" support polymorphism or quantification over
  types (ie. definable trisets). Nevertheless, it is powerful enough
  that we can build these features ourselves in it. This chapter shows
  how.
  
  On a more theoretical level, the chapter can be understood as showing
  that diagonalization arguments a la the diagonal lemma and Rogers's
  fixed-point theorem go through in WFC, and we can define fixed points
  of arbitrary definable transformations of definable trisets, internally.
  
  ## The easy part
  
  The initial "showing how" proceeds by example -- here is a simple
  definition of a list of natural numbers:
  
  ```
    s3 Nat := null | (Nat, null) -- zero or successor
    s3 ListNat :=
      | null -- the empty list
      | (Nat, ListNat) -- a head and tail
  ```
  
  We would like to quantify this definition with a type of the elements
  of the list instead of hardcoding `Nat`. Thanks to `uniSetMap` from
  the previous chapter, this is a really easy task:
  
  ```
    s3 List (T: Any) :=
      | null
      | (uniSetMap T, List T)
  ```
  
  From the previous chapter, we know that for any definable triset `t`,
  there is an index pair `i` such that `uniSetMap i` evaluates to `t`.
  
  This index pair is just a mechanical encoding of an expression defining
  `t` (along with a definition list defining the constants used by the
  expression, and a list of free variables with which to interpret it),
  and is computable from these three -- see `uniSetMapIndex`. (The fourth
  param, `n`, just needs to be large enough so that all used constants
  are less than `n`.
  
  Thanks to the above, a caller wishing to use a List of eg. pairs of
  naturals just needs to mechanically convert `(Nat, Nat)` to the
  corresponding index, and then use `List i`.
  
  This also means that quantification over types collapses to
  quantification over pairs, and it is up to authors of definitions to
  decide whether they will use a parameter as a pair or an encoding of
  a type.
  
  So far, all is well... that is, unless the caller would like to pass
  to `List` the type they are trying to define in the first place. What
  about definitions like `s3 Foo := List (Foo | Nat)`?
  
  ## The self-referential case
  
  TODO diagonal lemma? we're being syntactic after all
  The answer is Rogers's fixed-point theorem. An index representing such
  a definition is guaranteed to exist, even in case of multiple mutually
  self-referential definitions. We prove that in this chapter.
  
  TODO revisit this description when the chapter is done, make sure it
  is accurate.
  
  For example, the type
  
      s3 Foo := List (Foo | null)
  
  will be defined as a fixed point of
  
      s3 FooT Foo := List (uniSetMap Foo | null)
  
  Footnotes:
  0. To quote a legend: "I am dogmatic, and I believe that 0 is the very
    zerost number." No particular reason for the quotation is given.
    https://tex.stackexchange.com/questions/325340/
-/

import Etst.WFC.Ch6_SelfDefinability

namespace Etst


-- TODO the chapter lol. don't forget to clean up.

-- ## Section: Single definition version

def Pair.toExpr: Pair → BasicExpr
| .null => .null
| .pair l r => .pair l.toExpr r.toExpr

/-
  Represents an index (interpretable with `uniSetMap`) of a call
  expression with `fn` and `arg` as the function and argument
  encodings.
  
  (More accurately, the expression part of the index, see
  `uniSetMapIndex`).
-/
def Expr.callEncExpr {E}
  (fn arg: Expr E)
:
  Expr E
:=
  s3(null, (11, (6, ((9, (6, ([fn], (5, ([arg], (2, 0)))))), (2, 0)))))

def Expr.callEncExpr_eq
  (fn arg: BasicExpr)
:
  Eq
    (fn.encoding.toExpr.callEncExpr arg.encoding.toExpr)
    (BasicExpr.encoding (fn.call arg)).toExpr
:=
  rfl


def uniSetMapDlEncoding :=
  uniSetMapDl.prefixEncoding (uniSetMapDl.consts.uniSetMap + 1)

open uniSetMapDl in
pairDefList callFixHelpersDl extends uniSetMapDl
  -- `callEnc i j` returns the index representing `(uniSetMap i).call j`.
  s3 callEnc :=
    Ex fn arg, (
      fn, (arg,
      (
        [uniSetMapDlEncoding.toExpr],
        (
          null,
          [(uniSetMapConst.callEncExpr (.var 1)).callEncExpr (.var 0)],
        )
      )
    ))
  
  s3 diag := Ex i, (i, callEnc i i)
  
  -- Named χ on the wiki's article on the Diagonal lemma:
  s3 magic := Ex op i, (op, (i, uniSetMap op (diag i)))
pairDefList.

def callFixDl.magicIndex: Pair :=
  (uniSetMapIndex
    callFixHelpersDl.toDefList
    (callFixHelpersDl.consts.magic + 1)
    []
    (.const callFixHelpersDl.consts.magic))

pairDefList callFixDl extends callFixHelpersDl  
  s3 callFix :=
    Ex i, (
      i,
      (magic i) (callEnc [callFixDl.magicIndex.toExpr] i)
    )
pairDefList.


-- Hopefully, at least one of these is the correct statement
-- of the main result.
def callFix_eq_A
  (i: Pair)
:
  ∃ iFix: Pair,
  And
    (callFixDl.vals.callFix.call i = uniSetMap.call iFix)
    (callFixDl.vals.callFix.call i = (uniSetMap.call i).call iFix)
:=
  sorry





-- Goal: a practical way to use this. Delete later?
pairDefList ExamplePolymorphismDl extends callFixDl
  -- Note: pairDefList does not yet support param syntax, so we
  -- desugar it manually.
  s3 List :=
    Ex T, (
      T,
      | null
      | (uniSetMap T, List T)
    )
  
  -- s3 Foo := List Foo
  -- s3 FooNull := List (FooNull | null)
  s3 FooNullT := Ex T, (T, List (T | null))
pairDefList.


-- TODO either delete later, or fix the hack in the impl.
def FinBoundedDL.getConstEncoding
  (dl: FinBoundedDL)
  (x: Nat)
:
  Pair
:=
  uniSetMapIndex
    dl.toDefList
    (x + 1) -- just a hack assuming the definition does not use latter constants.
    []
    (.const x)

open ExamplePolymorphismDl in
def listIndex: Pair :=
  ExamplePolymorphismDl.getConstEncoding consts.List

open ExamplePolymorphismDl in
def fooNullIndex: Pair :=
  ExamplePolymorphismDl.getConstEncoding consts.FooNullT


pairDefList ExamplePolymorphismUsageDl extends ExamplePolymorphismDl
  -- TODO: uncomment when not reliant on sorry.
  -- s3 Foo := callFix [listIndex.toExpr]
  -- s3 FooNull := callFix [fooNullIndex.toExpr]
pairDefList.
