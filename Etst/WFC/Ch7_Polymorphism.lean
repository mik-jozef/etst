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
  
  Because polymorphic types are encoded with just ordinary types, this
  works recursively too -- higher order polymorphism is a part of the
  package.
  
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
  This index is mechanically derivable from the definition of `t`.
  
  Thanks to that, a caller wishing to use a List of eg. pairs of
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
  
  An index representing the fixed point of any such definition may be
  defined by a diagonal-lemma-like construction. Like with the previous
  chapters, the plumbing is hidden in a utility file, with the chapter
  displaying the main results.
  
  For example, the type
  
      s3 Foo := List (Foo | null)
  
  will be defined as a fixed point of
  
      s3 FooT Foo := List (uniSetMap Foo | null)
  
  Footnotes:
  0. To quote a legend: "I am dogmatic, and I believe that 0 is the very
    zerost number." No particular reason for the quotation is given.
    https://tex.stackexchange.com/questions/325340/
-/

import Etst.WFC.Utils.SelfDefinability.PolymorphismHelpers

namespace Etst


-- ## Section: Single definition version

/-
  The main result: `magicCallIndex iFn` is the index of a fixed point
  of `iFn`.
-/
open callFixDl in
def magicCallIndex_fix
  (iFn: Pair)
:
  Eq
    (uniSetMap.call (magicCallIndex iFn))
    ((uniSetMap.call iFn).call (magicCallIndex iFn))
:=
  magicCallIndex_eq iFn ▸
  magic_call_eq iFn (magicIndex.callEnc iFn) ▸
  rfl

/-
  The fixed point `magicCallIndex iFn` is definable internally.
-/
open callFixDl in
def callFix_call_eq_magic (iFn: Pair):
  Eq
    (vals.callFix.call iFn)
    ((uniSetMap.call iFn).call (magicCallIndex iFn))
:=
  (callFix_call_eq iFn).trans (magicCallIndex_fix iFn)


-- ## Section: Multiple definitions version

/-
  We would like to define the fixed point for several mutually
  self-referential definitions. However, this is doable in a very
  mechanical and unenlightening way by merging a list of definitions
  into a single definition defining a tuple of the defined types, and
  then using the single-definition version.
  
  Because this is guaranteed to work, but would still involve tedious
  proofs of equivalences, I'm leaving this excercise as my future's me
  problem.
-/
