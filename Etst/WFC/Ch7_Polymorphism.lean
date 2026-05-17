/-
  # Chapter 7: Polymorphism
  
  Used syntax sugars:
  
  - named variables: Eg. `Ex x, x` instead of `arbUn (var 0)`
  - function calls: `f x`, see `Expr.call` in `PairExpr.lean`
    for syntax, and `Set3.call` / `Set3.flatCall` for the semantic
    version.
  - parameters: `s3 Foo T := [body]` means `s3 Foo := Ex T, (T, [body])`
  
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
  of arbitrary definable transformations of trisets, internally.
  
  ## The easy part
  
  TODO the approach shown here works, but might not be the one that
  will eventually be chosen as the "official" way to do polymorphism,
  resp. what polymorphism in latter chapters desugars into.
  To be revised later, potentially.
  
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
  The main result: `trisetFixIndex iFn` is the index of a fixed point
  of `iFn`.
-/
open opFixDl in
def trisetFixIndex_fix
  (iFn: Pair)
:
  Eq
    (uniSetMap.call (trisetFixIndex iFn))
    ((uniSetMap.call iFn).call (trisetFixIndex iFn))
:=
  trisetFixIndex_eq iFn ▸
  magic_call_eq iFn (magicIndex.callEnc iFn) ▸
  rfl

/-
  The fixed point `trisetFixIndex iFn` is definable internally.
-/
open opFixDl in
def trisetFix_eq (iFn: Pair):
  Eq
    (vals.trisetFix.call iFn)
    ((uniSetMap.call iFn).call (trisetFixIndex iFn))
:=
  (trisetFix_call_eq iFn).trans (trisetFixIndex_fix iFn)


/-
  A version of the above for operators on indices instead of maps from
  indices to trisets.
-/
def indexFixIndex (iOp: Pair): Pair :=
  opFixDl.trisetFixIndex (composeIndex iOp)

open opFixDl in
def indexFixIndex_fix (iOp: Pair):
  Eq
    (uniSetMap.call (indexFixIndex iOp))
    (uniSetMap.flatCall ((uniSetMap.call iOp).call (indexFixIndex iOp)))
:=
  (trisetFixIndex_fix (composeIndex iOp)).trans
    (composeIndex_call iOp (indexFixIndex iOp))

/-
  Specialized to the case where `iOp` is total and functional at
  the fixed point input: if its output there is a single index `p`,
  then `indexFixIndex iOp` and `p` denote the same triset.
-/
def indexFixIndex_fix_of_just
  (iOp: Pair)
  {p: Pair}
  (hJust: (uniSetMap.call iOp).call (indexFixIndex iOp) = Set3.just p)
:
  Eq
    (uniSetMap.call (indexFixIndex iOp))
    (uniSetMap.call p)
:=
  (indexFixIndex_fix iOp).trans
    (hJust ▸ Set3.flatCall_just uniSetMap p)

/-
  Variant for the case where `iOp` codes a total function
  `f: Pair → Pair`. Then `indexFixIndex iOp` denotes the same
  triset as `f` applied to it.
-/
def indexFixIndex_fix_of_fn
  (iOp: Pair)
  (f: Pair → Pair)
  (hFn: ∀ arg, (uniSetMap.call iOp).call arg = Set3.just (f arg))
:
  Eq
    (uniSetMap.call (indexFixIndex iOp))
    (uniSetMap.call (f (indexFixIndex iOp)))
:=
  indexFixIndex_fix_of_just iOp (hFn (indexFixIndex iOp))


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
