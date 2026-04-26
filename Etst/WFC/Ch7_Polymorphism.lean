/-
  # Chapter 7: Polymorphism
  
  Used syntax sugars:
  
  - named variables: Eg. `Ex x, x` instead of `arbUn (var 0)`
  - function calls: `f x`, see `Expr.call` in `PairExpr.lean`
    for syntax, and `Set3.pairCallJust` for a restricted semantic
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
  about definitions like `s3 Foo := List (Foo | Nat)`? And what about
  `Ex x, List x`, the type of all single-element lists?
  
  ## The self-referential case
  
  The answer is Kleene's recursion theorem. An index representing such
  a definition is guaranteed to exist, even in case of multiple mutually
  self-referential definitions. We prove that in this chapter.
  
  TODO revisit this description when the chapter is done, make sure it
  is accurate.
  
  Footnotes:
  0. To quote a legend: "I am dogmatic, and I believe that 0 is the very
    zerost number." No particular reason for the quotation is given.
    https://tex.stackexchange.com/questions/325340/
-/

import Etst.WFC.Ch6_SelfDefinability


-- TODO the chapter lol
