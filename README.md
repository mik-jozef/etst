# Well-Founded Collections and a Theory of Three-Valued Sets

Well-founded collections are a formalism for defining three-valued
collections (or trisets) using recursive definitions that may
contain complements, while avoiding classical paradoxes of mixing
negation and self-reference.

TODO ETST is

All the math is formalized in the theorem prover
[Lean 4](https://lean-lang.org/).


## Quick introduction
### Trisets
A triset is a three-valued version of a set. To a triset, any
element is related in one of three ways:

0. it may be a (definite) member of that triset,
1. it may be a (definite) nonmember, or
2. its membership may be in an *undetermined* state.

An element that is either a definite or an undetermined member
is called a *possible member*, analogously there are *possible
nonmembers*. A triset whose elements are all determined is called
*classical*, or two-valued, and corresponds to a set.

### What well-founded collections are
Let's assume we are working with natural numbers, and our operations
on them are the constant zero and the successor function.

We may define the (tri)set of even numbers recursively like this:

```
  let even = 0 ∪ succ (succ even)
```

Equivalently, we could use the complement:

```
  let even = ~(succ even)
```

The latter definition feels a bit "dangerous" as complements are
not monotonic. That is because non-monotonic definitions need not
make sense when interpreted in a classical, two-valued way. For
example, take

```
  let bad = ~bad
```

Here, `bad` is meant to contain exactly those elements it does not
contain, which is contradictory. Well-founded collections nevertheless
gives a natural semantics to recursive definitions that employ
complements in arbitrary way.

This is achieved while preserving the standard semantics of those
definitions that are complement-free, or whose complements are not
circular. That is, "sensible" definitions retain their two-valued
semantics.

The additional state *undetermined* is used for elements whose
membership in a set cannot be reasonably determined because of
self-referential negations. This is how paradoxes similar to the
Russel paradox are avoided. (The triset `bad` defined above is the
wholly undetermined triset.)


## Project structure
The project is divided into several folders, or volumes, which in
turn are divided into chapters that may be read (or skimmed over)
sequentially.

The folder `/WFC` contains the definition of the formalism of
well-founded collections. This includes formally defining trisets,
the syntax of WFC, its semantics, and a sound and complete proof
system for definite membership / nonmembership. An instance of WFC
of particular interest is defined – the Well-founded collections
of Pairs (pairs being unlabelled binary trees).

The folder `/UniSet3` defines a special triset of pairs that in a
sense "contains" all definable trisets of pairs. This triset is
shown to be itself definable (in WFC). Contradictions a la Russell
are avoided because of the three-valued nature of trisets.

The folder `/Trisets` is TODO under construction.

The folder `/HM` is TODO currently broken and unused, to be fixed.

The folder `/Utils` contains various utility files.


## Previous work
Well-founded collections are generalization of *well-founded
semantics* [[0]][van-gelder-wfs] for arbitrary domains (with
monotonic operations), not just the boolean domain
`{ true, false }`. The formalization models that of the well-founded
semantics for boolean grammars [[1]][wfs-bg]. Unlike these, WFC also
feature the existential and universal quantifier.

### References
For more references and context, mostly from the area of programming
language theory, see my magister thesis [[2]][my-mgr-thesis] (the
Czech equivalent of the master's thesis).

[van-gelder-wfs]: https://dl.acm.org/doi/10.1145/116825.116838
[wfs-bg]: https://www.sciencedirect.com/science/article/pii/S0890540109001473
[my-mgr-thesis]: https://is.muni.cz/th/xr8vu/Well-founded-type-semantics.pdf

0. Allen Van Gelder, Kenneth A. Ross, John S. Schlipf (July 1991):
   [The well-founded semantics for general logic programs][van-gelder-wfs]
1. Vassilis Kountouriotis, Christos Nomikos, Panos Rondogiannis (2009):
   [Well-founded semantics for Boolean grammars][wfs-bg]
2. Jozef Mikušinec (2022): Well-founded semantics for dependent,
   recursive record types with type complement


## Future plans
TODO I hope to make this a base for a semantics of a sound type system of a programming language suitable for mathematics (a theorem prover).
