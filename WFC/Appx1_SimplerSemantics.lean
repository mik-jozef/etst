/-
  Appendix 1: Simpler semantics
  
  TODO this is just a half baked idea for an inequivalent,
  but hopefully essentially the same, semantics. It only
  uses a single valuation that maps expressions (not variables!)
  to elements, and the interpretation interprets expressions
  based on the value of their direct subexpressions.
  
  The iterative process begins with an empty valuation. The limit
  ordinals get assigned a limit infimum of the previous stages,
  with respect to the approximation order.
  
  It is unclear whether this idea is even well-founded, since
  it is not trivially clear whether this process is guaranteed
  to converge to a stable valuation.
  
  This semantics is inequivalent to the original semantics, take
  
      let x = x | ~x \,.
  
  In the original semantics, x is undetermined, while in the
  propsed semantics, x is the universal set. The hope is that
  these differences are inessential, and in particular that the
  definable sets are the same.
-/
