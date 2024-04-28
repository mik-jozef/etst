import ExampleWFCs
import UniDefList
import UniSet3.DefListToEncoding


namespace theDefListExternal
  open Pair
  open uniDefList
  
  def Expr := _root_.Expr pairSignature
  def Expr.toEnc := Pair.exprToEncoding
  
  
  noncomputable def getDef
    (x: Nat)
  :
    Expr
  :=
    sorry
  
end theDefListExternal

noncomputable def theDefListExternal:
  DefList pairSignature
:= {
  getDef := theDefListExternal.getDef
  -- Oh shit. The "DefList" I've been building in
  -- `UniDefList.lean` and `Defs.lean` isn't really
  -- finitely bounded, is it? (That would be a massive
  -- coincidence, I'm sure it's not.)
  -- The easiest way out of this mess is likely to
  -- remove `isFinBounded` from the definition of
  -- a DefList, and add it to the definition of
  -- `Salgebra.IsDefinable`. May be even a good
  -- thing, as the interpretation of non-ninitely
  -- bounded definition lists is a perfectly
  -- well-defined concept, it's just that definability
  -- then needs to be defined with greater care.
  isFinBounded := sorry
}
