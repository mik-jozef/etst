import ExampleWFCs
import UniSet3.UniDefList
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
}
