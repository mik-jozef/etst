module
public import Etst.WFC.Utils.Trisets.TrisetFn.TrisetFn
public import Etst.WFC.Ch6_SelfDefinability

public section
namespace Etst


def Expr.encodingExpr (expr: Expr .basic): Expr .basic :=
  expr.encoding.toExpr

/-- The `uniSetMap` constant of `uniSetMapDl`, as an expression. -/
def Expr.uniSetMapConst: Expr .basic :=
  uniSetMapDl.constExpr () "uniSetMap"

/-
  Given two uniSetMap indices, returns an index of their union. `dlEnc`
  must be a deflist encoding of an extension of `uniSetMapDl`.
-/
exposed def uniSetMapIndex.un
  (dlEnc left rite: Expr .basic)
:
  Expr .basic
:=
  .prod dlEnc <|
  .prod (.prod rite (.prod left .null)) <|
  .encodingExpr <|
  .un
    (Expr.uniSetMapConst.call (.var 1))
    (Expr.uniSetMapConst.call (.var 0))

namespace TrisetFn
  /- ## Codes -/
  
  /-- A triset code expression from a code body. -/
  def setCodeExpr (body: Expr .basic): Expr .basic := .prod (.nat 0) body
  
  /-- A function code expression from a code body. -/
  def fnCodeExpr (body: Expr .basic): Expr .basic := .prod (.nat 1) body
  
  /- The code body expression of a triset code. -/
  def setCodeBodyExpr (code: Expr .basic): Expr .basic := code.call (.nat 0)
  
  /- The body expression of a function code. -/
  def fnCodeBodyExpr (code: Expr .basic): Expr .basic := code.call (.nat 1)
  
  /- ## Code body expressions -/
  
  /- The body of the empty triset. -/
  def emptyBodyExpr (dlEnc: Expr .basic): Expr .basic :=
    .prod dlEnc <| .prod .null <| .encodingExpr (.var 0)
  
  /- The body of `{elem}`, where `elem` is a TrisetFn code. -/
  def singletonBodyExpr (dlEnc elem: Expr .basic): Expr .basic :=
    .prod dlEnc <| .prod (.prod elem .null) <| .encodingExpr (.var 0)
  
  /-
    The body of the union of the trisets whose bodies are `left` and
    `rite`.
  -/
  def unionBodyExpr (dlEnc left rite: Expr .basic): Expr .basic :=
    uniSetMapIndex.un dlEnc left rite
  
  /-
    The body of the pair value `(a, b)`; `a` and `b` are code
    expressions. This is the body-level counterpart of
    `TrisetFnExpr.pair`,
    
    ```
      { {∅, {a}}, {{∅}, {{b}}} }
    ```
    
    (The Kuratowski definition of a pair is not well-behaved for
    non-classical trisets.)
  -/
  def pairBodyExpr (dlEnc a b: Expr .basic): Expr .basic :=
    let emptyCode := setCodeExpr (emptyBodyExpr dlEnc)
    let aCode := setCodeExpr (singletonBodyExpr dlEnc a)
    let bCode := setCodeExpr (singletonBodyExpr dlEnc b)
    let one :=
      unionBodyExpr dlEnc
        (singletonBodyExpr dlEnc emptyCode)
        (singletonBodyExpr dlEnc aCode)
    let two :=
      unionBodyExpr dlEnc
        (singletonBodyExpr dlEnc
          (setCodeExpr (singletonBodyExpr dlEnc emptyCode)))
        (singletonBodyExpr dlEnc
          (setCodeExpr (singletonBodyExpr dlEnc bCode)))
    unionBodyExpr dlEnc
      (singletonBodyExpr dlEnc (setCodeExpr one))
      (singletonBodyExpr dlEnc (setCodeExpr two))
  
  /- ## Code expressions -/
  
  /-- A triset code expression for the pair value `(a, b)`. -/
  def pairCodeExpr (dlEnc a b: Expr .basic): Expr .basic :=
    setCodeExpr (pairBodyExpr dlEnc a b)
  
  /- ## The conversion -/
  
  /-
    Represents the triset (`Set3`) of the codes `(0, pairBodyExpr x y)`
    of the pairs `(x, y)` that are members of the free variable 0
    (interpreted as entries of the graph of the function).
    
    Note the members are *codes of set-encoded pairs*, whereas the graph
    itself is a triset of raw pairs `(x, y)` of codes.
  -/
  def fnToSetExpr (dlEnc: Expr .basic): Expr .basic :=
    .arbUn <|
    .arbUn <|
    .ifThen
      (Expr.ir
        (Expr.prod (Expr.var 1) (Expr.var 0))
        -- Note: `call` introduces a quantifier.
        (Expr.uniSetMapConst.call (Expr.var 3)))
      (pairCodeExpr dlEnc (Expr.var 1) (Expr.var 0))
  
  /- Code body of `fnToSetExpr`. -/
  def fnToSetBodyExpr (dlEnc fBody: Expr .basic): Expr .basic :=
    .prod dlEnc <|
    .prod (.prod fBody .null) <|
    .encodingExpr (fnToSetExpr dlEnc)
  
  /- ## Tests -/
  
  /-
    Implicit conversion of a function to a triset (a set of input-output
    pairs; pairs are encoded as in `pairBodyExpr`), and identity on
    trisets.
    
    A function becomes the triset `{ (a, b) | (a, b) is a graph entry }`,
    with the pairs set-encoded.
  -/
  exposed def fnToSet (dlEnc f: Expr .basic): Expr .basic :=
    .un
      (setCodeExpr (setCodeBodyExpr f))
      (setCodeExpr (fnToSetBodyExpr dlEnc (fnCodeBodyExpr f)))
  
  /- ## Lemmas -/
  
end TrisetFn
