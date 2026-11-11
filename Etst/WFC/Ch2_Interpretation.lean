-- # Chapter 2: Interpretation of Expressions
module
public import Etst.WFC.Ch0_Set3
public import Etst.WFC.Ch1_ExprDefList
public import Etst.WFC.Utils.General.PointwiseOrder
public import Etst.WFC.Utils.Set3


namespace Etst

universe u


-- ## Section 0: Valuations

/-
  A valuation is a function from constants to trisets of values.
-/
exposed def Valuation (D: Type u) := Nat → Set3 D

namespace Valuation
  variable {D: Type u}
  /-
    In the empty valuation, every constant represents the empty
    triset.
  -/
  exposed def empty: Valuation D := fun _ => Set3.empty
  
  /-
    In the undetermined valuation, every constant represents
    the undetermined triset.
  -/
  exposed def undetermined: Valuation D := fun _ => Set3.undetermined
  
  /-
    In the full valuation, every constant represents the full
    triset.
  -/
  exposed def univ: Valuation D := fun _ => Set3.univ
  
  -- The approximation order on valuations is defined pointwise.
  @[expose, reducible]
  public def ordApx (D: Type u):
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ordApx D)
  
  -- The standard order on valuations is defined pointwise.
  @[expose, reducible]
  public def ordStd (D: Type u)
  :
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ordStd D)
  
  
  -- The lte relation of the approximation order is denoted using ⊑.
  public instance instSqle (D: Type u): SqLE (Valuation D) where
    le := (ordApx D).le
  
  -- The lt relation of the approximation order is denoted using ⊏.
  public instance instSqlt (D: Type u): SqLT (Valuation D) where
    lt := (ordApx D).lt
  
  -- The lte relation of the standard order is denoted using ≤.
  public instance instLe (D: Type u): LE (Valuation D) where
    le := (ordStd D).le
  
  -- The lt relation of the standard order is denoted using <.
  public instance instLt (D: Type u): LT (Valuation D) where
    lt := (ordStd D).lt
  
  
  exposed def ordStd.IsLeast
    (s: Set (Valuation D))
    (a: Valuation D)
  :
    Prop
  :=
    @_root_.IsLeast _ (ordStd D).toLE s a
  
  exposed def ordApx.IsLeast
    (s: Set (Valuation D))
    (a: Valuation D)
  :
    Prop
  :=
    @_root_.IsLeast _ (ordApx D).toLE s a
  
  exposed def ordStd.IsLUB
    (s: Set (Valuation D))
    (a: Valuation D)
  :
    Prop
  :=
    @_root_.IsLUB _ (ordStd D).toLE s a
  
  exposed def ordApx.IsLUB
    (s: Set (Valuation D))
    (a: Valuation D)
  :
    Prop
  :=
    @_root_.IsLUB _ (ordApx D).toLE s a
  
  
  /-
    The empty valuation is the least element of the standard
    order.
  -/
  public theorem ordStd.empty_least {D}:
    IsLeast (D := D) Set.univ empty
  := ⟨
    trivial,
    fun _v _valInFull _x => {
      defLe := nofun
      posLe := nofun
    }
  ⟩
  
  /-
    The undetermined valuation is the least element of the
    approximation order.
  -/
  public theorem ordApx.undetermined_least {D}:
    IsLeast (D := D) Set.univ undetermined
  := ⟨
    trivial,
    fun _v _valInFull _x => {
      defLe := nofun
      posLe _ _ := trivial
    }
  ⟩

  /-
    Returns the supremum of a chain of valuations under the
    standard order.
  -/
  noncomputable def ordStd.sup
    {ch}
    (isChain: IsChain (ordStd D).le ch)
  :
    Valuation D
  :=
    isChain.pointwiseSup (Set3.ordStd.isChainComplete D)
  
  theorem ordStd.sup_isLUB
    {ch}
    (isChain: IsChain (ordStd D).le ch)
  :
    IsLUB ch (ordStd.sup isChain)
  :=
    isChain.pointwiseSup_isLUB (Set3.ordStd.isChainComplete D)
  
  
  /-
    Returns the supremum of a chain of valuations under the
    approximation order.
  -/
  noncomputable def ordApx.sup
    {ch}
    (isChain: IsChain (ordApx D).le ch)
  :
    Valuation D
  :=
    isChain.pointwiseSup (Set3.ordApx.isChainComplete D)
  
  theorem ordApx.sup_isLUB
    {ch}
    (isChain: IsChain (ordApx D).le ch)
  :
    IsLUB ch (ordApx.sup isChain)
  :=
    isChain.pointwiseSup_isLUB (Set3.ordApx.isChainComplete D)
  
  
  -- The standard order is chain complete.
  public theorem ordStd.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ordStd D)
  :=
    fun _ isChain => ⟨sup isChain, sup_isLUB isChain⟩
  
  -- The approximation order is chain complete.
  public theorem ordApx.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ordApx D)
  :=
    fun _ isChain => ⟨sup isChain, sup_isLUB isChain⟩
  
end Valuation


-- ## Section 3: The Interpretation Function

public inductive Pair where
| null -- Null is considered an improper pair.
| pair (a b: Pair)


exposed def Expr.intpVar
  (fv: List Pair)
  (x: Nat)
:
  Set Pair
:=
  match fv[x]? with
  | .none => {}
  | .some p => {p}

exposed def ExprKind.Lane: ExprKind → Type
| .basic => Set3.Lane
| .lane => Unit

namespace ExprKind.Lane
  exposed def defLane: ExprKind.basic.Lane := Set3.Lane.defLane
  exposed def posLane: ExprKind.basic.Lane := Set3.Lane.posLane

  exposed def toggle
    {kind: ExprKind}
    (lane: kind.Lane)
  :
    kind.Lane
  :=
    match kind with
    | .basic => Set3.Lane.toggle lane
    | .lane => lane
end ExprKind.Lane

exposed def ExprKind.ConstTag.getLane
  {kind: ExprKind}
  (tag: kind.ConstTag)
  (lane: kind.Lane)
:
  Set3.Lane
:=
  match kind with
  | .basic => lane
  | .lane => tag

/-
  The interpretation of an expression is defined using two valuations
  we will call "background" and "context". Context is the "main"
  valuation that is used to interpret constants under an even number
  of complements, while background is used to interpret constants
  under an odd number of complements.
  
  This division allows retaining monotonicity of interpretation
  with respect to context (assuming a fixed background).
  When background and context are the same valuation, this
  definition reduces to the usual one with a single valuation.
  
  (Historical note: originally, expressions were defined relative
  to a signature, and the interpretation function took an algebra
  acting monotonically on sets of elements. The pair algebra with
  `null` and `pair _ _` was later baked into expressions because
  unfortunately, it made it a pain to recurse on them.
  See also: [ref][ref])
  
  [ref][https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/RFC.3A.20pattern.20matching.20on.20.28syntactically.20equal.29.20functions]
-/
exposed def Expr.intp {kind}
  (expr: Expr kind)
  (lane: kind.Lane)
  (b c: Valuation Pair)
  (fv: List Pair)
:
  Set Pair
:=
  match expr with
  | .const tag x => (c x).getLane (tag.getLane lane)
  | .var x => intpVar fv x
  | .null => {.null}
  | .prod left rite =>
    .ofPred fun p =>
      ∃ pL pR,
        p = .pair pL pR ∧
        pL ∈ left.intp lane b c fv ∧
        pR ∈ rite.intp lane b c fv
  | .ir left rite =>
    .ofPred fun p =>
      And
        (p ∈ left.intp lane b c fv)
        (p ∈ rite.intp lane b c fv)
  | .full body =>
    -- Contains all elements iff the body contains all elements.
    .ofPred fun _ => ∀ pB, pB ∈ body.intp lane b c fv
  | .compl body =>
    -- Note the swap of b and c.
    (body.intp lane.toggle c b fv).compl
  | .arbIr body =>
    .ofPred fun p => ∀ pX, p ∈ body.intp lane b c (pX :: fv)


-- A proof that definite membership implies possible membership.
public theorem Expr.triIntp_defLePos
  (expr: Expr .basic)
  {b c fv p}
  (isDef: p ∈ expr.intp .defLane b c fv)
:
  p ∈ expr.intp .posLane b c fv
:=
  match expr, isDef with
  | .const _ x, isDef => (c x).defLePos isDef
  | .var _, isDef => isDef
  | .null, isDef => isDef
  | .prod left rite, ⟨pl, pr, eq, isDefL, isDefR⟩ =>
    let ihL := triIntp_defLePos left isDefL
    let ihR := triIntp_defLePos rite isDefR
    ⟨pl, pr, eq, ihL, ihR⟩
  | .ir left rite, ⟨isDefL, isDefR⟩ => ⟨
      triIntp_defLePos left isDefL,
      triIntp_defLePos rite isDefR
    ⟩
  | .full body, isDef => fun pB =>
    triIntp_defLePos body (isDef pB)
  | .compl body, isDef => fun isPos =>
      isDef (triIntp_defLePos body isPos)
  | .arbIr body, isDef => fun pX =>
    triIntp_defLePos body (isDef pX)

/-
  A three-valued interpretation computes both lanes of a triset.
-/
exposed def Expr.triIntp
  (expr: Expr .basic)
  (b c: Valuation Pair)
  (fv: List Pair)
:
  Set3 Pair
:= {
  defMem := expr.intp .defLane b c fv
  posMem := expr.intp .posLane b c fv
  defLePos _ := triIntp_defLePos expr
}
-- Interpretation on definition lists is defined pointwise.
public abbrev DefList.intpDefs
  (dl: DefList)
  (b c: Valuation Pair)
:
  Valuation Pair
:=
  fun x => (dl.getDef x).triIntp b c []
