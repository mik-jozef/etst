-- # Chapter 2: Interpretation of Expressions

import Etst.WFC.Ch1_ExprDefList
import Etst.WFC.Utils.Set3

namespace Etst


-- ## Section 0: Valuations

/-
  A valuation is a function from constants to trisets of values.
-/
def Valuation D := Nat → Set3 D

namespace Valuation
  /-
    In the empty valuation, every constant represents the empty
    triset.
  -/
  def empty: Valuation D := fun _ => Set3.empty
  
  /-
    In the undetermined valuation, every constant represents
    the undetermined triset.
  -/
  def undetermined: Valuation D := fun _ => Set3.undetermined
  
  /-
    In the full valuation, every constant represents the full
    triset.
  -/
  def full: Valuation D := fun _ => Set3.full
  
  -- The approximation order on valuations is defined pointwise.
  def ordApx (D: Type u):
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ordApx D)
  
  -- The standard order on valuations is defined pointwise.
  def ordStd (D: Type u)
  :
    PartialOrder (Valuation D)
  :=
    PartialOrder.pointwise Nat (Set3.ordStd D)
  
  
  -- The lte relation of the approximation order is denoted using ⊑.
  instance instSqle (D: Type u): SqLE (Valuation D) where
    le := (ordApx D).le
  
  -- The lt relation of the approximation order is denoted using ⊏.
  instance instSqlt (D: Type u): SqLT (Valuation D) where
    lt := (ordApx D).lt
  
  -- The lte relation of the standard order is denoted using ≤.
  instance instLe (D: Type u): LE (Valuation D) where
    le := (ordStd D).le
  
  -- The lt relation of the standard order is denoted using <.
  instance instLt (D: Type u): LT (Valuation D) where
    lt := (ordStd D).lt
  
  
  def ordStd.IsLeast (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLeast _ (ordStd D).toLE s a
  
  def ordApx.IsLeast (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLeast _ (ordApx D).toLE s a
  
  def ordStd.IsLUB (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLUB _ (ordStd D).toLE s a
  
  def ordApx.IsLUB (s: Set (Valuation D)) (a: Valuation D): Prop :=
    @_root_.IsLUB _ (ordApx D).toLE s a
  
  
  /-
    The empty valuation is the least element of the standard
    order.
  -/
  def ordStd.empty_least {D}: IsLeast (D := D) Set.univ empty := ⟨
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
  def ordApx.undetermined_least {D}: IsLeast (D := D) Set.univ undetermined := ⟨
    trivial,
    fun _v _valInFull _x => {
      defLe := nofun
      posLe := fun _ _ => trivial
    }
  ⟩

  /-
    Returns the supremum of a chain of valuations under the
    standard order.
  -/
  noncomputable def ordStd.sup
    (isChain: IsChain (ordStd D).le ch)
  :
    Valuation D
  :=
    isChain.pointwiseSup (Set3.ordStd.isChainComplete D)
  
  def ordStd.sup_isLUB
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
    (isChain: IsChain (ordApx D).le ch)
  :
    Valuation D
  :=
    isChain.pointwiseSup (Set3.ordApx.isChainComplete D)
  
  def ordApx.sup_isLUB
    (isChain: IsChain (ordApx D).le ch)
  :
    IsLUB ch (ordApx.sup isChain)
  :=
    isChain.pointwiseSup_isLUB (Set3.ordApx.isChainComplete D)
  
  
  -- The standard order is chain complete.
  def ordStd.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ordStd D)
  :=
    fun _ isChain => ⟨sup isChain, sup_isLUB isChain⟩
  
  -- The approximation order is chain complete.
  def ordApx.isChainComplete (D: Type u)
  :
    IsChainComplete (Valuation.ordApx D)
  :=
    fun _ isChain => ⟨sup isChain, sup_isLUB isChain⟩
  
end Valuation

/-
  `ValConst` encodes some (usage-specific) relation between a constant
  and an element. For example, it may be used to represent the
  assertion that a certain constant contains a certain element in
  some valuation.
  
  That the constant `x` contains the element `d` may be denoted
  as `d ∈ x`.
-/
structure ValConst (D: Type*) where
  d: D
  x: Nat


-- ## Section 3: The Interpretation Function

inductive Pair where
| null -- Null is considered an improper pair.
| pair (a b: Pair)


abbrev SingleLaneExpr := Expr Set3.Lane

def SingleLaneExpr.intpVar
  (bv: List Pair)
  (x: Nat)
:
  Set Pair
:=
  match bv[x]? with
  | none => {}
  | some d => {d}

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
-/
def SingleLaneExpr.intp2
  (expr: SingleLaneExpr)
  (bv: List Pair)
  (b c: Valuation Pair)
:
  Set Pair
:=
  match expr with
  | .const lane x => (c x).getLane lane
  | .var x => intpVar bv x
  | .null => {.null}
  | .pair left rite =>
      fun d =>
        ∃ dL dR,
          d = .pair dL dR ∧
          intp2 left bv b c dL ∧
          intp2 rite bv b c dR
  | .ir left rite =>
      fun d =>
        And
          (intp2 left bv b c d)
          (intp2 rite bv b c d)
  | .condFull body =>
      fun _ => ∀ dB, intp2 body bv b c dB
  | .compl body =>
      -- Note the swap of b and c.
      (intp2 body bv c b).compl
  | .arbIr body =>
      fun d => ∀ dX, intp2 body (dX :: bv) b c d

abbrev SingleLaneExpr.intp
  (expr: SingleLaneExpr)
  (bv: List Pair)
  (v: Valuation Pair)
:=
  expr.intp2 bv v v


-- Note the lane gets toggled inside complements.
def BasicExpr.toLane
  (expr: BasicExpr)
  (lane: Set3.Lane)
:
  SingleLaneExpr
:=
  match expr with
  | .const a => .const lane a
  | .var a => .var a
  | .null => .null
  | .pair left rite => .pair (left.toLane lane) (rite.toLane lane)
  | .ir left rite => .ir (left.toLane lane) (rite.toLane lane)
  | .condFull body => .condFull (body.toLane lane)
  | .compl body => .compl (body.toLane lane.toggle)
  | .arbIr body => .arbIr (body.toLane lane)

def BasicExpr.toDefLane (expr: BasicExpr): SingleLaneExpr :=
  expr.toLane .defLane

def BasicExpr.toPosLane (expr: BasicExpr): SingleLaneExpr :=
  expr.toLane .posLane

def BasicExpr.triIntp2Def
  (expr: BasicExpr)
  (bv: List Pair)
  (b c: Valuation Pair)
:
  Set Pair
:=
  (expr.toLane .defLane).intp2 bv b c

def BasicExpr.triIntp2Pos
  (expr: BasicExpr)
  (bv: List Pair)
  (b c: Valuation Pair)
:
  Set Pair
:=
  (expr.toLane .posLane).intp2 bv b c

-- A proof that definite membership implies possible membership.
def BasicExpr.triIntp2_defLePos
  (expr: BasicExpr)
  (isDef: expr.triIntp2Def bv b c d)
:
  expr.triIntp2Pos bv b c d
:=
  match expr, isDef with
  | .const x, isDef => (c x).defLePos isDef
  | .var _, isDef => isDef
  | .null, isDef => isDef
  | .pair left rite, ⟨pl, pr, eq, isDefL, isDefR⟩ =>
      let ihL := triIntp2_defLePos left isDefL
      let ihR := triIntp2_defLePos rite isDefR
      ⟨pl, pr, eq, ihL, ihR⟩
  | .ir left rite, ⟨isDefL, isDefR⟩ => ⟨
      triIntp2_defLePos left isDefL,
      triIntp2_defLePos rite isDefR
    ⟩
  | .condFull body, isDef => fun dB =>
      triIntp2_defLePos body (isDef dB)
  | .compl body, isDef => fun isPos =>
      isDef (triIntp2_defLePos body isPos)
  | .arbIr body, isDef => fun dX =>
      triIntp2_defLePos body (isDef dX)

/-
  A three-valued interpretation is an intuitive extension of single-lane
  expressions -- the definite members of an expression are defined in
  terms of the definite members of its subexpressions, and the same
  applies to the possible members.
  
  An interesting exception is the complement, where `d` is a
  definite member of the complement of `expr` iff `d` is not
  a *possible* member of `expr`, and vice versa. This is handled
  in `toLane` by toggling the lane of constants inside complements.
-/
def BasicExpr.triIntp2
  (expr: BasicExpr)
  (bv: List Pair)
  (b c: Valuation Pair)
:
  Set3 Pair
:= {
  defMem := expr.triIntp2Def bv b c
  posMem := expr.triIntp2Pos bv b c
  defLePos _ := triIntp2_defLePos expr
}

abbrev BasicExpr.triIntp
  (expr: BasicExpr)
  (bv: List Pair)
  (v: Valuation Pair)
:=
  expr.triIntp2 bv v v

-- Interpretation on definition lists is defined pointwise.
def DefList.triIntp2
  (dl: DefList)
  (b c: Valuation Pair)
:
  Valuation Pair
:=
  fun x => (dl.getDef x).triIntp2 [] b c

abbrev DefList.triIntp
  (dl: DefList)
  (v: Valuation Pair)
:=
  dl.triIntp2 v v
