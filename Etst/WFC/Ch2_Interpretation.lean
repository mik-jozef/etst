-- # Chapter 2: Interpretation of Expressions

import Etst.WFC.Ch1_ExprDefList
import Etst.WFC.Utils.Set3

namespace Etst


-- ## Section 0: Valuations

/-
  A valuation is a function from variables to trisets of values.
-/
def Valuation D := Nat → Set3 D

namespace Valuation
  /-
    In the empty valuation, every variable represents the empty
    triset.
  -/
  def empty: Valuation D := fun _ => Set3.empty
  
  /-
    In the undetermined valuation, every variable represents
    the undetermined triset.
  -/
  def undetermined: Valuation D := fun _ => Set3.undetermined
  
  /-
    In the full valuation, every variable represents the full
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
    fun _val _valInFull _x => {
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
    fun _val _valInFull _x => {
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
  `ValVar` encodes some (usage-specific) relation between a variable
  and an element. For example, it may be used to represent the
  assertion that a certain variable contains a certain element in
  some valuation.
  
  That the variable `x` contains the element `d` may be denoted
  as `d ∈ x`.
-/
structure ValVar (D: Type*) where
  d: D
  x: Nat


-- ## Section 3: The Interpretation Function

inductive Pair where
| null -- Null is considered an improper pair.
| pair (a b: Pair)


inductive SingleLaneVarType
  | posLane
  | defLane
deriving DecidableEq

def SingleLaneVarType.toggle:
  SingleLaneVarType → SingleLaneVarType
  | .posLane => .defLane
  | .defLane => .posLane

def SingleLaneVarType.getSet
  (lane: SingleLaneVarType)
  (s3: Set3 T)
:
  Set T
:=
  match lane with
  | .posLane => s3.posMem
  | .defLane => s3.defMem


def SingleLaneExpr := Expr SingleLaneVarType

/-
  The interpretation of an expression is defined using two valuations
  we will call "background" and "context". Context is the "main"
  valuation that is normally used to interpret the variables in the
  expression. Background is used to interpret complements and their
  subexpressions. In particular,
  
      (Expr.compl expr).interpretation b c
  
  is defined in terms of
  
      expr.interpretation b b \,.
  
  When background and context are the same valuation, this
  definition reduces to the usual one with a single valuation.
-/
def SingleLaneExpr.interpretation
  (bv: List Pair)
  (b c: Valuation Pair)
:
  SingleLaneExpr → Set Pair

| .var lane a => lane.getSet (c a)
| .bvar a =>
    match bv[a]? with
    | none => {}
    | some d => {d}
| .null => {.null}
| .pair left rite =>
    fun d => ∃ dL dR,
      d = .pair dL dR ∧
      interpretation bv b c left dL ∧
      interpretation bv b c rite dR
| .un left rite =>
    fun d =>
      Or
        (interpretation bv b c left d)
        (interpretation bv b c rite d)
| .ir left rite =>
    fun d =>
      And
        (interpretation bv b c left d)
        (interpretation bv b c rite d)
| .condSome body =>
    fun _ => ∃ dB, interpretation bv b c body dB
| .condFull body =>
    fun _ => ∀ dB, interpretation bv b c body dB
| .compl body => (interpretation bv b b body).compl
| .arbUn body =>
    fun d => ∃ dX, interpretation (dX :: bv) b c body d
| .arbIr body =>
    fun d => ∀ dX, interpretation (dX :: bv) b c body d


-- Note the lane gets toggled inside complements.
def BasicExpr.toLane
  (expr: BasicExpr)
  (lane: SingleLaneVarType)
:
  SingleLaneExpr
:=
  match expr with
  | .var a => .var lane a
  | .bvar a => .bvar a
  | .null => .null
  | .pair left rite => .pair (left.toLane lane) (rite.toLane lane)
  | .un left rite => .un (left.toLane lane) (rite.toLane lane)
  | .ir left rite => .ir (left.toLane lane) (rite.toLane lane)
  | .condSome body => .condSome (body.toLane lane)
  | .condFull body => .condFull (body.toLane lane)
  | .compl body => .compl (body.toLane lane.toggle)
  | .arbUn body => .arbUn (body.toLane lane)
  | .arbIr body => .arbIr (body.toLane lane)

def BasicExpr.toDefLane (expr: BasicExpr): SingleLaneExpr :=
  expr.toLane .defLane

def BasicExpr.toPosLane (expr: BasicExpr): SingleLaneExpr :=
  expr.toLane .posLane

def BasicExpr.interpretationDef
  (bv: List Pair)
  (b c: Valuation Pair)
  (expr: BasicExpr)
:
  Set Pair
:=
  (expr.toLane .defLane).interpretation bv b c

def BasicExpr.interpretationPos
  (bv: List Pair)
  (b c: Valuation Pair)
  (expr: BasicExpr)
:
  Set Pair
:=
  (expr.toLane .posLane).interpretation bv b c

-- A proof that definite membership implies possible membership.
def BasicExpr.interpretation_defLePos
  (bv: List Pair)
  (b c: Valuation Pair)
:
  (expr: BasicExpr) →
  (d: Pair) →
  expr.interpretationDef bv b c d →
  expr.interpretationPos bv b c d
| .var x, _, isDef => (c x).defLePos isDef
| .bvar _, _, isDef => isDef
| .null, _, isDef => isDef
| .pair left rite, _, ⟨pl, pr, eq, isDefL, isDefR⟩ =>
    let ihL := interpretation_defLePos bv b c left pl isDefL
    let ihR := interpretation_defLePos bv b c rite pr isDefR
    ⟨pl, pr, eq, ihL, ihR⟩
| .un left _, d, Or.inl isDef =>
    Or.inl (interpretation_defLePos bv b c left d isDef)
| .un _ rite, d, Or.inr isDef =>
    Or.inr (interpretation_defLePos bv b c rite d isDef)
| .ir left rite, d, ⟨isDefL, isDefR⟩ => ⟨
    interpretation_defLePos bv b c left d isDefL,
    interpretation_defLePos bv b c rite d isDefR
  ⟩
| .condSome body, _d, ⟨dB, isDef⟩ =>
    ⟨dB, interpretation_defLePos bv b c body dB isDef⟩
| .condFull body, _d, isDef => fun dB =>
    interpretation_defLePos bv b c body dB (isDef dB)
| .compl body, d, isDef => fun isPos =>
    let ih := interpretation_defLePos bv b b body d
    isDef (ih isPos)
| .arbUn body, d, ⟨dX, isDef⟩ =>
    ⟨dX, interpretation_defLePos (dX :: bv) b c body d isDef⟩
| .arbIr body, d, isDef => fun dX =>
    interpretation_defLePos (dX :: bv) b c body d (isDef dX)

/-
  A three-valued interpretation is an intuitive extension of single-lane
  expressions -- the definite members of an expression are defined in
  terms of the definite members of its subexpressions, and the same
  applies to the possible members.
  
  An interesting exception is the complement, where `d` is a
  definite member of the complement of `expr` iff `d` is not
  a *possible* member of `expr`, and vice versa. This is handled
  in `toLane` by toggling the lane of variables inside complements.
-/
def BasicExpr.interpretation
  (bv: List Pair)
  (b c: Valuation Pair)
  (expr: BasicExpr)
:
  Set3 Pair
:= {
  defMem := expr.interpretationDef bv b c,
  posMem := expr.interpretationPos bv b c,
  defLePos := interpretation_defLePos bv b c expr
}

-- Interpretation on definition lists is defined pointwise.
def DefList.interpretation
  (b c: Valuation Pair)
  (dl: DefList)
:
  Valuation Pair
:=
  fun x => (dl.getDef x).interpretation [] b c
