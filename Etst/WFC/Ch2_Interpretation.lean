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

def SingleLaneExpr.intp2Bvar
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
  valuation that is normally used to interpret the variables in the
  expression. Background is used to interpret complements and their
  subexpressions. In particular,
  
      (Expr.compl expr).intp2 b c
  
  is defined in terms of
  
      expr.intp2 b b \,.
  
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
  | .var lane a => lane.getSet (c a)
  | .bvar x => intp2Bvar bv x
  | .null => {.null}
  | .pair left rite =>
      fun d => ∃ dL dR,
        d = .pair dL dR ∧
        intp2 left bv b c dL ∧
        intp2 rite bv b c dR
  | .un left rite =>
      fun d =>
        Or
          (intp2 left bv b c d)
          (intp2 rite bv b c d)
  | .ir left rite =>
      fun d =>
        And
          (intp2 left bv b c d)
          (intp2 rite bv b c d)
  | .condSome body =>
      fun _ => ∃ dB, intp2 body bv b c dB
  | .condFull body =>
      fun _ => ∀ dB, intp2 body bv b c dB
  | .compl body => (intp2 body bv b b).compl
  | .arbUn body =>
      fun d => ∃ dX, intp2 body (dX :: bv) b c d
  | .arbIr body =>
      fun d => ∀ dX, intp2 body (dX :: bv) b c d

def SingleLaneExpr.intp
  (expr: SingleLaneExpr)
  (bv: List Pair)
  (v: Valuation Pair)
:=
  expr.intp2 bv v v

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
  (bv: List Pair)
  (b c: Valuation Pair)
  (d: Pair)
  (isDef: expr.triIntp2Def bv b c d)
:
  expr.triIntp2Pos bv b c d
:=
  match expr, isDef with
  | .var x, isDef => (c x).defLePos isDef
  | .bvar _, isDef => isDef
  | .null, isDef => isDef
  | .pair left rite, ⟨pl, pr, eq, isDefL, isDefR⟩ =>
      let ihL := triIntp2_defLePos left bv b c pl isDefL
      let ihR := triIntp2_defLePos rite bv b c pr isDefR
      ⟨pl, pr, eq, ihL, ihR⟩
  | .un left _, Or.inl isDef =>
      Or.inl (triIntp2_defLePos left bv b c d isDef)
  | .un _ rite, Or.inr isDef =>
      Or.inr (triIntp2_defLePos rite bv b c d isDef)
  | .ir left rite, ⟨isDefL, isDefR⟩ => ⟨
      triIntp2_defLePos left bv b c d isDefL,
      triIntp2_defLePos rite bv b c d isDefR
    ⟩
  | .condSome body, ⟨dB, isDef⟩ =>
      ⟨dB, triIntp2_defLePos body bv b c dB isDef⟩
  | .condFull body, isDef => fun dB =>
      triIntp2_defLePos body bv b c dB (isDef dB)
  | .compl body, isDef => fun isPos =>
      let ih := triIntp2_defLePos body bv b b d
      isDef (ih isPos)
  | .arbUn body, ⟨dX, isDef⟩ =>
      ⟨dX, triIntp2_defLePos body (dX :: bv) b c d isDef⟩
  | .arbIr body, isDef => fun dX =>
      triIntp2_defLePos body (dX :: bv) b c d (isDef dX)

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
def BasicExpr.triIntp2
  (expr: BasicExpr)
  (bv: List Pair)
  (b c: Valuation Pair)
:
  Set3 Pair
:= {
  defMem := expr.triIntp2Def bv b c,
  posMem := expr.triIntp2Pos bv b c,
  defLePos := triIntp2_defLePos expr bv b c
}

abbrev BasicExpr.triIntp
  (expr: BasicExpr)
  (bv: List Pair)
  (v: Valuation Pair)
:=
  expr.triIntp2 bv v v

-- Interpretation on definition lists is defined pointwise.
def DefList.triIntp2
  (b c: Valuation Pair)
  (dl: DefList)
:
  Valuation Pair
:=
  fun x => (dl.getDef x).triIntp2 [] b c

abbrev DefList.triIntp
  (v: Valuation Pair)
  (dl: DefList)
:=
  dl.triIntp2 v v
