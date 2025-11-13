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

abbrev Signature.Args
  (sig: Signature)
  (op: sig.Op)
  (D: Type u)
:=
  List.Vector (Set D) (sig.arity op)

/-
  A salgebra on T is an algebra on sets of T whose operations are
  monotonic.
  
  A salgebra with a signature `sig` provides an interpretation of
  each operation in the signature.
  
  The reason for using salgebras rather than algebras and defining
  the operations on sets in the standard manner (which would get
  us monotonicity for free) is that some operations, for example
  the dual of string concatenation, are not definable in this way.
  Take
      { '' } ⊙ {}      = { '' }.
      { 'a' } ⊙ {}     = {}.
      { '', 'a' } ⊙ {} = { '', 'a' }.
-/
structure Salgebra (sig: Signature) where
  D: Type u
  I: (op: sig.Op) → sig.Args op D → Set D
  isMonotonic
    (op: sig.Op)
    (args0 args1: sig.Args op D)
    (le: ∀ param, (h: param < sig.arity op) → args0[param] ≤ args1[param])
  :
    I op args0 ≤ I op args1


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


def SingleLaneExpr sig := Expr SingleLaneVarType sig


-- I'd rather use mutual recursion, but termination checking fails.
abbrev InterpretationRet (D: Type u): ExprKind → Type u
| .expr => Set D
| .args n => List.Vector (Set D) n

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
  (salg: Salgebra sig)
  (bv: List salg.D)
  (b c: Valuation salg.D)
:
  SingleLaneExpr sig kind → InterpretationRet salg.D kind

| .var lane a => lane.getSet (c a)
| .bvar a =>
    match bv[a]? with
    | none => ({}: Set salg.D)
    | some d => ({d}: Set salg.D)
| .op opr exprs =>
    salg.I opr (interpretation salg bv b c exprs)
| .compl body => (interpretation salg bv b b body).compl
| .arbUn body =>
    fun d => ∃ dX, interpretation salg (dX :: bv) b c body d
| .arbIr body =>
    fun d => ∀ dX, interpretation salg (dX :: bv) b c body d
| .nil => List.Vector.nil
| .cons head tail =>
    let headSet := interpretation salg bv b c head
    let tailSets := interpretation salg bv b c tail
    tailSets.cons headSet

-- Note the lane gets toggled inside complements.
def BasicExpr.toLane
  (expr: BasicExpr sig kind)
  (lane: SingleLaneVarType)
:
  SingleLaneExpr sig kind
:=
  match expr with
  | Expr.var _ a => .var lane a
  | .bvar a => .bvar a
  | .op opr exprs => .op opr (toLane exprs lane)
  | .compl body => .compl (body.toLane lane.toggle)
  | .arbUn body => .arbUn (body.toLane lane)
  | .arbIr body => .arbIr (body.toLane lane)
  | .nil => .nil
  | .cons head tail =>
      .cons (toLane head lane) (toLane tail lane)

def BasicExpr.toDefLane (expr: BasicExpr sig kind): SingleLaneExpr sig kind :=
  expr.toLane .defLane

def BasicExpr.toPosLane (expr: BasicExpr sig kind): SingleLaneExpr sig kind :=
  expr.toLane .posLane

def BasicExpr.interpretationDef
  (salg: Salgebra sig)
  (bv: List salg.D)
  (b c: Valuation salg.D)
  (expr: BasicExpr sig kind)
:
  InterpretationRet salg.D kind
:=
  (expr.toLane .defLane).interpretation salg bv b c

def BasicExpr.interpretationPos
  (salg: Salgebra sig)
  (bv: List salg.D)
  (b c: Valuation salg.D)
  (expr: BasicExpr sig kind)
:
  InterpretationRet salg.D kind
:=
  (expr.toLane .posLane).interpretation salg bv b c


def Interpretation_defLePosRet
  (salg: Salgebra sig)
  (bv: List salg.D)
  (b c: Valuation salg.D)
  (expr: BasicExpr sig kind)
:
  Prop
:=
  match kind with
  | .expr =>
      ∀ d,
      expr.interpretationDef salg bv b c d →
      expr.interpretationPos salg bv b c d
  | .args n =>
      ∀ i,
        (h: i < n) →
      ∀ d,
        (expr.interpretationDef salg bv b c)[i] d →
        (expr.interpretationPos salg bv b c)[i] d

-- A proof that definite membership implies possible membership.
def BasicExpr.interpretation_defLePos
  (salg: Salgebra sig)
  (bv: List salg.D)
  (b c: Valuation salg.D)
:
  (expr: BasicExpr sig kind) →
  Interpretation_defLePosRet salg bv b c expr
| Expr.var _ x => fun _ isDef => (c x).defLePos isDef
| .bvar _ => fun _ => id
| .op opr args =>
    salg.isMonotonic opr _ _ (interpretation_defLePos salg bv b c args)
| .compl body => fun d isDef isPos =>
    let ih := interpretation_defLePos salg bv b b body d
    isDef (ih isPos)
| .arbUn body => fun d ⟨dX, isDef⟩ =>
    ⟨dX, interpretation_defLePos salg (dX :: bv) b c body d isDef⟩
| .arbIr body => fun d isDef dX =>
    interpretation_defLePos salg (dX :: bv) b c body d (isDef dX)
| .nil => nofun
| .cons head tail =>
    let headLe := interpretation_defLePos salg bv b c head
    let tailLe := interpretation_defLePos salg bv b c tail
    fun
      | .zero, _, d => headLe d
      | .succ i', h, d => tailLe i' (Nat.lt_of_succ_lt_succ h) d

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
  (salg: Salgebra sig)
  (bv: List salg.D)
  (b c: Valuation salg.D)
  (expr: BasicExpr sig .expr)
:
  Set3 salg.D
:= {
  defMem := expr.interpretationDef salg bv b c,
  posMem := expr.interpretationPos salg bv b c,
  defLePos := interpretation_defLePos salg bv b c expr
}

-- Interpretation on definition lists is defined pointwise.
def DefList.interpretation
  (salg: Salgebra sig)
  (b c: Valuation salg.D)
  (dl: DefList sig)
:
  Valuation salg.D
:=
  fun x => (dl.getDef x).interpretation salg [] b c
