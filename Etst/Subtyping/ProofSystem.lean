/-
  Here we attempt to create a proof system for showing subsethood
  among expressions, when interpreted in a given definition list.
  
  The proof system is later proven sound with respect to a strict
  notion of subsethood -- see `IsDefSubset`.
  
  TODO describe induction and coinduction:
  A ⊆ B may be proved by any of:
  0. s A ⊆ B (unfolding A)
  1. s B ⊆ B (induction on A)
  2. s (A & B) ⊆ B (not implied by, but a moral combination of the above two)
  3. A ⊆ t B (unfolding B, eq to `A ⊆ ~(t' B')`, `A ⊆ ~(t' ~B)`)
  4. A ⊆ t A (coinduction on "B", or precisely on t)
  5. A ⊆ t (A | B)) (combination of 3 and 4, eq to `A ⊆ ~(t' (~A & B'))`)
  
  TODO emphasize somewhere that induction/coinduction is built with the
  idea that our inductive structures are in the possible lane, while
  coinductive structures are in the definite lane.
-/

import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

namespace Etst
open PairExpr


abbrev PairDl.IsDefSubset (dl: PairDl) (a b: SingleLanePairExpr) :=
  Set.Subset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
abbrev PairDl.IsPosSubset (dl: PairDl) (a b: SingleLanePairExpr) :=
  Set.Subset (a.intp [] dl.wfm) (b.intp [] dl.wfm)


def Expr.replacePosVars
  (e: Expr E sig)
  (replacer: E → Nat → Expr E sig)
:
  Expr E sig
:=
  match e with
  | var i x => replacer i x
  | bvar x => .bvar x
  | op o args => op o fun param => (args param).replacePosVars replacer
  | compl body => compl body -- Note: no replacing in complements.
  | arbUn body => arbUn (body.replacePosVars replacer)
  | arbIr body => arbIr (body.replacePosVars replacer)


-- Represents an inductive proof of `var .posLane left ⊆ rite`
structure InductionDescriptor (dl: PairDl) where
  left: Nat
  rite: SingleLanePairExpr
  riteIsClean: rite.IsClean
  expansion: BasicPairExpr
  expandsInto: ExpandsInto dl (dl.getDef left) expansion

-- Represents a coinductive proof of `left ⊆ var .defLane rite`
structure CoinductionDescriptor (dl: PairDl) where
  left: SingleLanePairExpr
  rite: Nat
  leftIsClean: left.IsClean
  expansion: BasicPairExpr
  expandsInto: ExpandsInto dl (dl.getDef rite) expansion

abbrev MutIndDescriptor (dl: PairDl) := List (InductionDescriptor dl)
abbrev MutCoindDescriptor (dl: PairDl) := List (CoinductionDescriptor dl)

def InductionDescriptor.hypothesis
  (x: Nat)
  (desc: InductionDescriptor dl)
  (expr: SingleLanePairExpr)
:
  SingleLanePairExpr
:=
  if desc.left = x then ir desc.rite expr else expr

def CoinductionDescriptor.hypothesis
  (x: Nat)
  (desc: CoinductionDescriptor dl)
  (expr: SingleLanePairExpr)
:
  SingleLanePairExpr
:=
  if desc.rite = x then ir (.compl desc.left) expr else expr

def MutIndDescriptor.hypothesis
  (desc: MutIndDescriptor dl)
  -- Because the hypothesis is only applied to positive variables,
  -- which are always possible-lane (see `InductionDescriptor`),
  -- we can ignore the lane type here.
  (_: SingleLaneVarType)
  (x: Nat)
:
  SingleLanePairExpr
:=
  desc.foldr (InductionDescriptor.hypothesis x) (.var .posLane x)

def MutCoindDescriptor.hypothesis
  (desc: MutCoindDescriptor dl)
  -- We can ignore the lane analogously to `MutIndDescriptor.hypothesis`.
  (_: SingleLaneVarType)
  (x: Nat)
:
  SingleLanePairExpr
:=
  desc.foldr (CoinductionDescriptor.hypothesis x) (.var .defLane x)

def MutIndDescriptor.hypothesify
  (desc: MutIndDescriptor dl)
  (expr: SingleLanePairExpr)
:
  SingleLanePairExpr
:=
  expr.replacePosVars desc.hypothesis

def MutCoindDescriptor.hypothesify
  (desc: MutCoindDescriptor dl)
  (expr: SingleLanePairExpr)
:
  SingleLanePairExpr
:=
  .compl (expr.replacePosVars desc.hypothesis)

def InductionDescriptor.exprLeft
  (desc: InductionDescriptor dl)
:
  SingleLanePairExpr
:=
  .var .posLane desc.left

def CoinductionDescriptor.exprLeft
  (desc: CoinductionDescriptor dl)
:
  SingleLanePairExpr
:=
  desc.left

def InductionDescriptor.exprRite
  (desc: InductionDescriptor dl)
:
  SingleLanePairExpr
:=
  desc.rite

def CoinductionDescriptor.exprRite
  (desc: CoinductionDescriptor dl)
:
  SingleLanePairExpr
:=
  .compl (.var .defLane desc.rite)

inductive Subset
  (dl: PairDl)
:
  SingleLanePairExpr → SingleLanePairExpr → Type

| null: Subset dl null null
| pair
    (sl: Subset dl al bl)
    (sr: Subset dl ar br)
  :
    Subset dl (pair al ar) (pair bl br)
| unL (s: Subset dl a b) {r: SingleLanePairExpr}: Subset dl a (un b r)
| unR (s: Subset dl a b) {l: SingleLanePairExpr}: Subset dl a (un l b)
| mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      Subset
        dl
        (desc.hypothesify (desc[i].expansion.toLane .posLane))
        desc[i].rite)
    (i: desc.Index)
  :
    Subset dl desc[i].exprLeft desc[i].exprRite
| mutCoinduction
    (desc: MutCoindDescriptor dl)
    (premises:
      (i: desc.Index) →
      Subset
        dl
        desc[i].left
        (desc.hypothesify (desc[i].expansion.toLane .defLane)))
    (i: desc.Index)
  :
    Subset dl desc[i].exprLeft desc[i].exprRite


def Subset.induction
  (desc: InductionDescriptor dl)
  (premise:
    Subset
      dl
      ((desc.expansion.toLane .posLane).replacePosVars fun _ x =>
        desc.hypothesis x (.var .posLane x))
      desc.rite)
:
  Subset dl (.var .posLane desc.left) desc.rite
:=
  Subset.mutInduction
    [desc]
    (fun | ⟨0, _⟩ => premise)
    ⟨0, Nat.zero_lt_succ _⟩

def Subset.coinduction
  (desc: CoinductionDescriptor dl)
  (premise:
    Subset
      dl
      desc.left
      (.compl
        ((desc.expansion.toLane .defLane).replacePosVars fun _ x =>
          desc.hypothesis x (.var .defLane x))))
:
  Subset dl desc.left (.compl (.var .defLane desc.rite))
:=
  Subset.mutCoinduction
    [desc]
    (fun | ⟨0, _⟩ => premise)
    ⟨0, Nat.zero_lt_succ _⟩


def Subset.simpleInduction
  (left: Nat)
  (riteIsClean: Expr.IsClean rite)
  (premise:
    Subset
      dl
      (((dl.getDef left).toLane .posLane).replacePosVars fun _ x =>
        if left = x then PairExpr.ir rite (.var .posLane x) else (.var .posLane x))
      rite)
:
  Subset dl (.var .posLane left) rite
:=
  Subset.induction
    {
      left,
      rite,
      riteIsClean,
      expansion := dl.getDef left,
      expandsInto := .rfl
    }
    premise

def Subset.simpleCoinduction
  (rite: Nat)
  (leftIsClean: Expr.IsClean left)
  (premise:
    Subset
      dl
      left
      (.compl
        (((dl.getDef rite).toLane .defLane).replacePosVars fun _ x =>
          if rite = x then PairExpr.ir (.compl left) (.var .defLane x) else (.var .defLane x))))
:
  Subset dl left (.compl (.var .defLane rite))
:=
  Subset.coinduction
    {
      left,
      rite,
      leftIsClean,
      expansion := dl.getDef rite,
      expandsInto := .rfl
    }
    premise
