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


-- Semantic entailment.
abbrev PairDl.Subset (dl: PairDl) (a b: SingleLanePairExpr) :=
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


-- Syntactic entailment.
inductive PairDl.SubsetStx
  (dl: PairDl)
:
  SingleLanePairExpr → SingleLanePairExpr → Type

| null: SubsetStx dl null null
| pair
    (sl: SubsetStx dl al bl)
    (sr: SubsetStx dl ar br)
  :
    SubsetStx dl (pair al ar) (pair bl br)
| unL (s: SubsetStx dl a b) {r: SingleLanePairExpr}: SubsetStx dl a (un b r)
| unR (s: SubsetStx dl a b) {l: SingleLanePairExpr}: SubsetStx dl a (un l b)
| mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      SubsetStx
        dl
        (desc.hypothesify (desc[i].expansion.toLane .posLane))
        desc[i].rite)
    (i: desc.Index)
  :
    SubsetStx dl desc[i].exprLeft desc[i].exprRite
| mutCoinduction
    (desc: MutCoindDescriptor dl)
    (premises:
      (i: desc.Index) →
      SubsetStx
        dl
        desc[i].left
        (desc.hypothesify (desc[i].expansion.toLane .defLane)))
    (i: desc.Index)
  :
    SubsetStx dl desc[i].exprLeft desc[i].exprRite

namespace PairDl.SubsetStx
  def induction
    (desc: InductionDescriptor dl)
    (premise:
      SubsetStx
        dl
        ((desc.expansion.toLane .posLane).replacePosVars fun _ x =>
          desc.hypothesis x (.var .posLane x))
        desc.rite)
  :
    SubsetStx dl (.var .posLane desc.left) desc.rite
  :=
    mutInduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def coinduction
    (desc: CoinductionDescriptor dl)
    (premise:
      SubsetStx
        dl
        desc.left
        (.compl
          ((desc.expansion.toLane .defLane).replacePosVars fun _ x =>
            desc.hypothesis x (.var .defLane x))))
  :
    SubsetStx dl desc.left (.compl (.var .defLane desc.rite))
  :=
    mutCoinduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  
  def simpleInduction
    (left: Nat)
    (riteIsClean: Expr.IsClean rite)
    (premise:
      SubsetStx
        dl
        (((dl.getDef left).toLane .posLane).replacePosVars fun _ x =>
          if left = x then PairExpr.ir rite (.var .posLane x) else (.var .posLane x))
        rite)
  :
    SubsetStx dl (.var .posLane left) rite
  :=
    induction
      {
        left,
        rite,
        riteIsClean,
        expansion := dl.getDef left,
        expandsInto := .rfl
      }
      premise
  
  def simpleCoinduction
    (rite: Nat)
    (leftIsClean: Expr.IsClean left)
    (premise:
      SubsetStx
        dl
        left
        (.compl
          (((dl.getDef rite).toLane .defLane).replacePosVars fun _ x =>
            if rite = x then PairExpr.ir (.compl left) (.var .defLane x) else (.var .defLane x))))
  :
    SubsetStx dl left (.compl (.var .defLane rite))
  :=
    coinduction
      {
        left,
        rite,
        leftIsClean,
        expansion := dl.getDef rite,
        expandsInto := .rfl
      }
      premise
end PairDl.SubsetStx
