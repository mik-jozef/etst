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
  
-/

import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.PairExprMono

namespace Etst
open PairExpr


def IsDefSubset (a b: Set3 Pair) := ∀ ⦃p⦄, p ∈ a.posMem → p ∈ b.defMem
def IsPosSubset (a b: Set3 Pair) := ∀ ⦃p⦄, p ∈ a.defMem → p ∈ b.posMem

abbrev PairDl.IsDefSubset (dl: PairDl) (a b: PairExpr) :=
  Etst.IsDefSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
abbrev PairDl.IsPosSubset (dl: PairDl) (a b: PairExpr) :=
  Etst.IsPosSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)


def Expr.replacePosVars
  (e: Expr sig)
  (replacer: Nat → Expr sig)
:
  Expr sig
:=
  match e with
  | var x => replacer x
  | bvar x => .bvar x
  | op o args => op o fun param => (args param).replacePosVars replacer
  | cpl body => cpl body -- Note: no replacing in complements.
  | arbUn body => arbUn (body.replacePosVars replacer)
  | arbIr body => arbIr (body.replacePosVars replacer)


structure InductionDescriptor (dl: PairDl) where
  left: Nat
  rite: PairExpr
  riteIsClean: rite.IsClean
  expansion: PairExpr
  expandsInto: ExpandsInto dl (dl.getDef left) expansion

structure CoinductionDescriptor (dl: PairDl) where
  left: PairExpr
  rite: Nat
  leftIsClean: left.IsClean
  expansion: PairExpr
  expandsInto: ExpandsInto dl (dl.getDef rite) expansion

abbrev MutIndDescriptor (dl: PairDl) := List (InductionDescriptor dl)
abbrev MutCoindDescriptor (dl: PairDl) := List (CoinductionDescriptor dl)

def InductionDescriptor.hypothesis
  (x: Nat)
  (desc: InductionDescriptor dl)
  (expr: PairExpr)
:
  PairExpr
:=
  if desc.left = x then .ir desc.rite expr else expr

def CoinductionDescriptor.hypothesis
  (x: Nat)
  (desc: CoinductionDescriptor dl)
  (expr: PairExpr)
:
  PairExpr
:=
  if desc.rite = x then .ir (.cpl desc.left) expr else expr

def MutIndDescriptor.hypothesis
  (desc: MutIndDescriptor dl)
  (x: Nat)
:
  PairExpr
:=
  desc.foldr (InductionDescriptor.hypothesis x) (.var x)

def MutCoindDescriptor.hypothesis
  (desc: MutCoindDescriptor dl)
  (x: Nat)
:
  PairExpr
:=
  desc.foldr (CoinductionDescriptor.hypothesis x) (.var x)

def MutIndDescriptor.hypothesify
  (desc: MutIndDescriptor dl)
  (expr: PairExpr)
:
  PairExpr
:=
  expr.replacePosVars desc.hypothesis

def MutCoindDescriptor.hypothesify
  (desc: MutCoindDescriptor dl)
  (expr: PairExpr)
:
  PairExpr
:=
  .cpl (expr.replacePosVars desc.hypothesis)

def InductionDescriptor.exprLeft
  (desc: InductionDescriptor dl)
:
  PairExpr
:=
  .var desc.left

def CoinductionDescriptor.exprLeft
  (desc: CoinductionDescriptor dl)
:
  PairExpr
:=
  desc.left

def InductionDescriptor.exprRite
  (desc: InductionDescriptor dl)
:
  PairExpr
:=
  desc.rite

def CoinductionDescriptor.exprRite
  (desc: CoinductionDescriptor dl)
:
  PairExpr
:=
  .cpl (.var desc.rite)

inductive Subset
  (dl: PairDl)
:
  PairExpr → PairExpr → Type

| null: Subset dl .null .null
| pair
    (sl: Subset dl al bl)
    (sr: Subset dl ar br)
  :
    Subset dl (.pair al ar) (.pair bl br)
| unL (s: Subset dl a b) {r: PairExpr}: Subset dl a (.un b r)
| unR (s: Subset dl a b) {l: PairExpr}: Subset dl a (.un l b)
| induction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      Subset dl (desc.hypothesify desc[i].expansion) desc[i].rite)
    (i: desc.Index)
  :
    Subset dl desc[i].exprLeft desc[i].exprRite
| coinduction
    (desc: MutCoindDescriptor dl)
    (premises:
      (i: desc.Index) →
      Subset dl desc[i].left (desc.hypothesify desc[i].expansion))
    (i: desc.Index)
  :
    Subset dl desc[i].exprLeft desc[i].exprRite
