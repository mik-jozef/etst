import Etst.WFC.Utils.SubsetStx.Basic
import Etst.WFC.Syntax.FiniteDefList

namespace Etst
open Expr


pairDefList ExampleDl
  s3 Any := Ex x, x
  
  s3 Nat := null | (Nat, null)
  
  s3 NotNat :=
  | (Any, (Any, Any))
  | (NotNat, Any)

pairDefList.

local macro "s3(" e:s3_pair_expr ")" : term => `(s3(ExampleDl, $e))

def notNatDef := ExampleDl.defs.NotNat.toLane .posLane

def NotNat.notNat:
  ExampleDl.SubsetStx s3(.NotNat) s3(!.Nat)
:=
  .trans
    (.unfold .subId)
    (.complSwap -- complSwapping should not be necessary with coinduction.
      (.subSimpleInduction
        (show
          ExampleDl.SubsetStx
            (.un
              .null
              (.pair
                (.ir (.compl notNatDef) (.const .posLane 1))
                .null))
            (.compl notNatDef)
        from
          .complUn
            (.unElim
              .subId
              (.irCtxR
                (.irI
                  (.nullComplPair .subId)
                  (.nullComplPair .subId)))
              (.irCtxR
                (.irI
                  (.complRiteComplPair
                    (.subPairMono
                      .anyI
                      (.nullComplPair .subId)))
                  (.complLeftComplPair
                    (.subPairMono
                      (.irCtxL (.subCompl (.unfold .subId)))
                      .anyI))))))))


inductive IndCoindDescriptor.Type
| induction
| coinduction

/-
  Represents a (co)inductive proof of either
  
  ```
    const lane x ⊆ expr    (if induction)
    expr ⊆ ~const lane x   (if coinduction.)
  ```
-/
structure IndCoindDescriptor (dl: DefList) where
  type: IndCoindDescriptor.Type
  lane: Set3.Lane
  x: Nat
  expr: SingleLaneExpr
  expansion: BasicExpr
  expandsInto: dl.ExpandsInto true (dl.getDef x) expansion

namespace IndCoindDescriptor
  /-
    The `expr` field of the inductive descriptor obtained from a
    (co)inductive one. Coinductive descriptors get their `expr`
    complemented; inductive ones pass through.
  -/
  def Type.exprFor:
    IndCoindDescriptor.Type → SingleLaneExpr → SingleLaneExpr
  | .induction, e => e
  | .coinduction, e => .compl e
  
  def Type.premiseFor:
    IndCoindDescriptor.Type →
    (e: SingleLaneExpr) → (hypo: SingleLaneExpr) → SingleLaneExpr
  | .induction, e, hypo => impl hypo e
  | .coinduction, e, hypo => impl e (.compl hypo)
  
  def Type.conclusionFor:
    IndCoindDescriptor.Type →
    Set3.Lane → Nat → SingleLaneExpr → SingleLaneExpr
  | .induction, lane, x, e => impl (const lane x) e
  | .coinduction, lane, x, e => impl e (compl (const lane x))
  
  /-
    Converts a single coinductive descriptor into an inductive one
    by complementing the `expr` field on coinductive descriptors.
    
    This is the reduction underlying the coinduction principle: a
    coinductive proof of `expr ⊆ ~const lane x` is equivalent (by
    contraposition) to an inductive proof of `const lane x ⊆ ~expr`,
    which is what an inductive descriptor with `expr := ~original_expr`
    describes.
  -/
  def toIndDescriptor
    {dl} (d: IndCoindDescriptor dl)
  :
    InductionDescriptor dl
  := {
    lane := d.lane
    x := d.x
    expr := d.type.exprFor d.expr
    expansion := d.expansion
    expandsInto := d.expandsInto
  }
  
end IndCoindDescriptor


abbrev MutIndCoindDescriptor dl := List (IndCoindDescriptor dl)

namespace MutIndCoindDescriptor
  def toMutIndDescriptor
    {dl} (desc: MutIndCoindDescriptor dl)
  :
    MutIndDescriptor dl
  :=
    desc.map IndCoindDescriptor.toIndDescriptor

  def premise
    {dl} (desc: MutIndCoindDescriptor dl)
    (i: desc.Index)
  :
    SingleLaneExpr
  :=
    desc[i].type.premiseFor
      desc[i].expr
      (desc.toMutIndDescriptor.hypothesify
        0
        (desc[i].expansion.toLane desc[i].lane))

  def conclusion
    {dl} (desc: MutIndCoindDescriptor dl)
    (i: desc.Index)
  :
    SingleLaneExpr
  :=
    desc[i].type.conclusionFor desc[i].lane desc[i].x desc[i].expr
  
end MutIndCoindDescriptor


-- Mutual (co)induction principle.
def DefList.SubsetStx.mutIndCoind {dl x}
  (desc: MutIndCoindDescriptor dl)
  (premises: (i: desc.Index) → dl.SubsetStx x (full (desc.premise i)))
  (i: desc.Index)
:
  dl.SubsetStx x (full (desc.conclusion i))
:=
  /-
    The reduction strategy is:
    
    - Map each coinductive descriptor to an inductive one whose `expr`
      is the complement of the original (`toIndDescriptor`).
    - For each premise:
      - induction case: pass through unchanged.
      - coinduction case: from `expr ⊆ ~hypo`, derive `hypo ⊆ ~expr`
        via contraposition (`fullMono _ (contra subId)`) and remove
        the resulting double negation on the antecedent.
    - Apply `mutInduction`.
    - For the conclusion:
      - induction case: pass through.
      - coinduction case: from `const lane x ⊆ ~expr`, derive
        `expr ⊆ ~const lane x` via contraposition.
  -/
  let descMap: MutIndDescriptor dl := desc.toMutIndDescriptor
  let iMap: descMap.Index :=
    i.map IndCoindDescriptor.toIndDescriptor
  
  -- Element-wise correspondence between `descMap` and `desc`.
  let eqMap (j: desc.Index):
    Eq
      (descMap[j.map IndCoindDescriptor.toIndDescriptor])
      desc[j].toIndDescriptor
  :=
    List.getElem_map _
  
  let eqI: descMap[iMap] = desc[i].toIndDescriptor := eqMap i
  
  let mappedPremise (j: descMap.Index):
    dl.SubsetStx x
      (full
        (impl
          (descMap.hypothesify
            0
            (descMap[j].expansion.toLane descMap[j].lane))
          descMap[j].expr))
  :=
    let eqJ: descMap[j] = desc[j.unmap].toIndDescriptor := eqMap j.unmap
    let prem := premises j.unmap
    match h: desc[j.unmap].type with
    | .induction => by
      rw [eqJ]
      show dl.SubsetStx x (full (impl _ (desc[j.unmap].type.exprFor _)))
      rw [h]
      change
        dl.SubsetStx x (full (desc[j.unmap].type.premiseFor _ _))
      at prem
      rw [h] at prem
      exact prem
    | .coinduction => by
      rw [eqJ]
      show dl.SubsetStx x (full (impl _ (desc[j.unmap].type.exprFor _)))
      rw [h]
      change
        dl.SubsetStx x (full (desc[j.unmap].type.premiseFor _ _))
      at prem
      rw [h] at prem
      exact fullSubTransImpl (dni subId) (fullMono prem (contra subId))
  
  let conclusion := SubsetStx.mutInduction descMap mappedPremise iMap
  
  match h: desc[i].type with
  | .induction => by
    change dl.SubsetStx x (full (desc[i].type.conclusionFor _ _ _))
    rw [h]
    rw [eqI] at conclusion
    change
      dl.SubsetStx x (full (impl _ (desc[i].type.exprFor _)))
    at conclusion
    rw [h] at conclusion
    exact conclusion
  | .coinduction => by
    change dl.SubsetStx x (full (desc[i].type.conclusionFor _ _ _))
    rw [h]
    rw [eqI] at conclusion
    change
      dl.SubsetStx x (full (impl _ (desc[i].type.exprFor _)))
    at conclusion
    rw [h] at conclusion
    exact
      fullSubTransImpl (dni subId) (fullMono conclusion (contra subId))
