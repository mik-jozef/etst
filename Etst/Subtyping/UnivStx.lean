import Etst.Subtyping.Syntax.FiniteDefList

/-
  An experimental attempt to base a proof system on universality (proving
  type expressions denote the entire universe) rather than subsethood,
  which can be represented as `IsUniversal (~a | b)` instead of `a ⊆ b`.
  Conjecturally, this could be a simpler system, though I'm not at all sure.
-/

import Etst.Subtyping.SubsetStx

namespace Etst
open Expr


def MutIndDescriptor.hypothesifyUniv
  (mutDesc: MutIndDescriptor dl)
  (desc: InductionDescriptor dl)
:
  SingleLaneExpr
:=
  .un
    (.compl
      ((desc.expansion.toLane .posLane).replaceComplZeroVars mutDesc.hypothesis))
    desc.rite


def Set.Univ (s: Set T): Prop := ∀ x, s x

def DefList.Univ (dl: DefList) (expr: SingleLaneExpr): Prop :=
  Set.Univ (expr.intp [] dl.wfm)


-- Note: `A ⊆ B` is equivalent to (encodeable as) `Univ (~A | B)`.
inductive DefList.UnivStx (dl: DefList): SingleLaneExpr → Type

| excludedMiddle
    (expr: SingleLaneExpr)
  :
    -- A.k.a. `A ⊆ A`
    UnivStx dl (.un (.compl expr) expr)

-- TODO should this be somehow provable using induction?
| nullPair
    (univL: UnivStx dl l)
    (univR: UnivStx dl r)
  :
    UnivStx dl (.un .null (.pair l r))

| univUnL {l r: SingleLaneExpr} (u: UnivStx dl l): UnivStx dl (.un l r)
| univUnSymm (u: UnivStx dl (.un a b)): UnivStx dl (.un b a)

| univIr (ul: UnivStx dl l) (ur: UnivStx dl r): UnivStx dl (.ir l r)
| univIrSymm (u: UnivStx dl (.ir a b)): UnivStx dl (.ir b a)
| mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      UnivStx
        dl
        (desc.hypothesifyUniv desc[i]))
    (i: desc.Index)
  :
    dl.UnivStx
      (.un (.compl (.var .posLane desc[i].left))
      desc[i].rite)


namespace DefList.UnivStx
  def univUnR
    {l: SingleLaneExpr}
    (u: UnivStx dl r)
  :
    UnivStx dl (.un l r)
  :=
    univUnSymm (univUnL u)
  
  
  def induction
    (desc: InductionDescriptor dl)
    (premise:
      UnivStx
        dl
        (.un
          (.compl
            ((desc.expansion.toLane .posLane).replaceComplZeroVars fun _ x =>
              desc.hypothesis x (.var .posLane x)))
          desc.rite))
  :
    dl.UnivStx
      (.un
        (.compl (.var .posLane desc.left))
        desc.rite)
  :=
    mutInduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def simpleInduction
    (x: Nat)
    (exprIsClean: Expr.IsClean expr)
    (premise:
      UnivStx
        dl
        (.un
          (.compl
            (((dl.getDef x).toLane .posLane).replaceComplZeroVars fun _ xR =>
              if x = xR
              then .ir expr (.var .posLane xR)
              else (.var .posLane xR)))
          expr))
  :
    UnivStx dl (.un (.compl (.var .posLane x)) expr)
  :=
    induction
      {
        left := x,
        rite := expr,
        riteIsClean := exprIsClean,
        expansion := dl.getDef x,
        expandsInto := .rfl
      }
      premise
  
end DefList.UnivStx
