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
  
  Some wisdom for the future:
  Initially, I was only interested in creating a proof system for definite
  subsethood, ie. `∀ p, p ∈ A.posMem → p ∈ B.posMem`. However, I found that
  this notion of subsethood (strong as it is), does not permit any fixpoint
  reasoning.
  
  For example, let's say one wants to show `Nat ⊆ Nat`. Diretly, we cannot,
  because we may not assert for an arbitrary identifier that every its
  possible member is also its definite member. We may try to use induction,
  but while proving the inductive premise `succ (Nat & Nat) ⊆ succ Nat`,
  we run into the same problem.
  
  The issue here is that the inductive hypothesis `Nat` ought to be interpreted
  using definite membership, since for the "past" natural numbers, we were
  supposed to have already shown that their possible members are also their
  definite members. In a sense, definite subsethood is not closed under
  induction and coinduction.
  
  This leads us to a system where some variables are interpreted using
  possible membership, and some using definite membership. This system
  allows us to mix possible and definite subsethood arbitrarily. Definite
  subsethood is still the main notion of interest, but is no longer the
  only one.
-/

import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

namespace Etst
open Expr


def Expr.replaceComplZeroVars
  (e: Expr E)
  (replacer: E → Nat → Expr E)
:
  Expr E
:=
  match e with
  | var i x => replacer i x
  | bvar x => .bvar x
  | null => null
  | pair left rite =>
      pair
        (left.replaceComplZeroVars replacer)
        (rite.replaceComplZeroVars replacer)
  | un left rite =>
      un
        (left.replaceComplZeroVars replacer)
        (rite.replaceComplZeroVars replacer)
  | ir left rite =>
      ir
        (left.replaceComplZeroVars replacer)
        (rite.replaceComplZeroVars replacer)
  | condSome body =>
      condSome (body.replaceComplZeroVars replacer)
  | condFull body =>
      condFull (body.replaceComplZeroVars replacer)
  | compl body => compl body -- Note: no replacing in complements.
  | arbUn body => arbUn (body.replaceComplZeroVars replacer)
  | arbIr body => arbIr (body.replaceComplZeroVars replacer)


-- Represents an inductive proof of `var .posLane left ⊆ rite`
structure InductionDescriptor (dl: DefList) where
  left: Nat
  rite: SingleLaneExpr
  riteIsClean: rite.IsClean
  expansion: BasicExpr
  expandsInto: ExpandsInto dl (dl.getDef left) expansion

def InductionDescriptor.hypothesis
  (x: Nat)
  (desc: InductionDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  if desc.left = x then .ir desc.rite expr else expr

abbrev MutIndDescriptor (dl: DefList) := List (InductionDescriptor dl)

def MutIndDescriptor.hypothesis
  (desc: MutIndDescriptor dl)
  -- Because the hypothesis is only applied to positive variables,
  -- which are always possible-lane (see `InductionDescriptor`),
  -- we can ignore the lane type here.
  (_: SingleLaneVarType)
  (x: Nat)
:
  SingleLaneExpr
:=
  desc.foldr (InductionDescriptor.hypothesis x) (.var .posLane x)

def MutIndDescriptor.hypothesify
  (desc: MutIndDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  expr.replaceComplZeroVars desc.hypothesis


inductive ContextVariableKind
| cs
| ex
| uv

structure ContextVariable where
  kind: ContextVariableKind
  satisfies: SingleLaneExpr

/-
  Syntactic entailment. Note the similarities with propositional logic.
  Naming convention: subX for the "subset form" and just X for the
  "function form".
  
  Typical subset form: A ⊆ B.
  Typical function form: X ⊆ A → X ⊆ B.
  
  In function form, the left expression is interpreted as "context".
  Sometimes, this distinction is blurry.
-/
inductive DefList.SubsetStx
  (dl: DefList)
:
  List ContextVariable →
  SingleLaneExpr →
  SingleLaneExpr →
  Type
|
  subId {expr: SingleLaneExpr}: SubsetStx dl ctx expr expr
|
  subDefPos {x: Nat}:
    SubsetStx dl ctx (.var .defLane x) (.var .posLane x)
|
  subPair
    (sl: SubsetStx dl ctx al bl)
    (sr: SubsetStx dl ctx ar br)
  :
    SubsetStx dl ctx (.pair al ar) (.pair bl br)
|
  subUnL
    {a r: SingleLaneExpr}
  :
    SubsetStx dl ctx a (.un a r)
|
  subUnR
    {a l: SingleLaneExpr}
  :
    SubsetStx dl ctx a (.un l a)
|
  subUn
    (ac: SubsetStx dl ctx l b)
    (bc: SubsetStx dl ctx r b)
  :
    SubsetStx dl ctx (.un l r) b
|
  subIrL
    {a r: SingleLaneExpr}
  :
    SubsetStx dl ctx (.ir a r) a
|
  subIrR
    {a l: SingleLaneExpr}
  :
    SubsetStx dl ctx (.ir l a) a
|
  subIr
    (ac: SubsetStx dl ctx a l)
    (bc: SubsetStx dl ctx a r)
  :
    SubsetStx dl ctx a (.ir l r)
-- Distributivity of ir over un in "functional" form.
-- Can be used to derive implication elimination.
| unIr
    (subA: SubsetStx dl ctx x (.un al ar))
    (subB: SubsetStx dl ctx x b)
  :
    SubsetStx dl ctx x (.un (.ir al b) (.ir ar b))
|
  condSomeNull:
    SubsetStx dl ctx Expr.any (.condSome .null)
|
  condSomePair
    (sl: SubsetStx dl ctx Expr.any (.condSome l))
    (sr: SubsetStx dl ctx Expr.any (.condSome r))
  :
    SubsetStx dl ctx Expr.any (.condSome (.pair l r))
|
  condSomeSubTrans
    (ab: SubsetStx dl ctx a b)
    (sa: SubsetStx dl ctx Expr.any (.condSome a))
  :
    SubsetStx dl ctx Expr.any (.condSome b)
|
  condSomeUpgrade
    (sx: SubsetStx dl ctx Expr.any (.condSome a))
    (sub: SubsetStx dl ctx a (.condSome b))
  :
    SubsetStx dl ctx Expr.any (.condSome b)
|
  condFull
    (sub: SubsetStx dl ctx Expr.any e)
  :
    SubsetStx dl ctx Expr.any (.condFull e)
| condFullElim
    (sub: SubsetStx dl ctx Expr.any (.condFull e))
  :
    SubsetStx dl ctx Expr.any e
| condFullUpgrade
    (sx: SubsetStx dl ctx Expr.any (.condSome a))
    (sub: SubsetStx dl ctx a (.condFull b))
  :
    SubsetStx dl ctx Expr.any (.condFull b)
|
  subUnfold:
    SubsetStx
      dl
      ctx
      (.var lane a)
      ((dl.getDef a).toLane lane)
|
  subFold:
    SubsetStx
      dl
      ctx
      ((dl.getDef a).toLane lane)
      (.var lane a)
|
  trans
    (ab: SubsetStx dl ctx a b)
    (bc: SubsetStx dl ctx b c)
  :
    SubsetStx dl ctx a c
| -- excluded middle.
  em
    {a b: SingleLaneExpr}
  :
    SubsetStx dl ctx a (.un b b.compl)
| -- principle of explosion. Used as a basic rule instead of
  -- implication elimination, which is derived from this.
  subPe
    {a b: SingleLaneExpr}
  :
    SubsetStx dl ctx (.ir a a.compl) b
|
  mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      SubsetStx
        dl
        ctx
        (desc.hypothesify (desc[i].expansion.toLane .posLane))
        desc[i].rite)
    (i: desc.Index)
  :
    SubsetStx dl ctx (.var .posLane desc[i].left) desc[i].rite


namespace DefList.SubsetStx
  def toFn
    (ab: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx x a → SubsetStx dl ctx x b
  :=
    (trans · ab)
  
  def ofFn
    (_sub: SubsetStx dl ctx x a → SubsetStx dl ctx x b)
  :
    -- SubsetStx dl ctx a b
    Nat -- let's not accidentally use this.
  :=
    -- If this is true in the first place, it's gonna be hard to prove.
    42
  
  
  def pair
    (subL: SubsetStx dl ctx al bl)
    (subR: SubsetStx dl ctx ar br)
    (subP: SubsetStx dl ctx x (.pair al ar))
  :
    SubsetStx dl ctx x (.pair bl br)
  :=
    (subPair subL subR).toFn subP
  
  
  def unL
    {r: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx a (.un b r)
  :=
    sub.trans subUnL
  
  def unR
    {l: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx a (.un l b)
  :=
    sub.trans subUnR
  
  def subUnLR
    (subL: SubsetStx dl ctx al bl)
    (subR: SubsetStx dl ctx ar br)
  :
    SubsetStx dl ctx (.un al ar) (.un bl br)
  :=
    subUn subL.unL subR.unR
  
  def subUnSymm
    {l r: SingleLaneExpr}
  :
    SubsetStx dl ctx (.un l r) (.un r l)
  :=
    subUn subUnR subUnL
  
  def subUnElimL
    (sub: SubsetStx dl ctx (.un l r) b)
  :
    SubsetStx dl ctx l b
  :=
    trans subUnL sub
  
  def subUnElimR
    (sub: SubsetStx dl ctx (.un l r) b)
  :
    SubsetStx dl ctx r b
  :=
    trans subUnR sub
  
  def subUnSymmA
    (sub: SubsetStx dl ctx (.un l r) b)
  :
    SubsetStx dl ctx (.un r l) b
  :=
    subUn (subUnElimR sub) (subUnElimL sub)
  
  def unSymm
    (sub: SubsetStx dl ctx a (.un l r))
  :
    SubsetStx dl ctx a (.un r l)
  :=
    sub.trans subUnSymm
  
  def unElim
    (sub: SubsetStx dl ctx a (.un l r))
    (subL: SubsetStx dl ctx l b)
    (subR: SubsetStx dl ctx r b)
  :
    SubsetStx dl ctx a b
  :=
    sub.trans (subUn subL subR)
  
  
  def irL
    {r: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (.ir a r) b
  :=
    trans subIrL sub
  
  def irR
    {l: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (.ir l a) b
  :=
    trans subIrR sub
  
  def subIrLR
    (subL: SubsetStx dl ctx al bl)
    (subR: SubsetStx dl ctx ar br)
  :
    SubsetStx dl ctx (.ir al ar) (.ir bl br)
  :=
    subIr subL.irL subR.irR
  
  def subIrSymm
    {l r: SingleLaneExpr}
  :
    SubsetStx dl ctx (.ir l r) (.ir r l)
  :=
    subIr subIrR subIrL
  
  def irElimL
    (sub: SubsetStx dl ctx a (.ir l r))
  :
    SubsetStx dl ctx a l
  :=
    sub.trans subIrL
  
  def irElimR
    (sub: SubsetStx dl ctx a (.ir l r))
  :
    SubsetStx dl ctx a r
  :=
    sub.trans subIrR
  
  def subIrSymmA
    (sub: SubsetStx dl ctx (.ir l r) b)
  :
    SubsetStx dl ctx (.ir r l) b
  :=
    trans subIrSymm sub
  
  def irSymm
    (sub: SubsetStx dl ctx a (.ir l r))
  :
    SubsetStx dl ctx a (.ir r l)
  :=
    subIr (irElimR sub) (irElimL sub)
  
  def irMonoL
    (subA: SubsetStx dl ctx a al)
    (sub: SubsetStx dl ctx (.ir al ar) b)
  :
    SubsetStx dl ctx (.ir a ar) b
  :=
    trans (subIrLR subA subId) sub
  
  def irMonoR
    (subA: SubsetStx dl ctx a ar)
    (sub: SubsetStx dl ctx (.ir al ar) b)
  :
    SubsetStx dl ctx (.ir al a) b
  :=
    trans (subIrLR subId subA) sub
  
  
  def subIrUnDistL
    {dl ctx}
    {aul aur ar: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.ir (.un aul aur) ar)
      (.un (.ir aul ar) (.ir aur ar))
  :=
    unIr subIrL subIrR
  
  def subIrUnDistR
    {dl ctx}
    {al aur aul: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.ir al (.un aul aur))
      (.un (.ir al aul) (.ir al aur))
  :=
    trans
      (subIrSymmA
        subIrUnDistL)
        (subUnLR
          subIrSymm
          subIrSymm)
  
  def subIrUnDistElimL
    {dl ctx}
    {aul aur ar: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.un (.ir aul ar) (.ir aur ar))
      (.ir (.un aul aur) ar)
  :=
    subUn
      (subIr (irL subUnL) subIrR)
      (subIr (irL subUnR) subIrR)
  
  def subIrUnDistElimR
    {dl ctx}
    {al aur aul: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.un (.ir al aul) (.ir al aur))
      (.ir al (.un aul aur))
  :=
    subUn
      (subIr subIrL (irR subUnL))
      (subIr subIrL (irR subUnR))
  
  
  def subUnIrDistL
    {dl ctx}
    {ail air ar: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.un (.ir ail air) ar)
      (.ir (.un ail ar) (.un air ar))
  :=
    subUn
      (subIrLR subUnL subUnL)
      (subIr subUnR subUnR)
  
  def subUnIrDistR
    {dl ctx}
    {al air ail: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.un al (.ir ail air))
      (.ir (.un al ail) (.un al air))
  :=
    subUn
      (subIr subUnL subUnL)
      (subIrLR subUnR subUnR)
  
  def subUnIrDistElimL
    {dl ctx}
    {ail air ar: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.ir (.un ail ar) (.un air ar))
      (.un (.ir ail air) ar)
  :=
    subIrUnDistL.trans
      (subUn
        (subIrUnDistR.trans
          (subUn subUnL (irR subUnR)))
        (irL subUnR))
  
  def subUnIrDistElimR
    {dl ctx}
    {al air ail: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (.ir (.un al ail) (.un al air))
      (.un al (.ir ail air))
  :=
    subIrUnDistL.trans
      (subUn
        (irL subUnL)
        (subIrUnDistR.trans
          (subUn (irR subUnL) subUnR)))
  
  
  -- Aka implication introduction.
  def unComplIntro
    (sub: SubsetStx dl ctx (.ir l r) b)
  :
    SubsetStx dl ctx l (.un (.compl r) b)
  :=
    trans
      (trans (subIr subUnR em.unSymm) subUnIrDistElimR)
      (subUnLR subId sub)
  
  -- Aka implication elimination.
  def unComplElim
    (ab: SubsetStx dl ctx x a)
    (acbur: SubsetStx dl ctx x (.un (.compl a) b))
  :
    SubsetStx dl ctx x b
  :=
    trans
      (subIr ab acbur)
      (subIrUnDistR.trans (subUn subPe subIrR))
  
  def unElimOfCompl
    (ab: SubsetStx dl ctx x (a.compl))
    (acbur: SubsetStx dl ctx x (.un a b))
  :
    SubsetStx dl ctx x b
  :=
    trans
      (subIr ab acbur)
      (subIrUnDistR.trans (subUn subPe.subIrSymmA subIrR))
  
  -- Principle of explosion.
  def pe
    (subA: SubsetStx dl ctx x a)
    (subAc: SubsetStx dl ctx x a.compl)
  :
    SubsetStx dl ctx x b
  :=
    trans (subIr subA subAc) subPe
  
  
  def dne -- double negation elimination
    (sub: SubsetStx dl ctx a (.compl (.compl b)))
  :
    SubsetStx dl ctx a b
  :=
    unElimOfCompl sub em.unSymm
  
  def subCompl
    (ab: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx b.compl a.compl
  :=
    unElimOfCompl subId (em.trans (subUn ab.unL subUnR))
  
  def subComplElim
    (sub: SubsetStx dl ctx (.compl a) (.compl b))
  :
    SubsetStx dl ctx b a
  :=
    unComplElim subId (em.trans (subUn subUnR (unL sub)))
  
  def complComplA
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (.compl (.compl a)) b
  :=
    dne (subCompl (subCompl sub))
  
  def complComplElimA
    (sub: SubsetStx dl ctx (.compl (.compl a)) b)
  :
    SubsetStx dl ctx a b
  :=
    subComplElim sub.subCompl.dne
  
  def dni -- double negation introduction
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx a (.compl (.compl b))
  :=
    complComplElimA (subCompl (subCompl sub))
  
  def complSwapA
    (sub: SubsetStx dl ctx (.compl a) b)
  :
    SubsetStx dl ctx (.compl b) a
  :=
    subComplElim (dni sub)
  
  def complSwapB
    (sub: SubsetStx dl ctx a (.compl b))
  :
    SubsetStx dl ctx b (.compl a)
  :=
    subComplElim (complComplA sub)
  
  
  def subComplUn:
    SubsetStx dl ctx (.compl (.un l r)) (.ir (.compl l) (.compl r))
  :=
    subIr (subCompl subUnL) (subCompl subUnR)
  
  def subComplUnElim:
    SubsetStx dl ctx (.ir (.compl l) (.compl r)) (.compl (.un l r))
  :=
    complSwapB (subUn (complSwapB subIrL) (complSwapB subIrR))
  
  def complUn
    (sub: SubsetStx dl ctx a (.compl (.un l r)))
  :
    SubsetStx dl ctx a (.ir (.compl l) (.compl r))
  :=
    sub.trans subComplUn
  
  def complUnElim
    (sub: SubsetStx dl ctx a (.ir (.compl l) (.compl r)))
  :
    SubsetStx dl ctx a (.compl (.un l r))
  :=
    sub.trans subComplUnElim
  
  def complUnElimL
    (sub: SubsetStx dl ctx a (.compl (.un l r)))
  :
    SubsetStx dl ctx a (.compl l)
  :=
    irElimL (complUn sub)
  
  
  def unfoldA
      (sub: SubsetStx dl ctx (.var lane a) b)
    :
      SubsetStx dl ctx ((dl.getDef a).toLane lane) b
  :=
    trans subFold sub
  
  def unfoldB
      (sub: SubsetStx dl ctx a (.var lane b))
    :
      SubsetStx dl ctx a ((dl.getDef b).toLane lane)
  :=
    trans sub subUnfold
  
  def foldA
      (sub: SubsetStx dl ctx ((dl.getDef a).toLane lane) b)
    :
      SubsetStx dl ctx (.var lane a) b
  :=
    trans subUnfold sub
  
  def foldB
      (sub: SubsetStx dl ctx a ((dl.getDef b).toLane lane))
    :
      SubsetStx dl ctx a (.var lane b)
    :=
      trans sub subFold
  
  
  def induction
    (desc: InductionDescriptor dl)
    (premise:
      SubsetStx
        dl
        ctx
        ((desc.expansion.toLane .posLane).replaceComplZeroVars fun _ x =>
          desc.hypothesis x (.var .posLane x))
        desc.rite)
  :
    SubsetStx dl ctx (.var .posLane desc.left) desc.rite
  :=
    mutInduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def simpleInduction
    (left: Nat)
    (riteIsClean: Expr.IsClean rite)
    (premise:
      SubsetStx
        dl
        ctx
        (((dl.getDef left).toLane .posLane).replaceComplZeroVars fun _ x =>
          if left = x then .ir rite (.var .posLane x) else (.var .posLane x))
        rite)
  :
    SubsetStx dl ctx (.var .posLane left) rite
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
  
end DefList.SubsetStx


-- Semantic entailment.
abbrev DefList.Subset
  (dl: DefList)
  (a b: SingleLaneExpr)
:=
  Set.Subset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
