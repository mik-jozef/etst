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
import Etst.Subtyping.Utils.ExprLiftBvars
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

namespace Etst
open Expr


def Expr.replaceDepthEvenVars
  (e: Expr E)
  (depth: Nat) -- number of quantifiers crossed so far
  (ed: Bool) -- "even depth", number of complements crossed so far
  (replacer: (depth: Nat) → E → Nat → Expr E)
:
  Expr E
:=
  match e with
  | var i x => if ed then replacer depth i x else .var i x
  | bvar x => .bvar x
  | null => null
  | pair left rite =>
      pair
        (left.replaceDepthEvenVars depth ed replacer)
        (rite.replaceDepthEvenVars depth ed replacer)
  | ir left rite =>
      ir
        (left.replaceDepthEvenVars depth ed replacer)
        (rite.replaceDepthEvenVars depth ed replacer)
  | condFull body =>
      condFull (body.replaceDepthEvenVars depth ed replacer)
  | compl body =>
      compl (body.replaceDepthEvenVars depth (!ed) replacer)
  | arbIr body => arbIr (body.replaceDepthEvenVars (depth + 1) ed replacer)

-- Represents an inductive proof of `var .posLane left ⊆ rite`
structure InductionDescriptor (dl: DefList) where
  left: Nat
  rite: SingleLaneExpr
  expansion: BasicExpr
  expandsInto: ExpandsInto dl true (dl.getDef left) expansion

def InductionDescriptor.hypothesis
  (depth: Nat)
  (x: Nat)
  (desc: InductionDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  if desc.left = x then .ir (desc.rite.lift 0 depth) expr else expr

abbrev MutIndDescriptor (dl: DefList) := List (InductionDescriptor dl)

def MutIndDescriptor.hypothesis
  (desc: MutIndDescriptor dl)
  (depth: Nat)
  -- Because the hypothesis is only applied to positive variables,
  -- which are always possible-lane (see `InductionDescriptor`),
  -- we can ignore the lane type here.
  (_: Set3.Lane)
  (x: Nat)
:
  SingleLaneExpr
:=
  desc.foldr (InductionDescriptor.hypothesis depth x) (var .posLane x)

def MutIndDescriptor.hypothesify
  (desc: MutIndDescriptor dl)
  (depth := 0)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  expr.replaceDepthEvenVars depth true desc.hypothesis


inductive ContextVariableKind
| cst
| exi
| all

structure ContextVariable where
  kind: ContextVariableKind
  satisfies: SingleLaneExpr

/-
  Syntactic entailment. Note the similarities with propositional logic.
  Naming convention (rough rules of thumb):
  - subX if a basic rule (like ir intro), or "subset form"
  - just X for derived and/or more complex rules, or "function form"
  - fullX if of form `condFull x ⊆ y`
  - isFullX if of form `x ⊆ condFull y`
  - analogously for someX and isSomeX
  
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
    SubsetStx dl ctx (var .defLane x) (var .posLane x)
|
  subPair
    (sl: SubsetStx dl ctx al bl)
    (sr: SubsetStx dl ctx ar br)
  :
    SubsetStx dl ctx (pair al ar) (pair bl br)
|
  subIrL
    {a r: SingleLaneExpr}
  :
    SubsetStx dl ctx (ir a r) a
|
  subIrR
    {a l: SingleLaneExpr}
  :
    SubsetStx dl ctx (ir l a) a
|
  subIr
    (ac: SubsetStx dl ctx a l)
    (bc: SubsetStx dl ctx a r)
  :
    SubsetStx dl ctx a (ir l r)
|
  irUnDistL
    {a b c: SingleLaneExpr}
  :
    SubsetStx dl ctx (ir (un a b) c) (un (ir a c) (ir b c))
|
  subCompl
    {a b: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx b.compl a.compl
|
  dne
    {a: SingleLaneExpr}
  :
    SubsetStx dl ctx a.compl.compl a
|
  dni
    {a: SingleLaneExpr}
  :
    SubsetStx dl ctx a a.compl.compl
|
  isFull
    (subA: SubsetStx dl ctx Expr.any a)
  :
    SubsetStx dl ctx x (condFull a)
|
  -- Axiom K in modal logic.
  fullImplElim:
    SubsetStx
      dl
      ctx
      (condFull (impl a b))
      (impl (condFull a) (condFull b))
|
  -- Axiom T in modal logic.
  fullElim:
    SubsetStx dl ctx (condFull a) a
|
  /-
    The contraposition of Axiom 5 in modal logic, up to
    introducing a negation of `a`.
    
    This form is more convenient because proving it from 5
    requires double negation elimination, whereas proving
    5 from this just requires setting `a` to the complement
    of the desired expression. The axiom five is proven below
    as `someAddFull`.
  -/
  someStripFull:
    SubsetStx dl ctx (condSome (condFull a)) (condFull a)
|
  -- TODO should be provable with induction.
  unfold:
    SubsetStx
      dl
      ctx
      (var lane a)
      ((dl.getDef a).toLane lane)
|
  -- TODO is this provable with induction?
  fold:
    SubsetStx
      dl
      ctx
      ((dl.getDef a).toLane lane)
      (var lane a)
|
  trans
    (ab: SubsetStx dl ctx a b)
    (bc: SubsetStx dl ctx b c)
  :
    SubsetStx dl ctx a c
| -- principle of explosion. Used as a basic rule instead of
  -- implication elimination, which is derived from this.
  subPe
    {a b: SingleLaneExpr}
  :
    SubsetStx dl ctx (ir a a.compl) b
-- IsSingleton expr := (condSome expr) & (Ex p, condFull ~expr | p)
-- TODO these are adapted from logic, but are not general enougn, I think.
--   Logic has only `true = {*}` and `false = {}`, so it needs not deal
--   with the general case of non-subsingleton types.
-- note: replaceNextVar ought to bump bvars.
-- q: can I make a separate rule for replacing bvar using replaceNextVar?
-- existential introduction, sub form:
--   (body: SingleLaneExpr)
--   (IsSingleton t)
--   SubsetStx (body.replaceNextVar t) (Ex x, body)
-- existential elimination TODO this one is unfinished
--   (body: SingleLaneExpr)
--   (IsSingleton t)
--   SubsetStx body b
--   SubsetStx (arbUn body) b
-- universal elimination
--   (body: SingleLaneExpr)
--   (IsSingleton t)
--   SubsetStx (arbIr body) (body.replaceNextVar t)
-- universal introduction
--   (body: SingleLaneExpr)
--   (IsSingleton t)
--   SubsetStx (body.replaceNextVar t) (arbIr body)
|
  mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      SubsetStx
        dl
        ctx
        (desc.hypothesify 0 (desc[i].expansion.toLane .posLane))
        desc[i].rite)
    (i: desc.Index)
  :
    SubsetStx dl ctx (var .posLane desc[i].left) desc[i].rite


namespace DefList.SubsetStx
  def toFn
    (ab: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx x a → SubsetStx dl ctx x b
  :=
    (trans · ab)
  
  def ofFn
    (sub: ∀ x, SubsetStx dl ctx x a → SubsetStx dl ctx x b)
  :
    SubsetStx dl ctx a b
  :=
    sub a subId
  
  
  def subUnL
    {a r: SingleLaneExpr}
  :
    SubsetStx dl ctx a (un a r)
  :=
    dni.trans (subCompl subIrL)

  def subUnR
    {a l: SingleLaneExpr}
  :
    SubsetStx dl ctx a (un l a)
  :=
    dni.trans (subCompl subIrR)

  def subUn
    (ac: SubsetStx dl ctx l b)
    (bc: SubsetStx dl ctx r b)
  :
    SubsetStx dl ctx (un l r) b
  :=
    (subCompl (subIr (subCompl ac) (subCompl bc))).trans dne

  def em
    {a b: SingleLaneExpr}
  :
    SubsetStx dl ctx a (un b b.compl)
  :=
    dni.trans (subCompl subPe)
  
  
  def unL
    {r: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx a (un b r)
  :=
    sub.trans subUnL
  
  def unR
    {l: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx a (un l b)
  :=
    sub.trans subUnR
  
  def subUnLR
    (subL: SubsetStx dl ctx al bl)
    (subR: SubsetStx dl ctx ar br)
  :
    SubsetStx dl ctx (un al ar) (un bl br)
  :=
    subUn subL.unL subR.unR
  
  def subUnSymm
    {l r: SingleLaneExpr}
  :
    SubsetStx dl ctx (un l r) (un r l)
  :=
    subUn subUnR subUnL
  
  def subUnElimL
    (sub: SubsetStx dl ctx (un l r) b)
  :
    SubsetStx dl ctx l b
  :=
    trans subUnL sub
  
  def subUnElimR
    (sub: SubsetStx dl ctx (un l r) b)
  :
    SubsetStx dl ctx r b
  :=
    trans subUnR sub
  
  def subUnSymmA
    (sub: SubsetStx dl ctx (un l r) b)
  :
    SubsetStx dl ctx (un r l) b
  :=
    subUn (subUnElimR sub) (subUnElimL sub)
  
  def unSymm
    (sub: SubsetStx dl ctx a (un l r))
  :
    SubsetStx dl ctx a (un r l)
  :=
    sub.trans subUnSymm
  
  def unElim
    (sub: SubsetStx dl ctx a (un l r))
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
    SubsetStx dl ctx (ir a r) b
  :=
    trans subIrL sub
  
  def irR
    {l: SingleLaneExpr}
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (ir l a) b
  :=
    trans subIrR sub
  
  def subIrLR
    (subL: SubsetStx dl ctx al bl)
    (subR: SubsetStx dl ctx ar br)
  :
    SubsetStx dl ctx (ir al ar) (ir bl br)
  :=
    subIr subL.irL subR.irR
  
  def subIrSymm
    {l r: SingleLaneExpr}
  :
    SubsetStx dl ctx (ir l r) (ir r l)
  :=
    subIr subIrR subIrL
  
  def irElimL
    (sub: SubsetStx dl ctx a (ir l r))
  :
    SubsetStx dl ctx a l
  :=
    sub.trans subIrL
  
  def irElimR
    (sub: SubsetStx dl ctx a (ir l r))
  :
    SubsetStx dl ctx a r
  :=
    sub.trans subIrR
  
  def subIrSymmA
    (sub: SubsetStx dl ctx (ir l r) b)
  :
    SubsetStx dl ctx (ir r l) b
  :=
    trans subIrSymm sub
  
  def irSymm
    (sub: SubsetStx dl ctx a (ir l r))
  :
    SubsetStx dl ctx a (ir r l)
  :=
    subIr (irElimR sub) (irElimL sub)
  
  def irMonoL
    (subA: SubsetStx dl ctx a al)
    (sub: SubsetStx dl ctx (ir al ar) b)
  :
    SubsetStx dl ctx (ir a ar) b
  :=
    trans (subIrLR subA subId) sub
  
  def irMonoR
    (subA: SubsetStx dl ctx a ar)
    (sub: SubsetStx dl ctx (ir al ar) b)
  :
    SubsetStx dl ctx (ir al a) b
  :=
    trans (subIrLR subId subA) sub
  
  def subOfSubIr
    (subB: SubsetStx dl ctx a b)
    (subC: SubsetStx dl ctx (ir a b) c)
  :
    SubsetStx dl ctx a c
  :=
    trans (subIr subId subB) subC
  
  def unIr
    (subA: SubsetStx dl ctx x (un al ar))
    (subB: SubsetStx dl ctx x b)
  :
    SubsetStx dl ctx x (un (ir al b) (ir ar b))
  :=
    trans (subIr subA subB) irUnDistL
  
  def subIrUnDistR
    {dl ctx}
    {al aur aul: SingleLaneExpr}
  :
    SubsetStx
      dl
      ctx
      (ir al (un aul aur))
      (un (ir al aul) (ir al aur))
  :=
    trans
      (subIrSymmA
        irUnDistL)
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
      (un (ir aul ar) (ir aur ar))
      (ir (un aul aur) ar)
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
      (un (ir al aul) (ir al aur))
      (ir al (un aul aur))
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
      (un (ir ail air) ar)
      (ir (un ail ar) (un air ar))
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
      (un al (ir ail air))
      (ir (un al ail) (un al air))
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
      (ir (un ail ar) (un air ar))
      (un (ir ail air) ar)
  :=
    irUnDistL.trans
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
      (ir (un al ail) (un al air))
      (un al (ir ail air))
  :=
    irUnDistL.trans
      (subUn
        (irL subUnL)
        (subIrUnDistR.trans
          (subUn (irR subUnL) subUnR)))
  
  -- TODO finish once we can work with quantifiers.
  def subAny: SubsetStx dl ctx a Expr.any := sorry
  
  
  def implIntro
    (sub: SubsetStx dl ctx (ir l r) b)
  :
    SubsetStx dl ctx l (impl r b)
  :=
    trans
      (trans (subIr subUnR em.unSymm) subUnIrDistElimR)
      (subUnLR subId sub)
  
  def implElim
    (subImpl: SubsetStx dl ctx x (impl a b))
    (subA: SubsetStx dl ctx x a)
  :
    SubsetStx dl ctx x b
  :=
    trans
      (subIr subA subImpl)
      (subIrUnDistR.trans (subUn subPe subIrR))
  
  def implElimExact
    (subA: SubsetStx dl ctx a (impl a b))
  :
    SubsetStx dl ctx a b
  :=
    implElim subA subId
  
  def implAbsorb
    (subImpl: SubsetStx dl ctx x (impl a b))
  :
    SubsetStx dl ctx (ir x a) b
  :=
    irMonoL
      subImpl
      (trans
        irUnDistL
        (subUn (trans subIrSymm subPe) subIrL))
  
  def toImpl
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx x (impl a b)
  :=
    trans
      em
      (subUn
        (trans sub subUnR)
        subUnL)
  
  def ofImpl
    (sub: SubsetStx dl ctx Expr.any (impl a b))
  :
    SubsetStx dl ctx a b
  :=
    implElimExact (trans subAny sub)
  
  def unElimOfCompl
    (ab: SubsetStx dl ctx x (a.compl))
    (acbur: SubsetStx dl ctx x (un a b))
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
  
  
  def subComplElim
    (sub: SubsetStx dl ctx (compl a) (compl b))
  :
    SubsetStx dl ctx b a
  :=
    trans dni (trans (subCompl sub) dne)
  
  def complComplA
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (compl (compl a)) b
  :=
    dne.trans sub
  
  def complComplElimA
    (sub: SubsetStx dl ctx (compl (compl a)) b)
  :
    SubsetStx dl ctx a b
  :=
    dni.trans sub
  
  def complSwapA
    (sub: SubsetStx dl ctx (compl a) b)
  :
    SubsetStx dl ctx (compl b) a
  :=
    (subCompl sub).trans dne
  
  def complSwapB
    (sub: SubsetStx dl ctx a (compl b))
  :
    SubsetStx dl ctx b (compl a)
  :=
    dni.trans (subCompl sub)
  
  def subContra:
    SubsetStx dl ctx (impl a b) (impl (compl b) (compl a))
  :=
    trans subUnSymm (subUnLR dni subId)
  
  def contra
    (sub: SubsetStx dl ctx x (impl a b))
  :
    SubsetStx dl ctx x (impl (compl b) (compl a))
  :=
    toFn subContra sub
  
  
  def subComplUn:
    SubsetStx dl ctx (compl (un l r)) (ir (compl l) (compl r))
  :=
    subIr (subCompl subUnL) (subCompl subUnR)
  
  def subComplUnElim:
    SubsetStx dl ctx (ir (compl l) (compl r)) (compl (un l r))
  :=
    complSwapB (subUn (complSwapB subIrL) (complSwapB subIrR))
  
  def complUn
    (sub: SubsetStx dl ctx x (compl (un l r)))
  :
    SubsetStx dl ctx x (ir (compl l) (compl r))
  :=
    sub.trans subComplUn
  
  def complUnElim
    (sub: SubsetStx dl ctx x (ir (compl l) (compl r)))
  :
    SubsetStx dl ctx x (compl (un l r))
  :=
    sub.trans subComplUnElim
  
  def complUnElimL
    (sub: SubsetStx dl ctx x (compl (un l r)))
  :
    SubsetStx dl ctx x (compl l)
  :=
    irElimL (complUn sub)
  
  
  def fullElimOfImpl
    (fullAb: SubsetStx dl ctx Expr.any (condFull (impl a b)))
  :
    SubsetStx dl ctx (condFull a) (condFull b)
  :=
    implElimExact
      (trans subAny (trans fullAb fullImplElim))
  
  def isFullImpl
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx Expr.any (condFull (impl a b))
  :=
    isFull (toImpl sub)
  
  def isFullImplElim
    (sub: SubsetStx dl ctx Expr.any (condFull (impl a b)))
  :
    SubsetStx dl ctx a b
  :=
    ofImpl (trans sub fullElim)
  
  def fullMono
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (condFull a) (condFull b)
  :=
    fullElimOfImpl (isFullImpl sub)
  
  def fullDne:
    SubsetStx dl ctx (condFull (compl (compl a))) (condFull a)
  :=
    fullMono dne
  
  def fullDni:
    SubsetStx dl ctx (condFull a) (condFull (compl (compl a)))
  :=
    fullMono dni
  
  def complFullAntimono
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (compl (condFull b)) (compl (condFull a))
  :=
    subCompl (fullMono sub)
  
  
  def subSome:
    SubsetStx dl ctx a (condSome a)
  :=
    trans dni (subCompl fullElim)
  
  def someMono
    (sub: SubsetStx dl ctx a b)
  :
    SubsetStx dl ctx (condSome a) (condSome b)
  :=
    complFullAntimono (subCompl sub)
  
  
  def fullSome:
    SubsetStx dl ctx (condFull a) (condSome a)
  :=
    trans fullElim subSome
  
  def someElimFull
    (sub: SubsetStx dl ctx a (condFull b))
  :
    SubsetStx dl ctx (condSome a) (condFull b)
  :=
    trans (someMono sub) someStripFull
  
  def isFullUpgrade
    (isSomeA: SubsetStx dl ctx Expr.any (condSome a))
    (aFullB: SubsetStx dl ctx a (condFull b))
  :
    SubsetStx dl ctx Expr.any (condFull b)
  :=
    trans isSomeA (someElimFull aFullB)
  
  def someAddFull:
    SubsetStx dl ctx (condSome a) (condFull (condSome a))
  :=
    complSwapA someStripFull
  
  def fullAddSome:
    SubsetStx dl ctx (condFull a) (condSome (condFull a))
  :=
    subSome
  
  def someAddSome:
    SubsetStx dl ctx (condSome a) (condSome (condSome a))
  :=
    subSome
  
  def subFullSome:
    SubsetStx dl ctx a (condFull (condSome a))
  :=
    trans subSome someAddFull
  
  def fullAddFull:
    SubsetStx dl ctx (condFull a) (condFull (condFull a))
  :=
    trans subFullSome (fullMono someStripFull)
  
  def someElimComplFull
    (sub: SubsetStx dl ctx a (compl (condFull b)))
  :
    SubsetStx dl ctx (condSome a) (compl (condFull b))
  :=
    subCompl (trans fullAddFull (fullMono (complSwapB sub)))
  
  def someStripSome:
    SubsetStx dl ctx (condSome (condSome a)) (condSome a)
  :=
    subCompl (trans fullAddFull (fullMono dni))
  
  
  def condSomeNull:
    SubsetStx dl ctx Expr.any (condSome .null)
  :=
    sorry
  
  def condSomePair
    (sl: SubsetStx dl ctx Expr.any (condSome l))
    (sr: SubsetStx dl ctx Expr.any (condSome r))
  :
    SubsetStx dl ctx Expr.any (condSome (pair l r))
  :=
    sorry
  
  def isSomeMono
    (ab: SubsetStx dl ctx a b)
    (sa: SubsetStx dl ctx Expr.any (condSome a))
  :
    SubsetStx dl ctx Expr.any (condSome b)
  :=
    trans sa (someMono ab)
  
  def isSomeUpgrade
    (isSomeA: SubsetStx dl ctx Expr.any (condSome a))
    (aSomeB: SubsetStx dl ctx a (condSome b))
  :
    SubsetStx dl ctx Expr.any (condSome b)
  :=
    trans (isSomeMono aSomeB isSomeA) someStripSome
  
  
  def unfoldA
      (sub: SubsetStx dl ctx (var lane a) b)
    :
      SubsetStx dl ctx ((dl.getDef a).toLane lane) b
  :=
    trans fold sub
  
  def unfoldB
      (sub: SubsetStx dl ctx a (var lane b))
    :
      SubsetStx dl ctx a ((dl.getDef b).toLane lane)
  :=
    trans sub unfold
  
  def foldA
      (sub: SubsetStx dl ctx ((dl.getDef a).toLane lane) b)
    :
      SubsetStx dl ctx (var lane a) b
  :=
    trans unfold sub
  
  def foldB
      (sub: SubsetStx dl ctx a ((dl.getDef b).toLane lane))
    :
      SubsetStx dl ctx a (var lane b)
    :=
      trans sub fold
  
  
  def induction
    (desc: InductionDescriptor dl)
    (premise:
      SubsetStx
        dl
        ctx
        ((desc.expansion.toLane .posLane).replaceDepthEvenVars 0 true fun depth _ x =>
          desc.hypothesis depth x (var .posLane x))
        desc.rite)
  :
    SubsetStx dl ctx (var .posLane desc.left) desc.rite
  :=
    mutInduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def simpleInduction
    {left: Nat}
    {rite: SingleLaneExpr}
    (premise:
      SubsetStx
        dl
        ctx
        (((dl.getDef left).toLane .posLane).replaceDepthEvenVars 0 true fun depth _ x =>
          if left = x then .ir (rite.lift 0 depth) (var .posLane x) else (var .posLane x))
        rite)
  :
    SubsetStx dl ctx (var .posLane left) rite
  :=
    induction
      {
        left,
        rite,
        expansion := dl.getDef left,
        expandsInto := .rfl
      }
      premise
  
end DefList.SubsetStx


-- Semantic entailment.
abbrev DefList.SubsetBv
  (dl: DefList)
  (bv: List Pair)
  (a b: SingleLaneExpr)
:=
  Set.Subset (a.intp bv dl.wfm) (b.intp bv dl.wfm)

-- Semantic entailment.
abbrev DefList.Subset
  (dl: DefList)
  (a b: SingleLaneExpr)
:=
  ∀ bv, dl.SubsetBv bv a b
