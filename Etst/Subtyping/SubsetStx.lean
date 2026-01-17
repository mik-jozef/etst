/-
  Here we attempt to create a proof system for showing subsethood
  among expressions, when interpreted in a given definition list.
  
  The proof system is later proven sound with respect to a strict
  notion of subsethood -- see `IsDefSubset`.
  
  TODO describe induction and coinduction:
  A ⊆ B may be proved by any of:
  0. s A ⊆ B (subUnfolding A)
  1. s B ⊆ B (induction on A)
  2. s (A & B) ⊆ B (not implied by, but a moral combination of the above two)
  3. A ⊆ t B (subUnfolding B, eq to `A ⊆ ~(t' B')`, `A ⊆ ~(t' ~B)`)
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
import Etst.Subtyping.Utils.ExprLiftVars
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

namespace Etst
open Expr

/-
  TODO: pair negation rule, splitting rule for condFull (un a b)
  
  can we prove this?:
  
  & condFull (un a b)
  & condFull (impl (ir c a) d)
  & condFull (impl (ir c b) d)
  -> d
-/

def Expr.replaceDepthEvenConsts
  (e: Expr E)
  (depth: Nat) -- number of quantifiers crossed so far
  (ed: Bool) -- "even depth", number of complements crossed so far
  (replacer: (depth: Nat) → E → Nat → Expr E)
:
  Expr E
:=
  match e with
  | const i x => if ed then replacer depth i x else .const i x
  | var x => .var x
  | null => null
  | pair left rite =>
      pair
        (left.replaceDepthEvenConsts depth ed replacer)
        (rite.replaceDepthEvenConsts depth ed replacer)
  | ir left rite =>
      ir
        (left.replaceDepthEvenConsts depth ed replacer)
        (rite.replaceDepthEvenConsts depth ed replacer)
  | condFull body =>
      condFull (body.replaceDepthEvenConsts depth ed replacer)
  | compl body =>
      compl (body.replaceDepthEvenConsts depth (!ed) replacer)
  | arbIr body => arbIr (body.replaceDepthEvenConsts (depth + 1) ed replacer)

-- Represents an inductive proof of `const lane x ⊆ expr`
structure InductionDescriptor (dl: DefList) where
  lane: Set3.Lane
  x: Nat
  expr: SingleLaneExpr
  expansion: BasicExpr
  expandsInto: ExpandsInto dl true (dl.getDef x) expansion

def InductionDescriptor.hypothesis
  (depth: Nat)
  (lane: Set3.Lane)
  (x: Nat)
  (desc: InductionDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  if lane.Le desc.lane && desc.x = x then .ir (desc.expr.lift 0 depth) expr else expr

abbrev MutIndDescriptor (dl: DefList) := List (InductionDescriptor dl)

def MutIndDescriptor.hypothesis
  (desc: MutIndDescriptor dl)
  (depth: Nat)
  (lane: Set3.Lane)
  (x: Nat)
:
  SingleLaneExpr
:=
  desc.foldr (InductionDescriptor.hypothesis depth lane x) (const lane x)

def MutIndDescriptor.hypothesify
  (desc: MutIndDescriptor dl)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  expr.replaceDepthEvenConsts 0 true desc.hypothesis


inductive ContextVariableKind
| cst
| exi
| all

structure ContextVariable where
  kind: ContextVariableKind
  satisfies: SingleLaneExpr

/-
  Syntactic entailment. Note the similarities with natural deduction.
  The left side is called context, the right side is called conclusion.
  
  Subset form: A ⊆ B. (No parameters.)
  Context form: X ⊆ A → X ⊆ B.
  
  Some rules are neither, because they take parameters (unlike the
  subset form), but also manipulate the context (unlike the context
  form).
  
  Naming conventions:
  - `subX` if subset form
  - just `X` if context form
  - `fullX` if of form `condFull x ⊆ y`
  - `isFullX` if of form `x ⊆ condFull y`
  - analogously for `someX` and `isSomeX`
  - context form rules where context is just a variable ought to
    call the context `x`.
  - rules that manipulate the context ought to have `ctx` in the
    name, with the exception of implication rules where context
    manipulation is expected (eg. implication introduction).
  
  TODO things to prove/axiomatize after we have quantifiers:
  - reconstruction:  ir e (pair any any)  ⊆  pair (zth e) (fst e)
  - projection l:  condSome b  ⊆  impl a (zth (pair a b))
  - projection r:  condSome a  ⊆  impl b (zth (pair a b))
  - monotonicity of projections
  - distribution of projections over ir, un, arbIr, arbUn
  - induction on pairs.
  - (condFull a)  ⊆  b  ->  condFull a  ⊆  condFull b
  - (a  ⊆  b  ->  a  ⊆  condFull b)  ->  condFull (impl a b)  ⊆  impl (condFull a) (condFull b)
  
  TODO make this a chapter, make IsFullStx an appendix.
-/
inductive DefList.SubsetStx
  (dl: DefList)
:
  List ContextVariable →
  SingleLaneExpr →
  SingleLaneExpr →
  Type
|
  subId {expr}: dl.SubsetStx ctx expr expr
|
  subDefPos {x}:
    dl.SubsetStx ctx (const .defLane x) (const .posLane x)
|
  pairMono
    (sl: dl.SubsetStx ctx x (condFull (impl al bl)))
    (sr: dl.SubsetStx ctx x (condFull (impl ar br)))
  :
    dl.SubsetStx ctx x (condFull (impl (pair al ar) (pair bl br)))
|
  subComplPairUn:
    dl.SubsetStx ctx
      (compl (pair a b))
      (un null (un (pair (compl a) any) (pair any (compl b))))
|
  subUnComplPair:
    dl.SubsetStx ctx
      (un null (un (pair (compl a) any) (pair any (compl b))))
      (compl (pair a b))
-- TODO is this one necessary?
| subPairIrDistL:
    dl.SubsetStx ctx (ir (pair a c) (pair b c)) (pair (ir a b) c)
-- TODO is this one necessary?
| subPairIrDistR:
    dl.SubsetStx ctx (ir (pair a b) (pair a c)) (pair a (ir b c))
| subIrL:
    dl.SubsetStx ctx (ir a r) a
| subIrR:
    dl.SubsetStx ctx (ir l a) a
| subIr
    (ac: dl.SubsetStx ctx x l)
    (bc: dl.SubsetStx ctx x r)
  :
    dl.SubsetStx ctx x (ir l r)
| -- TODO is this one necessary?
  subIrUnDistL:
    dl.SubsetStx ctx (ir (un a b) c) (un (ir a c) (ir b c))
|
  isFull
    (subA: dl.SubsetStx ctx any a)
  :
    dl.SubsetStx ctx x (condFull a)
|
  -- Axiom K in modal logic.
  fullImplElim:
    dl.SubsetStx
      ctx
      (condFull (impl a b))
      (impl (condFull a) (condFull b))
|
  -- Axiom T in modal logic.
  fullElim:
    dl.SubsetStx ctx (condFull a) a
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
    dl.SubsetStx ctx (condSome (condFull a)) (condFull a)
-- TODO is this one necessary?
-- | subCompl:
--     dl.SubsetStx ctx (ir (impl a b) (impl a b.compl)) a.compl
| -- TODO is this one necessary?
  implIntro
    (sub: dl.SubsetStx ctx (ir x a) b)
  :
    dl.SubsetStx ctx x (impl a b)
-- TODO is this one necessary?
-- | subDne: dl.SubsetStx ctx a.compl.compl a
-- TODO is this one necessary?
-- | subDni: dl.SubsetStx ctx a a.compl.compl
-- Principle of explosion. Used as a basic rule instead of
-- implication elimination, which is derived from this.
-- TODO is this one necessary?
| subPe:
    dl.SubsetStx ctx (ir a a.compl) b
-- TODO is this one necessary?
| subImplCompl:
    dl.SubsetStx ctx (impl a none) a.compl
    -- TODO subComplImpl, subImplElim (ir a (impl a b) ⊆ b)
-- IsSingleton expr := (condSome expr) & (Ex p, condFull ~expr | p)
-- TODO these are adapted from logic, but are not general enougn, I think.
--   Logic has only `true = {*}` and `false = {}`, so it needs not deal
--   with the general case of non-subsingleton types.
-- note: replaceNextVar ought to bump vars.
-- q: can I make a separate rule for replacing var using replaceNextVar?
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
-- | subArbIr {body}:
--   dl.SubsetStx ctx body (arbIr (body.lift 1))
-- | subArbIrElim
|
  trans
    (ab: dl.SubsetStx ctx a b)
    (bc: dl.SubsetStx ctx b c)
  :
    dl.SubsetStx ctx a c
| -- TODO should be provable with induction.
  subUnfold:
    dl.SubsetStx
      ctx
      (const lane a)
      ((dl.getDef a).toLane lane)
|
  -- TODO is this provable with induction?
  subFold:
    dl.SubsetStx
      ctx
      ((dl.getDef a).toLane lane)
      (const lane a)
|
  mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      dl.SubsetStx
        ctx
        x
        (condFull
          (impl
            (desc.hypothesify (desc[i].expansion.toLane desc[i].lane))
            desc[i].expr)))
    (i: desc.Index)
  :
    dl.SubsetStx
      ctx
      x
      (condFull (impl (const desc[i].lane desc[i].x) desc[i].expr))


namespace DefList.SubsetStx
  variable {dl: DefList}
  
  def toFn {x a b}
    (ab: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx x a → dl.SubsetStx ctx x b
  :=
    (trans · ab)
  
  def ofFn {a b}
    (sub: ∀ x, dl.SubsetStx ctx x a → dl.SubsetStx ctx x b)
  :
    dl.SubsetStx ctx a b
  :=
    sub a subId
  
  
  def irCtxL {a b r}
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx (ir a r) b
  :=
    trans subIrL sub
  
  def irCtxR {a b l}
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx (ir l a) b
  :=
    trans subIrR sub
  
  def irCtxLR
    (subL: dl.SubsetStx ctx al bl)
    (subR: dl.SubsetStx ctx ar br)
  :
    dl.SubsetStx ctx (ir al ar) (ir bl br)
  :=
    subIr subL.irCtxL subR.irCtxR
  
  def subIrSymm
    {l r: SingleLaneExpr}
  :
    dl.SubsetStx ctx (ir l r) (ir r l)
  :=
    subIr subIrR subIrL
  
  def irElimL
    (sub: dl.SubsetStx ctx x (ir l r))
  :
    dl.SubsetStx ctx x l
  :=
    sub.trans subIrL
  
  def irElimR
    (sub: dl.SubsetStx ctx x (ir l r))
  :
    dl.SubsetStx ctx x r
  :=
    sub.trans subIrR
  
  def irSymm
    (sub: dl.SubsetStx ctx x (ir l r))
  :
    dl.SubsetStx ctx x (ir r l)
  :=
    subIr (irElimR sub) (irElimL sub)
  
  def irSymmCtx
    (sub: dl.SubsetStx ctx (ir l r) b)
  :
    dl.SubsetStx ctx (ir r l) b
  :=
    trans subIrSymm sub
  
  def irMonoCtxL
    (subA: dl.SubsetStx ctx a al)
    (sub: dl.SubsetStx ctx (ir al ar) b)
  :
    dl.SubsetStx ctx (ir a ar) b
  :=
    trans (irCtxLR subA subId) sub
  
  def irMonoCtxR
    (subA: dl.SubsetStx ctx a ar)
    (sub: dl.SubsetStx ctx (ir al ar) b)
  :
    dl.SubsetStx ctx (ir al a) b
  :=
    trans (irCtxLR subId subA) sub
  
  
  def complIntro
    (sub: dl.SubsetStx ctx (ir x a) none)
  :
    dl.SubsetStx ctx x a.compl
  :=
    trans (implIntro sub) subImplCompl
  
  def subUnL {a r}:
    dl.SubsetStx ctx a (un a r)
  :=
    trans
      (implIntro
        (trans
          (irCtxLR subId subIrL)
          subPe))
      subImplCompl

  def subUnR {a l}:
    dl.SubsetStx ctx a (un l a)
  :=
    trans
      (implIntro
        (trans
          (irCtxLR subId subIrR)
          subPe))
      subImplCompl

  def unCtx {l r b}
    (ac: dl.SubsetStx ctx l b)
    (bc: dl.SubsetStx ctx r b)
  :
    dl.SubsetStx ctx (un l r) b
  :=
    (subCompl (subIr (subCompl ac) (subCompl bc))).trans subDne

  def em {x a}:
    dl.SubsetStx ctx x (un a a.compl)
  :=
    subDni.trans (subCompl subPe)
  
  def unL {x a b}
    (sub: dl.SubsetStx ctx x a)
  :
    dl.SubsetStx ctx x (un a b)
  :=
    sub.trans subUnL
  
  def unR {x a b}
    (sub: dl.SubsetStx ctx x b)
  :
    dl.SubsetStx ctx x (un a b)
  :=
    sub.trans subUnR
  
  def unCtxLR {al ar bl br}
    (subL: dl.SubsetStx ctx al bl)
    (subR: dl.SubsetStx ctx ar br)
  :
    dl.SubsetStx ctx (un al ar) (un bl br)
  :=
    unCtx subL.unL subR.unR
  
  def subUnSymm {l r}:
    dl.SubsetStx ctx (un l r) (un r l)
  :=
    unCtx subUnR subUnL
  
  def unElimCtxL {l r b}
    (sub: dl.SubsetStx ctx (un l r) b)
  :
    dl.SubsetStx ctx l b
  :=
    trans subUnL sub
  
  def unElimCtxR
    (sub: dl.SubsetStx ctx (un l r) b)
  :
    dl.SubsetStx ctx r b
  :=
    trans subUnR sub
  
  def unSymm
    (sub: dl.SubsetStx ctx x (un l r))
  :
    dl.SubsetStx ctx x (un r l)
  :=
    sub.trans subUnSymm
  
  def unSymmCtx
    (sub: dl.SubsetStx ctx (un l r) b)
  :
    dl.SubsetStx ctx (un r l) b
  :=
    unCtx (unElimCtxR sub) (unElimCtxL sub)
  
  def unElimSub
    (sub: dl.SubsetStx ctx x (un l r))
    (subL: dl.SubsetStx ctx l a)
    (subR: dl.SubsetStx ctx r a)
  :
    dl.SubsetStx ctx x a
  :=
    sub.trans (unCtx subL subR)
  
  def unMonoSubL
    (sub: dl.SubsetStx ctx x (un la r))
    (subL: dl.SubsetStx ctx la lb)
  :
    dl.SubsetStx ctx x (un lb r)
  :=
    unElimSub sub (unL subL) subUnR
  
  def unMonoSubR
    (sub: dl.SubsetStx ctx x (un l ra))
    (subR: dl.SubsetStx ctx ra rb)
  :
    dl.SubsetStx ctx x (un l rb)
  :=
    unElimSub sub subUnL (unR subR)
  
  def unIr
    (subA: dl.SubsetStx ctx x (un al ar))
    (subB: dl.SubsetStx ctx x b)
  :
    dl.SubsetStx ctx x (un (ir al b) (ir ar b))
  :=
    trans (subIr subA subB) subIrUnDistL
  
  
  def subIrUnDistR {al aur aul}:
    dl.SubsetStx
      ctx
      (ir al (un aul aur))
      (un (ir al aul) (ir al aur))
  :=
    trans
      (irSymmCtx
        subIrUnDistL)
        (unCtxLR
          subIrSymm
          subIrSymm)
  
  def subIrUnDistElimL {aul aur ar}:
    dl.SubsetStx
      ctx
      (un (ir aul ar) (ir aur ar))
      (ir (un aul aur) ar)
  :=
    unCtx
      (subIr (irCtxL subUnL) subIrR)
      (subIr (irCtxL subUnR) subIrR)
  
  def subIrUnDistElimR {al aur aul}:
    dl.SubsetStx
      ctx
      (un (ir al aul) (ir al aur))
      (ir al (un aul aur))
  :=
    unCtx
      (subIr subIrL (irCtxR subUnL))
      (subIr subIrL (irCtxR subUnR))
  
  
  def subUnIrDistL {ail air ar}:
    dl.SubsetStx
      ctx
      (un (ir ail air) ar)
      (ir (un ail ar) (un air ar))
  :=
    unCtx
      (irCtxLR subUnL subUnL)
      (subIr subUnR subUnR)
  
  def subUnIrDistR {al air ail}:
    dl.SubsetStx
      ctx
      (un al (ir ail air))
      (ir (un al ail) (un al air))
  :=
    unCtx
      (subIr subUnL subUnL)
      (irCtxLR subUnR subUnR)
  
  def subUnIrDistElimL {ail air ar: SingleLaneExpr}:
    dl.SubsetStx
      ctx
      (ir (un ail ar) (un air ar))
      (un (ir ail air) ar)
  :=
    subIrUnDistL.trans
      (unCtx
        (subIrUnDistR.trans
          (unCtx subUnL (irCtxR subUnR)))
        (irCtxL subUnR))
  
  def subUnIrDistElimR {al air ail}:
    dl.SubsetStx
      ctx
      (ir (un al ail) (un al air))
      (un al (ir ail air))
  :=
    subIrUnDistL.trans
      (unCtx
        (irCtxL subUnL)
        (subIrUnDistR.trans
          (unCtx (irCtxR subUnL) subUnR)))
  
  -- TODO finish once we can work with quantifiers.
  def subAny: dl.SubsetStx ctx a any := sorry
  def subNone: dl.SubsetStx ctx none a := sorry
  
  
  def implElim
    (subImpl: dl.SubsetStx ctx x (impl a b))
    (subA: dl.SubsetStx ctx x a)
  :
    dl.SubsetStx ctx x b
  :=
    trans
      (subIr subA subImpl)
      (subIrUnDistR.trans (unCtx subPe subIrR))
  
  def implElimExact
    (subA: dl.SubsetStx ctx a (impl a b))
  :
    dl.SubsetStx ctx a b
  :=
    implElim subA subId
  
  def implAbsorb
    (subImpl: dl.SubsetStx ctx x (impl a b))
  :
    dl.SubsetStx ctx (ir x a) b
  :=
    irMonoCtxL
      subImpl
      (trans
        subIrUnDistL
        (unCtx (trans subIrSymm subPe) subIrL))
  
  def toImpl
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx x (impl a b)
  :=
    trans
      em
      (unCtx
        (trans sub subUnR)
        subUnL)
  
  def ofImpl
    (sub: dl.SubsetStx ctx any (impl a b))
  :
    dl.SubsetStx ctx a b
  :=
    implElimExact (trans subAny sub)
  
  def unElimComplL
    (ab: dl.SubsetStx ctx x (un a b))
    (aCompl: dl.SubsetStx ctx x (a.compl))
  :
    dl.SubsetStx ctx x b
  :=
    trans
      (subIr aCompl ab)
      (subIrUnDistR.trans (unCtx subPe.irSymmCtx subIrR))
  
  def unElimComplR
    (ab: dl.SubsetStx ctx x (un a b))
    (bCompl: dl.SubsetStx ctx x (b.compl))
  :
    dl.SubsetStx ctx x a
  :=
    trans
      (subIr bCompl ab)
      (subIrUnDistR.trans (unCtx subIrR subPe.irSymmCtx))
  
  -- Principle of explosion.
  def pe
    (subA: dl.SubsetStx ctx x a)
    (subAc: dl.SubsetStx ctx x a.compl)
  :
    dl.SubsetStx ctx x b
  :=
    trans (subIr subA subAc) subPe
  
  
  def unElim
    (sub: dl.SubsetStx ctx x (un l r))
    (subL: dl.SubsetStx ctx x (impl l a))
    (subR: dl.SubsetStx ctx x (impl r a))
  :
    dl.SubsetStx ctx x a
  :=
    trans
      (trans (subIr sub subId) subIrUnDistL)
      (unCtx
        (trans subIrSymm (implAbsorb subL))
        (trans subIrSymm (implAbsorb subR)))
  
  def unMonoL
    (sub: dl.SubsetStx ctx x (un la r))
    (subL: dl.SubsetStx ctx x (impl la lb))
  :
    dl.SubsetStx ctx x (un lb r)
  :=
    unElim
      sub
      (implIntro (trans (implAbsorb subL) subUnL))
      (toImpl subUnR)
  
  def unMonoR
    (sub: dl.SubsetStx ctx x (un l ra))
    (subR: dl.SubsetStx ctx x (impl ra rb))
  :
    dl.SubsetStx ctx x (un l rb)
  :=
    unElim
      sub
      (toImpl subUnL)
      (implIntro (trans (implAbsorb subR) subUnR))
  
  
  def dne
    (sub: dl.SubsetStx ctx x (compl (compl a)))
  :
    dl.SubsetStx ctx x a
  :=
    trans sub subDne
  
  def dneCtx
    (sub: dl.SubsetStx ctx (compl (compl a)) b)
  :
    dl.SubsetStx ctx a b
  :=
    subDni.trans sub
  
  def dni
    (sub: dl.SubsetStx ctx x a)
  :
    dl.SubsetStx ctx x (compl (compl a))
  :=
    trans sub subDni
  
  def dniCtx
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx (compl (compl a)) b
  :=
    subDne.trans sub
  
  def subComplElim
    (sub: dl.SubsetStx ctx (compl a) (compl b))
  :
    dl.SubsetStx ctx b a
  :=
    trans subDni (trans (subCompl sub) subDne)
  
  def complSwapCtx
    (sub: dl.SubsetStx ctx (compl a) b)
  :
    dl.SubsetStx ctx (compl b) a
  :=
    (subCompl sub).trans subDne
  
  def complSwap
    (sub: dl.SubsetStx ctx a (compl b))
  :
    dl.SubsetStx ctx b (compl a)
  :=
    subDni.trans (subCompl sub)
  
  def subContra:
    dl.SubsetStx ctx (impl a b) (impl (compl b) (compl a))
  :=
    trans subUnSymm (unCtxLR subDni subId)
  
  def subContraElim
    {a b: SingleLaneExpr}
  :
    dl.SubsetStx ctx (impl a.compl b.compl) (impl b a)
  :=
    em.unElim
      (implIntro (unR subIrR))
      (implIntro (unL (implElim subIrL subIrR)))

  def contra
    (sub: dl.SubsetStx ctx x (impl a b))
  :
    dl.SubsetStx ctx x (impl (compl b) (compl a))
  :=
    toFn subContra sub
  
  def contraElim
    (sub: dl.SubsetStx ctx x (impl a.compl b.compl))
  :
    dl.SubsetStx ctx x (impl b a)
  :=
    toFn subContraElim sub
  
  
  def subComplUn:
    dl.SubsetStx ctx (compl (un l r)) (ir (compl l) (compl r))
  :=
    subIr (subCompl subUnL) (subCompl subUnR)
  
  def subComplUnElim:
    dl.SubsetStx ctx (ir (compl l) (compl r)) (compl (un l r))
  :=
    complSwap (unCtx (complSwap subIrL) (complSwap subIrR))
  
  def complUn
    (sub: dl.SubsetStx ctx x (compl (un l r)))
  :
    dl.SubsetStx ctx x (ir (compl l) (compl r))
  :=
    sub.trans subComplUn
  
  def complUnElim
    (sub: dl.SubsetStx ctx x (ir (compl l) (compl r)))
  :
    dl.SubsetStx ctx x (compl (un l r))
  :=
    sub.trans subComplUnElim
  
  def complUnElimL
    (sub: dl.SubsetStx ctx x (compl (un l r)))
  :
    dl.SubsetStx ctx x (compl l)
  :=
    irElimL (complUn sub)
  
  def complUnElimR
    (sub: dl.SubsetStx ctx x (compl (un l r)))
  :
    dl.SubsetStx ctx x (compl r)
  :=
    irElimR (complUn sub)
  
  
  def fullElimOfImpl
    (fullAb: dl.SubsetStx ctx any (condFull (impl a b)))
  :
    dl.SubsetStx ctx (condFull a) (condFull b)
  :=
    implElimExact
      (trans subAny (trans fullAb fullImplElim))
  
  def isFullImpl
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx any (condFull (impl a b))
  :=
    isFull (toImpl sub)
  
  def isFullImplElim
    (sub: dl.SubsetStx ctx any (condFull (impl a b)))
  :
    dl.SubsetStx ctx a b
  :=
    ofImpl (trans sub fullElim)
  
  def fullMono
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx (condFull a) (condFull b)
  :=
    fullElimOfImpl (isFullImpl sub)
  
  def fullDne:
    dl.SubsetStx ctx (condFull (compl (compl a))) (condFull a)
  :=
    fullMono subDne
  
  def fullDni:
    dl.SubsetStx ctx (condFull a) (condFull (compl (compl a)))
  :=
    fullMono subDni
  
  def complFullAntimono
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx (compl (condFull b)) (compl (condFull a))
  :=
    subCompl (fullMono sub)
  
  
  def subSome:
    dl.SubsetStx ctx a (condSome a)
  :=
    trans subDni (subCompl fullElim)
  
  def someMono
    (sub: dl.SubsetStx ctx a b)
  :
    dl.SubsetStx ctx (condSome a) (condSome b)
  :=
    complFullAntimono (subCompl sub)
  
  
  def fullSome:
    dl.SubsetStx ctx (condFull a) (condSome a)
  :=
    trans fullElim subSome
  
  def someElimFull
    (sub: dl.SubsetStx ctx a (condFull b))
  :
    dl.SubsetStx ctx (condSome a) (condFull b)
  :=
    trans (someMono sub) someStripFull
  
  def isFullUpgrade
    (isSomeA: dl.SubsetStx ctx any (condSome a))
    (aFullB: dl.SubsetStx ctx a (condFull b))
  :
    dl.SubsetStx ctx any (condFull b)
  :=
    trans isSomeA (someElimFull aFullB)
  
  def someAddFull:
    dl.SubsetStx ctx (condSome a) (condFull (condSome a))
  :=
    complSwapCtx someStripFull
  
  def fullAddSome:
    dl.SubsetStx ctx (condFull a) (condSome (condFull a))
  :=
    subSome
  
  def someAddSome:
    dl.SubsetStx ctx (condSome a) (condSome (condSome a))
  :=
    subSome
  
  def subFullSome:
    dl.SubsetStx ctx a (condFull (condSome a))
  :=
    trans subSome someAddFull
  
  def fullAddFull:
    dl.SubsetStx ctx (condFull a) (condFull (condFull a))
  :=
    trans subFullSome (fullMono someStripFull)
  
  def someElimComplFull
    (sub: dl.SubsetStx ctx a (compl (condFull b)))
  :
    dl.SubsetStx ctx (condSome a) (compl (condFull b))
  :=
    subCompl (trans fullAddFull (fullMono (complSwap sub)))
  
  def someStripSome:
    dl.SubsetStx ctx (condSome (condSome a)) (condSome a)
  :=
    subCompl (trans fullAddFull (fullMono subDni))
  
  
  def condSomeNull:
    dl.SubsetStx ctx any (condSome null)
  :=
    sorry
  
  def condSomePair
    (sl: dl.SubsetStx ctx any (condSome l))
    (sr: dl.SubsetStx ctx any (condSome r))
  :
    dl.SubsetStx ctx any (condSome (pair l r))
  :=
    sorry
  
  def isSomeMono
    (ab: dl.SubsetStx ctx a b)
    (sa: dl.SubsetStx ctx any (condSome a))
  :
    dl.SubsetStx ctx any (condSome b)
  :=
    trans sa (someMono ab)
  
  def isSomeUpgrade
    (isSomeA: dl.SubsetStx ctx any (condSome a))
    (aSomeB: dl.SubsetStx ctx a (condSome b))
  :
    dl.SubsetStx ctx any (condSome b)
  :=
    trans (isSomeMono aSomeB isSomeA) someStripSome
  
  
  def unfoldCtx
      (sub: dl.SubsetStx ctx (const lane a) b)
    :
      dl.SubsetStx ctx ((dl.getDef a).toLane lane) b
  :=
    trans subFold sub
  
  def unfold
      (sub: dl.SubsetStx ctx x (const lane a))
    :
      dl.SubsetStx ctx x ((dl.getDef a).toLane lane)
  :=
    trans sub subUnfold
  
  def foldCtx
      (sub: dl.SubsetStx ctx ((dl.getDef a).toLane lane) b)
    :
      dl.SubsetStx ctx (const lane a) b
  :=
    trans subUnfold sub
  
  def fold
      (sub: dl.SubsetStx ctx x ((dl.getDef a).toLane lane))
    :
      dl.SubsetStx ctx x (const lane a)
    :=
      trans sub subFold
  
  
  def implPairMono:
    dl.SubsetStx
      ctx
      any
      (impl
        (condFull (impl al bl))
        (impl
          (condFull (impl ar br))
          (impl (pair al ar) (pair bl br))))
  :=
    implIntro
      (implIntro
        (trans
          (pairMono (irCtxL subIrR) subIrR)
          fullElim))
  
  def pairMonoOfSub
    (sl: dl.SubsetStx ctx al bl)
    (sr: dl.SubsetStx ctx ar br)
  :
    dl.SubsetStx ctx (pair al ar) (pair bl br)
  :=
    ofImpl
      (implElim
        (implElim implPairMono (isFullImpl sl))
        (isFullImpl sr))
  
  
  def subMutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      dl.SubsetStx
        ctx
        (desc.hypothesify (desc[i].expansion.toLane desc[i].lane))
        desc[i].expr)
    (i: desc.Index)
  :
    dl.SubsetStx ctx (const desc[i].lane desc[i].x) desc[i].expr
  :=
    isFullImplElim
      (mutInduction desc (fun i => isFullImpl (premises i)) i)
  
  def subInduction
    (desc: InductionDescriptor dl)
    (premise:
      dl.SubsetStx
        ctx
        ((desc.expansion.toLane desc.lane).replaceDepthEvenConsts 0 true fun depth lane x =>
          desc.hypothesis depth lane x (const lane x))
        desc.expr)
  :
    dl.SubsetStx ctx (const desc.lane desc.x) desc.expr
  :=
    subMutInduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def subSimpleInduction {x lane expr}
    (premise:
      dl.SubsetStx
        ctx
        (((dl.getDef x).toLane lane).replaceDepthEvenConsts 0 true fun depth l xR =>
          if l.Le lane && x = xR then .ir (expr.lift 0 depth) (const l xR) else (const l xR))
        expr)
  :
    dl.SubsetStx ctx (const lane x) expr
  :=
    subInduction
      {
        x,
        lane,
        expr,
        expansion := dl.getDef x,
        expandsInto := .rfl
      }
      premise
  
  
  def implDist:
    dl.SubsetStx ctx (impl a (impl b c)) (impl (impl a b) (impl a c))
  :=
    .implIntro
      (.implIntro
        (.implElim
          (.implElim (irCtxL .subIrL) .subIrR)
          (.implElim (irCtxL .subIrR) .subIrR)))
  
  def subIrUnCompl {a b}:
    dl.SubsetStx ctx a (un (ir a b.compl) b)
  :=
    trans
      (subIr subUnR em)
      (trans subUnIrDistElimR subUnSymm)
  
  def subIrPairComplUnL {a b c}:
    dl.SubsetStx
      ctx
      (ir (pair (compl a) c) (pair (compl b) c))
      (pair (compl (un a b)) c)
  :=
    trans subPairIrDistL <|
    pairMonoOfSub subComplUnElim subId

  def subIrPairComplUnR {a b c}:
    dl.SubsetStx
      ctx
      (ir (pair a (compl b)) (pair a (compl c)))
      (pair a (compl (un b c)))
  :=
    trans subPairIrDistR <|
    pairMonoOfSub subId subComplUnElim

  def subPairUnDistL {a b c}:
    dl.SubsetStx ctx (pair (un a b) c) (un (pair a c) (pair b c))
  :=
    subComplElim <|
    trans subComplUn <|
    trans (irCtxLR subComplPairUn subComplPairUn) <|
    trans (irCtxLR subUnSymm subUnSymm) <|
    trans subUnIrDistElimL <|
    trans (unCtxLR
      (trans subUnIrDistElimL <|
       unCtxLR
         subIrPairComplUnL
         subId)
      subId) <|
    trans subUnSymm <|
    subUnComplPair
  
  def subPairUnDistR {a b c}:
    dl.SubsetStx ctx (pair a (un b c)) (un (pair a b) (pair a c))
  :=
    subComplElim <|
    trans subComplUn <|
    trans (irCtxLR subComplPairUn subComplPairUn) <|
    trans (irCtxLR subUnSymm subUnSymm) <|
    trans subUnIrDistElimL <|
    trans (unCtxLR
      (trans (irCtxLR subUnSymm subUnSymm) <|
       trans subUnIrDistElimL <|
       unCtxLR
         subIrPairComplUnR
         subId)
      subId) <|
    trans subUnSymm <|
    trans (unCtxLR subId subUnSymm) <|
    subUnComplPair
  
  def subPairNoneL {a x}:
    dl.SubsetStx ctx (pair .none a) x
  :=
    trans (pairMonoOfSub subId subAny) <|
    trans
      (subIr
        (pairMonoOfSub subNone subId)
        (trans (unR (unL subId)) subUnComplPair)) <|
    subPe
  
  def subPairNoneR {a x}:
    dl.SubsetStx ctx (pair a .none) x
  :=
    trans (pairMonoOfSub subAny subId) <|
    trans
      (subIr
        (pairMonoOfSub subId subNone)
        (trans (unR (unR subId)) subUnComplPair)) <|
    subPe
  
  def subIrNullPair {a b x}:
    dl.SubsetStx ctx (ir .null (pair a b)) x
  :=
    trans (irCtxLR subId (pairMonoOfSub subAny subAny)) <|
    trans (irCtxLR (trans (unL subId) subUnComplPair) subId) <|
    trans subIrSymm <|
    subPe
  
  def nullPair {x}:
    dl.SubsetStx ctx x (un .null (pair any any))
  :=
    trans subAny <|
    trans (subCompl subPairNoneL) <|
    trans (subComplPairUn (a:=.none) (b:=.none)) <|
    unCtxLR
      subId
      (unCtx
        (pairMonoOfSub subAny subId)
        (pairMonoOfSub subId subAny))
  
end DefList.SubsetStx


abbrev SingleLaneExpr.intpUnivClosure
  (expr: SingleLaneExpr)
  (v: Valuation Pair)
:
  Set Pair
:=
  fun p =>
    ∀ bv,
      expr.freeVarUB ≤ bv.length →
      expr.intp bv v p

-- Semantic entailment.
abbrev DefList.Subset
  (dl: DefList)
  (a b: SingleLaneExpr)
:=
  Set.Subset
    (a.intpUnivClosure dl.wfm)
    (b.intpUnivClosure dl.wfm)
