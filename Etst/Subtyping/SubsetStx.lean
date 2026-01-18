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
  TODO: pair negation rule, splitting rule for full (un a b)
  
  can we prove this?:
  
  & full (un a b)
  & full (impl (ir c a) d)
  & full (impl (ir c b) d)
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
  | full body =>
      full (body.replaceDepthEvenConsts depth ed replacer)
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
  (depth := 0)
  (expr: SingleLaneExpr)
:
  SingleLaneExpr
:=
  expr.replaceDepthEvenConsts depth true desc.hypothesis


def Expr.isSubsingleton
  (expr: Expr E)
:
  Expr E
:=
  arbUn (full (impl expr.lift (var 0)))

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
  - `fullX` if of form `full x ⊆ y`
  - `isFullX` if of form `x ⊆ full y`
  - analogously for `someX` and `isSomeX`
  - context form rules where context is just a variable ought to
    call the context `x`.
  - rules that manipulate the context ought to have `ctx` in the
    name, with the exception of implication rules where context
    manipulation is expected (eg. implication introduction).
  
  TODO things to prove/axiomatize after we have quantifiers:
  - reconstruction:  ir e (pair any any)  ⊆  pair (zth e) (fst e)
  - projection l:  some b  ⊆  impl a (zth (pair a b))
  - projection r:  some a  ⊆  impl b (zth (pair a b))
  - monotonicity of projections
  - distribution of projections over ir, un, arbIr, arbUn
  - induction on pairs.
  - (full a)  ⊆  b  ->  full a  ⊆  full b
  - (a  ⊆  b  ->  a  ⊆  full b)  ->  full (impl a b)  ⊆  impl (full a) (full b)
  
  TODO make this a chapter, make IsFullStx an appendix.
-/
inductive DefList.SubsetStx
  (dl: DefList)
:
  SingleLaneExpr →
  SingleLaneExpr →
  Type
| -- TODO is this provable with induction?
  subDefPos {x}:
    dl.SubsetStx (const .defLane x) (const .posLane x)
| pairMono
    (sl: dl.SubsetStx al bl)
    (sr: dl.SubsetStx ar br)
  :
    dl.SubsetStx (pair al ar) (pair bl br)
|
  subComplPairUn:
    dl.SubsetStx
      (compl (pair a b))
      (un null (un (pair (compl a) any) (pair any (compl b))))
|
  subUnComplPair:
    dl.SubsetStx
      (un null (un (pair (compl a) any) (pair any (compl b))))
      (compl (pair a b))
-- TODO is this one necessary?
| subPairIrDistL:
    dl.SubsetStx (ir (pair a c) (pair b c)) (pair (ir a b) c)
-- TODO is this one necessary?
| subPairIrDistR:
    dl.SubsetStx (ir (pair a b) (pair a c)) (pair a (ir b c))
| subIrL:
    dl.SubsetStx (ir a r) a
| subIrR:
    dl.SubsetStx (ir l a) a
| subIr
    (ac: dl.SubsetStx x l)
    (bc: dl.SubsetStx x r)
  :
    dl.SubsetStx x (ir l r)
|
  subIrUnDistL:
    dl.SubsetStx (ir (un a b) c) (un (ir a c) (ir b c))
|
  isFull
    (subA: dl.SubsetStx any a)
  :
    dl.SubsetStx x (full a)
|
  -- Axiom K in modal logic.
  fullImplElim:
    dl.SubsetStx
      (full (impl a b))
      (impl (full a) (full b))
|
  -- Axiom T in modal logic.
  fullElim:
    dl.SubsetStx (full a) a
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
    dl.SubsetStx (some (full a)) (full a)
|
  subCompl
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx b.compl a.compl
| subDne: dl.SubsetStx a.compl.compl a
| subDni: dl.SubsetStx a a.compl.compl
-- Principle of explosion. Used as a basic rule instead of
-- implication elimination, which is derived from this.
| subPe:
    dl.SubsetStx (ir a a.compl) b
|
  univIntro
    (sub: dl.SubsetStx x.lift a)
  :
    dl.SubsetStx x (arbIr a)
|
  univElim
    (isSome: dl.SubsetStx x (some t))
    (isSubsingle: dl.SubsetStx x t.isSubsingleton)
    (sub: dl.SubsetStx x (arbIr a))
  :
    dl.SubsetStx x (a.instantiateVar t)
|
  trans
    (ab: dl.SubsetStx a b)
    (bc: dl.SubsetStx b c)
  :
    dl.SubsetStx a c
| -- TODO should be provable with induction.
  subUnfold:
    dl.SubsetStx
      (const lane a)
      ((dl.getDef a).toLane lane)
|
  -- TODO is this provable with induction?
  subFold:
    dl.SubsetStx
      ((dl.getDef a).toLane lane)
      (const lane a)
|
  mutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      dl.SubsetStx
        x
        (full
          (impl
            (desc.hypothesify 0 (desc[i].expansion.toLane desc[i].lane))
            desc[i].expr)))
    (i: desc.Index)
  :
    dl.SubsetStx
      x
      (full (impl (const desc[i].lane desc[i].x) desc[i].expr))


namespace DefList.SubsetStx
  variable {dl: DefList}
  
  def subId {expr}:
    dl.SubsetStx expr expr
  :=
    trans subDni subDne
  
  def toFn {x a b}
    (ab: dl.SubsetStx a b)
  :
    dl.SubsetStx x a → dl.SubsetStx x b
  :=
    (trans · ab)
  
  def ofFn {a b}
    (sub: ∀ x, dl.SubsetStx x a → dl.SubsetStx x b)
  :
    dl.SubsetStx a b
  :=
    sub a subId
  
  
  def irCtxL {a b r}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (ir a r) b
  :=
    trans subIrL sub
  
  def irCtxR {a b l}
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (ir l a) b
  :=
    trans subIrR sub
  
  def irCtxLR
    (subL: dl.SubsetStx al bl)
    (subR: dl.SubsetStx ar br)
  :
    dl.SubsetStx (ir al ar) (ir bl br)
  :=
    subIr subL.irCtxL subR.irCtxR
  
  def subIrSymm
    {l r: SingleLaneExpr}
  :
    dl.SubsetStx (ir l r) (ir r l)
  :=
    subIr subIrR subIrL
  
  def irElimL
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x l
  :=
    sub.trans subIrL
  
  def irElimR
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x r
  :=
    sub.trans subIrR
  
  def irSymm
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x (ir r l)
  :=
    subIr (irElimR sub) (irElimL sub)
  
  def irSymmCtx
    (sub: dl.SubsetStx (ir l r) b)
  :
    dl.SubsetStx (ir r l) b
  :=
    trans subIrSymm sub
  
  def irMonoCtxL
    (subA: dl.SubsetStx a al)
    (sub: dl.SubsetStx (ir al ar) b)
  :
    dl.SubsetStx (ir a ar) b
  :=
    trans (irCtxLR subA subId) sub
  
  def irMonoCtxR
    (subA: dl.SubsetStx a ar)
    (sub: dl.SubsetStx (ir al ar) b)
  :
    dl.SubsetStx (ir al a) b
  :=
    trans (irCtxLR subId subA) sub
  
  
  def subUnL {a r}:
    dl.SubsetStx a (un a r)
  :=
    subDni.trans (subCompl subIrL)

  def subUnR {a l}:
    dl.SubsetStx a (un l a)
  :=
    subDni.trans (subCompl subIrR)

  def unCtx {l r b}
    (ac: dl.SubsetStx l b)
    (bc: dl.SubsetStx r b)
  :
    dl.SubsetStx (un l r) b
  :=
    (subCompl (subIr (subCompl ac) (subCompl bc))).trans subDne

  def em {x a}:
    dl.SubsetStx x (un a a.compl)
  :=
    subDni.trans (subCompl subPe)
  
  def unL {x a b}
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (un a b)
  :=
    sub.trans subUnL
  
  def unR {x a b}
    (sub: dl.SubsetStx x b)
  :
    dl.SubsetStx x (un a b)
  :=
    sub.trans subUnR
  
  def unCtxLR {al ar bl br}
    (subL: dl.SubsetStx al bl)
    (subR: dl.SubsetStx ar br)
  :
    dl.SubsetStx (un al ar) (un bl br)
  :=
    unCtx subL.unL subR.unR
  
  def subUnSymm {l r}:
    dl.SubsetStx (un l r) (un r l)
  :=
    unCtx subUnR subUnL
  
  def unElimCtxL {l r b}
    (sub: dl.SubsetStx (un l r) b)
  :
    dl.SubsetStx l b
  :=
    trans subUnL sub
  
  def unElimCtxR
    (sub: dl.SubsetStx (un l r) b)
  :
    dl.SubsetStx r b
  :=
    trans subUnR sub
  
  def unSymm
    (sub: dl.SubsetStx x (un l r))
  :
    dl.SubsetStx x (un r l)
  :=
    sub.trans subUnSymm
  
  def unSymmCtx
    (sub: dl.SubsetStx (un l r) b)
  :
    dl.SubsetStx (un r l) b
  :=
    unCtx (unElimCtxR sub) (unElimCtxL sub)
  
  def unElimSub
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx l a)
    (subR: dl.SubsetStx r a)
  :
    dl.SubsetStx x a
  :=
    sub.trans (unCtx subL subR)
  
  def unMonoSubL
    (sub: dl.SubsetStx x (un la r))
    (subL: dl.SubsetStx la lb)
  :
    dl.SubsetStx x (un lb r)
  :=
    unElimSub sub (unL subL) subUnR
  
  def unMonoSubR
    (sub: dl.SubsetStx x (un l ra))
    (subR: dl.SubsetStx ra rb)
  :
    dl.SubsetStx x (un l rb)
  :=
    unElimSub sub subUnL (unR subR)
  
  def unIr
    (subA: dl.SubsetStx x (un al ar))
    (subB: dl.SubsetStx x b)
  :
    dl.SubsetStx x (un (ir al b) (ir ar b))
  :=
    trans (subIr subA subB) subIrUnDistL
  
  
  def subIrUnDistR {al aur aul}:
    dl.SubsetStx
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
      (un (ir aul ar) (ir aur ar))
      (ir (un aul aur) ar)
  :=
    unCtx
      (subIr (irCtxL subUnL) subIrR)
      (subIr (irCtxL subUnR) subIrR)
  
  def subIrUnDistElimR {al aur aul}:
    dl.SubsetStx
      (un (ir al aul) (ir al aur))
      (ir al (un aul aur))
  :=
    unCtx
      (subIr subIrL (irCtxR subUnL))
      (subIr subIrL (irCtxR subUnR))
  
  
  def subUnIrDistL {ail air ar}:
    dl.SubsetStx
      (un (ir ail air) ar)
      (ir (un ail ar) (un air ar))
  :=
    unCtx
      (irCtxLR subUnL subUnL)
      (subIr subUnR subUnR)
  
  def subUnIrDistR {al air ail}:
    dl.SubsetStx
      (un al (ir ail air))
      (ir (un al ail) (un al air))
  :=
    unCtx
      (subIr subUnL subUnL)
      (irCtxLR subUnR subUnR)
  
  def subUnIrDistElimL {ail air ar: SingleLaneExpr}:
    dl.SubsetStx
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
      (ir (un al ail) (un al air))
      (un al (ir ail air))
  :=
    subIrUnDistL.trans
      (unCtx
        (irCtxL subUnL)
        (subIrUnDistR.trans
          (unCtx (irCtxR subUnL) subUnR)))
  
  -- TODO finish once we can work with quantifiers.
  def subAny: dl.SubsetStx a any := sorry
  def subNone: dl.SubsetStx none a := sorry
  
  
  def implIntro
    (sub: dl.SubsetStx (ir x a) b)
  :
    dl.SubsetStx x (impl a b)
  :=
    trans
      (trans (subIr subUnR em.unSymm) subUnIrDistElimR)
      (unCtxLR subId sub)
  
  def implElim
    (subImpl: dl.SubsetStx x (impl a b))
    (subA: dl.SubsetStx x a)
  :
    dl.SubsetStx x b
  :=
    trans
      (subIr subA subImpl)
      (subIrUnDistR.trans (unCtx subPe subIrR))
  
  def implElimExact
    (subA: dl.SubsetStx a (impl a b))
  :
    dl.SubsetStx a b
  :=
    implElim subA subId
  
  def implAbsorb
    (subImpl: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx (ir x a) b
  :=
    irMonoCtxL
      subImpl
      (trans
        subIrUnDistL
        (unCtx (trans subIrSymm subPe) subIrL))
  
  def subImplCompl {a}:
    dl.SubsetStx (impl a none) (compl a)
  :=
    unCtx subId subNone

  def subComplImpl {a}:
    dl.SubsetStx (compl a) (impl a none)
  :=
    subUnL

  def toImpl
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx x (impl a b)
  :=
    trans
      em
      (unCtx
        (trans sub subUnR)
        subUnL)
  
  def ofImpl
    (sub: dl.SubsetStx any (impl a b))
  :
    dl.SubsetStx a b
  :=
    implElimExact (trans subAny sub)
  
  def unElimComplL
    (ab: dl.SubsetStx x (un a b))
    (aCompl: dl.SubsetStx x (a.compl))
  :
    dl.SubsetStx x b
  :=
    trans
      (subIr aCompl ab)
      (subIrUnDistR.trans (unCtx subPe.irSymmCtx subIrR))
  
  def unElimComplR
    (ab: dl.SubsetStx x (un a b))
    (bCompl: dl.SubsetStx x (b.compl))
  :
    dl.SubsetStx x a
  :=
    trans
      (subIr bCompl ab)
      (subIrUnDistR.trans (unCtx subIrR subPe.irSymmCtx))
  
  -- Principle of explosion.
  def pe
    (subA: dl.SubsetStx x a)
    (subAc: dl.SubsetStx x a.compl)
  :
    dl.SubsetStx x b
  :=
    trans (subIr subA subAc) subPe
  
  
  def unElim
    (sub: dl.SubsetStx x (un l r))
    (subL: dl.SubsetStx x (impl l a))
    (subR: dl.SubsetStx x (impl r a))
  :
    dl.SubsetStx x a
  :=
    trans
      (trans (subIr sub subId) subIrUnDistL)
      (unCtx
        (trans subIrSymm (implAbsorb subL))
        (trans subIrSymm (implAbsorb subR)))
  
  def unMonoL
    (sub: dl.SubsetStx x (un la r))
    (subL: dl.SubsetStx x (impl la lb))
  :
    dl.SubsetStx x (un lb r)
  :=
    unElim
      sub
      (implIntro (trans (implAbsorb subL) subUnL))
      (toImpl subUnR)
  
  def unMonoR
    (sub: dl.SubsetStx x (un l ra))
    (subR: dl.SubsetStx x (impl ra rb))
  :
    dl.SubsetStx x (un l rb)
  :=
    unElim
      sub
      (toImpl subUnL)
      (implIntro (trans (implAbsorb subR) subUnR))
  
  
  def dne
    (sub: dl.SubsetStx x (compl (compl a)))
  :
    dl.SubsetStx x a
  :=
    trans sub subDne
  
  def dneCtx
    (sub: dl.SubsetStx (compl (compl a)) b)
  :
    dl.SubsetStx a b
  :=
    subDni.trans sub
  
  def dni
    (sub: dl.SubsetStx x a)
  :
    dl.SubsetStx x (compl (compl a))
  :=
    trans sub subDni
  
  def dniCtx
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (compl (compl a)) b
  :=
    subDne.trans sub
  
  def subComplElim
    (sub: dl.SubsetStx (compl a) (compl b))
  :
    dl.SubsetStx b a
  :=
    trans subDni (trans (subCompl sub) subDne)
  
  def complSwapCtx
    (sub: dl.SubsetStx (compl a) b)
  :
    dl.SubsetStx (compl b) a
  :=
    (subCompl sub).trans subDne
  
  def complSwap
    (sub: dl.SubsetStx a (compl b))
  :
    dl.SubsetStx b (compl a)
  :=
    subDni.trans (subCompl sub)
  
  def subContra:
    dl.SubsetStx (impl a b) (impl (compl b) (compl a))
  :=
    trans subUnSymm (unCtxLR subDni subId)
  
  def subContraElim
    {a b: SingleLaneExpr}
  :
    dl.SubsetStx (impl a.compl b.compl) (impl b a)
  :=
    em.unElim
      (implIntro (unR subIrR))
      (implIntro (unL (implElim subIrL subIrR)))

  def contra
    (sub: dl.SubsetStx x (impl a b))
  :
    dl.SubsetStx x (impl (compl b) (compl a))
  :=
    toFn subContra sub
  
  def contraElim
    (sub: dl.SubsetStx x (impl a.compl b.compl))
  :
    dl.SubsetStx x (impl b a)
  :=
    toFn subContraElim sub
  
  
  def subComplUn:
    dl.SubsetStx (compl (un l r)) (ir (compl l) (compl r))
  :=
    subIr (subCompl subUnL) (subCompl subUnR)
  
  def subComplUnElim:
    dl.SubsetStx (ir (compl l) (compl r)) (compl (un l r))
  :=
    complSwap (unCtx (complSwap subIrL) (complSwap subIrR))
  
  def complUn
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (ir (compl l) (compl r))
  :=
    sub.trans subComplUn
  
  def complUnElim
    (sub: dl.SubsetStx x (ir (compl l) (compl r)))
  :
    dl.SubsetStx x (compl (un l r))
  :=
    sub.trans subComplUnElim
  
  def complUnElimL
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (compl l)
  :=
    irElimL (complUn sub)
  
  def complUnElimR
    (sub: dl.SubsetStx x (compl (un l r)))
  :
    dl.SubsetStx x (compl r)
  :=
    irElimR (complUn sub)
  
  
  def fullElimOfImpl
    (fullAb: dl.SubsetStx any (full (impl a b)))
  :
    dl.SubsetStx (full a) (full b)
  :=
    implElimExact
      (trans subAny (trans fullAb fullImplElim))
  
  def isFullImpl
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx any (full (impl a b))
  :=
    isFull (toImpl sub)
  
  def isFullImplElim
    (sub: dl.SubsetStx any (full (impl a b)))
  :
    dl.SubsetStx a b
  :=
    ofImpl (trans sub fullElim)
  
  def fullMono
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (full a) (full b)
  :=
    fullElimOfImpl (isFullImpl sub)
  
  def fullDne:
    dl.SubsetStx (full (compl (compl a))) (full a)
  :=
    fullMono subDne
  
  def fullDni:
    dl.SubsetStx (full a) (full (compl (compl a)))
  :=
    fullMono subDni
  
  def complFullAntimono
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (compl (full b)) (compl (full a))
  :=
    subCompl (fullMono sub)
  
  
  def subSome:
    dl.SubsetStx a (some a)
  :=
    trans subDni (subCompl fullElim)
  
  def someMono
    (sub: dl.SubsetStx a b)
  :
    dl.SubsetStx (some a) (some b)
  :=
    complFullAntimono (subCompl sub)
  
  
  def fullSome:
    dl.SubsetStx (full a) (some a)
  :=
    trans fullElim subSome
  
  def someElimFull
    (sub: dl.SubsetStx a (full b))
  :
    dl.SubsetStx (some a) (full b)
  :=
    trans (someMono sub) someStripFull
  
  def isFullUpgrade
    (isSomeA: dl.SubsetStx any (some a))
    (aFullB: dl.SubsetStx a (full b))
  :
    dl.SubsetStx any (full b)
  :=
    trans isSomeA (someElimFull aFullB)
  
  def someAddFull:
    dl.SubsetStx (some a) (full (some a))
  :=
    complSwapCtx someStripFull
  
  def fullAddSome:
    dl.SubsetStx (full a) (some (full a))
  :=
    subSome
  
  def someAddSome:
    dl.SubsetStx (some a) (some (some a))
  :=
    subSome
  
  def subFullSome:
    dl.SubsetStx a (full (some a))
  :=
    trans subSome someAddFull
  
  def fullAddFull:
    dl.SubsetStx (full a) (full (full a))
  :=
    trans subFullSome (fullMono someStripFull)
  
  def someElimComplFull
    (sub: dl.SubsetStx a (compl (full b)))
  :
    dl.SubsetStx (some a) (compl (full b))
  :=
    subCompl (trans fullAddFull (fullMono (complSwap sub)))
  
  def someStripSome:
    dl.SubsetStx (some (some a)) (some a)
  :=
    subCompl (trans fullAddFull (fullMono subDni))
  
  
  def someNull:
    dl.SubsetStx any (some null)
  :=
    sorry
  
  def somePair
    (sl: dl.SubsetStx any (some l))
    (sr: dl.SubsetStx any (some r))
  :
    dl.SubsetStx any (some (pair l r))
  :=
    sorry
  
  def isSomeMono
    (ab: dl.SubsetStx a b)
    (sa: dl.SubsetStx any (some a))
  :
    dl.SubsetStx any (some b)
  :=
    trans sa (someMono ab)
  
  def isSomeUpgrade
    (isSomeA: dl.SubsetStx any (some a))
    (aSomeB: dl.SubsetStx a (some b))
  :
    dl.SubsetStx any (some b)
  :=
    trans (isSomeMono aSomeB isSomeA) someStripSome
  
  
  def unfoldCtx
      (sub: dl.SubsetStx (const lane a) b)
    :
      dl.SubsetStx ((dl.getDef a).toLane lane) b
  :=
    trans subFold sub
  
  def unfold
      (sub: dl.SubsetStx x (const lane a))
    :
      dl.SubsetStx x ((dl.getDef a).toLane lane)
  :=
    trans sub subUnfold
  
  def foldCtx
      (sub: dl.SubsetStx ((dl.getDef a).toLane lane) b)
    :
      dl.SubsetStx (const lane a) b
  :=
    trans subUnfold sub
  
  def fold
      (sub: dl.SubsetStx x ((dl.getDef a).toLane lane))
    :
      dl.SubsetStx x (const lane a)
    :=
      trans sub subFold
  
  
  def pairMonoWithCtx
    (dist: ∀ {s a b}, dl.SubsetStx (ir (full s) (pair a b)) (pair (ir (full s) a) (ir (full s) b)))
    (sl: dl.SubsetStx x (full (impl al bl)))
    (sr: dl.SubsetStx x (full (impl ar br)))
  :
    dl.SubsetStx x (full (impl (pair al ar) (pair bl br)))
  :=
    let cal := full (impl al bl)
    let car := full (impl ar br)
    
    let lemma1 {A B l} (subL: dl.SubsetStx l (full (impl A B))) (subR: dl.SubsetStx l A) : dl.SubsetStx l B :=
      implElim (trans subL fullElim) subR
      
    let core: dl.SubsetStx (ir cal (ir car (pair al ar))) (pair bl br) :=
      trans (irCtxLR subId dist) <|
      trans dist <|
      pairMono
        (lemma1 subIrL (trans subIrR subIrR))
        (lemma1 (trans subIrR subIrL) (trans subIrR subIrR))
    
    let subAssoc {a b c} : dl.SubsetStx (ir (ir a b) c) (ir a (ir b c)) :=
      subIr
        (trans subIrL subIrL)
        (subIr
          (trans subIrL subIrR)
          subIrR)

    let bigImpl: dl.SubsetStx any (impl cal (impl car (impl (pair al ar) (pair bl br)))) :=
      implIntro <| implIntro <| implIntro <|
      trans (irCtxLR (irCtxLR subIrR subId) subId) <|
      trans subAssoc <|
      core

    let fullBig: dl.SubsetStx x (full (impl cal (impl car (impl (pair al ar) (pair bl br))))) :=
      isFull bigImpl

    let step1: dl.SubsetStx x (impl (full cal) (full (impl car (impl (pair al ar) (pair bl br))))) :=
      trans fullBig fullImplElim
    
    let elim1: dl.SubsetStx x (full (impl car (impl (pair al ar) (pair bl br)))) :=
      implElim step1 (trans sl fullAddFull)

    let step2: dl.SubsetStx x (impl (full car) (full (impl (pair al ar) (pair bl br)))) :=
      trans elim1 fullImplElim

    implElim step2 (trans sr fullAddFull)
  
  def implPairMono
    (dist: ∀ {s a b}, dl.SubsetStx (ir (full s) (pair a b)) (pair (ir (full s) a) (ir (full s) b)))
  :
    dl.SubsetStx
      any
      (impl
        (full (impl al bl))
        (impl
          (full (impl ar br))
          (impl (pair al ar) (pair bl br))))
  :=
    implIntro
      (implIntro
        (trans
          (pairMonoWithCtx dist (irCtxL subIrR) subIrR)
          fullElim))
  
  
  def subMutInduction
    (desc: MutIndDescriptor dl)
    (premises:
      (i: desc.Index) →
      dl.SubsetStx
        (desc.hypothesify 0 (desc[i].expansion.toLane desc[i].lane))
        desc[i].expr)
    (i: desc.Index)
  :
    dl.SubsetStx (const desc[i].lane desc[i].x) desc[i].expr
  :=
    isFullImplElim
      (mutInduction desc (fun i => isFullImpl (premises i)) i)
  
  def subInduction
    (desc: InductionDescriptor dl)
    (premise:
      dl.SubsetStx
        ((desc.expansion.toLane desc.lane).replaceDepthEvenConsts 0 true fun depth lane x =>
          desc.hypothesis depth lane x (const lane x))
        desc.expr)
  :
    dl.SubsetStx (const desc.lane desc.x) desc.expr
  :=
    subMutInduction
      [desc]
      (fun | ⟨0, _⟩ => premise)
      ⟨0, Nat.zero_lt_succ _⟩
  
  def subSimpleInduction {x lane expr}
    (premise:
      dl.SubsetStx
        (((dl.getDef x).toLane lane).replaceDepthEvenConsts 0 true fun depth l xR =>
          if l.Le lane && x = xR then .ir (expr.lift 0 depth) (const l xR) else (const l xR))
        expr)
  :
    dl.SubsetStx (const lane x) expr
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
    dl.SubsetStx (impl a (impl b c)) (impl (impl a b) (impl a c))
  :=
    .implIntro
      (.implIntro
        (.implElim
          (.implElim (irCtxL .subIrL) .subIrR)
          (.implElim (irCtxL .subIrR) .subIrR)))
  
  def subIrUnCompl {a b}:
    dl.SubsetStx a (un (ir a b.compl) b)
  :=
    trans
      (subIr subUnR em)
      (trans subUnIrDistElimR subUnSymm)
  
  def subIrPairComplUnL {a b c}:
    dl.SubsetStx
      (ir (pair (compl a) c) (pair (compl b) c))
      (pair (compl (un a b)) c)
  :=
    trans subPairIrDistL <|
    pairMono subComplUnElim subId

  def subIrPairComplUnR {a b c}:
    dl.SubsetStx
      (ir (pair a (compl b)) (pair a (compl c)))
      (pair a (compl (un b c)))
  :=
    trans subPairIrDistR <|
    pairMono subId subComplUnElim

  def subPairUnDistL {a b c}:
    dl.SubsetStx (pair (un a b) c) (un (pair a c) (pair b c))
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
    dl.SubsetStx (pair a (un b c)) (un (pair a b) (pair a c))
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
    dl.SubsetStx (pair none a) x
  :=
    sorry
  
  def subPairNoneR {a x}:
    dl.SubsetStx (pair a none) x
  :=
    sorry
  
  def subIrNullPair {a b x}:
    dl.SubsetStx (ir .null (pair a b)) x
  :=
    trans (irCtxLR subId (pairMono subAny subAny)) <|
    trans (irCtxLR (trans (unL subId) subUnComplPair) subId) <|
    trans subIrSymm <|
    subPe
  
  def nullPair {x}:
    dl.SubsetStx x (un .null (pair any any))
  :=
    trans subAny <|
    trans (subCompl subPairNoneL) <|
    trans (subComplPairUn (a:=none) (b:=none)) <|
    unCtxLR
      subId
      (unCtx
        (pairMono subAny subId)
        (pairMono subId subAny))
  
  
  def subArbUnIntro {a t}
    (isSome: dl.SubsetStx any (some t))
    (isSubsingle: dl.SubsetStx any t.isSubsingleton)
  :
    dl.SubsetStx (a.instantiateVar t) (arbUn a)
  :=
    complSwap
      (univElim
        (trans subAny isSome)
        (trans subAny isSubsingle)
        subId)

  def subArbUnElim {a b}
    (sub: dl.SubsetStx a b.lift)
  :
    dl.SubsetStx (arbUn a) b
  :=
    complSwapCtx (univIntro (subCompl sub))
  
  def exIntro {x a t}
    (isSome: dl.SubsetStx x (some t))
    (isSubsingle: dl.SubsetStx x t.isSubsingleton)
    (sub: dl.SubsetStx x (a.instantiateVar t))
  :
    dl.SubsetStx x (arbUn a)
  :=
    let y := ir x (arbIr (compl a))
    let aInst := a.instantiateVar t
    
    let subYa: dl.SubsetStx y aInst :=
      trans subIrL sub
    let subYnotA: dl.SubsetStx y (compl aInst) :=
      univElim
        (trans subIrL isSome)
        (trans subIrL isSubsingle)
        subIrR
    
    let subYNull: dl.SubsetStx y (ir aInst (compl aInst)) :=
      subIr subYa subYnotA
    
    trans (implIntro subYNull) (unCtx subId subPe)

  def exElim {x a b}
    (sub: dl.SubsetStx x (arbUn a))
    (impl: dl.SubsetStx x.lift (impl a b.lift))
  :
    dl.SubsetStx x b
  :=
    let y := ir x (Expr.compl b)
    let subYComplA: dl.SubsetStx y.lift (compl a) :=
      trans
        (trans (irCtxLR impl subId) subIrUnDistL)
        (unCtx subIrL subPe)
    
    let subYArbIr: dl.SubsetStx y (arbIr (compl a)) :=
      univIntro subYComplA
      
    let subYArbUn: dl.SubsetStx y (arbUn a) :=
      trans subIrL sub
    
    let subNull: dl.SubsetStx y none :=
      trans (subIr subYArbUn (trans subYArbIr subDni)) subPe
    
    trans (implIntro subNull) (trans subImplCompl subDne)
  
end DefList.SubsetStx


-- Semantic entailment for a given assignment of variables.
abbrev DefList.SubsetBv
  (dl: DefList)
  (fv: List Pair)
  (a b: SingleLaneExpr)
:=
  Set.Subset (a.intp fv dl.wfm) (b.intp fv dl.wfm)

-- Semantic entailment.
abbrev DefList.Subset
  (dl: DefList)
  (a b: SingleLaneExpr)
:=
  ∀ fv, dl.SubsetBv fv a b
