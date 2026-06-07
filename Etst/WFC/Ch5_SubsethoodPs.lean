/-
  # Chapter 5: A Proof System for Subsethood in Well-Founded Collections
  
  In this chapter, we define a natural-deduction-style proof system
  `SubsetStx`, with `dl.SubsetStx a b` interpretable in two equivalent
  ways:
  
  0. A proof that `a` represents a subset of `b`.
  1. A proof that, given an assumption `a`, we can derive `b`.
-/

/-
  Historical note: initially, I had hoped to avoid explicitly
  distinguishing between possible and definite membership; with
  `SubsetStx` using `BasicExpr` instead of `SingleLaneExpr`, and
  an expression `a ⊆ b` implicitly having the meaning "every
  possible member of `a` is a definite member of `b`". However,
  this kind of subsethood turned out not to be closed under
  induction -- the induction hypothesis needs to refer to definite
  members, since those are supposed to be already known to be
  definite members of `b`.
  
  However, I am still a little uneasy about this. Hopefully, this
  was the right choice.
-/

import Mathlib.Algebra.Order.BigOperators.Group.List

import Etst.WFC.Ch4_S1_MembershipPs
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.SubsetStx.Induction

namespace Etst
open Expr


-- Semantic entailment for a given assignment of variables.
abbrev DefList.SubsetFv
  (dl: DefList)
  (fv: List Pair)
  (o: Valuation Pair)
  (a b: SingleLaneExpr)
:=
  Set.Subset (a.intp fv (dl.wfm o) o) (b.intp fv (dl.wfm o) o)

-- Semantic entailment.
abbrev DefList.Subset
  (dl: DefList)
  (o: Valuation Pair)
  (a b: SingleLaneExpr)
:=
  ∀ fv,
    a.freeVarUb ≤ fv.length →
    b.freeVarUb ≤ fv.length →
    dl.SubsetFv fv o a b


def Expr.isSubsingleton_body {E} (e: Expr E): Expr E :=
  impl (some (ir e.lift (var 0))) (full (impl e.lift (var 0)))

def Expr.isSubsingleton {E} (e: Expr E) : Expr E :=
  arbIr e.isSubsingleton_body

def Expr.isSubsingleton_freeVarUb_pos {E}
  (e: Expr E)
:
  0 < e.isSubsingleton_body.freeVarUb
:=
  lt_max_iff.mpr
    (Or.inl
      (lt_max_iff.mpr
        (Or.inr
          (Nat.zero_lt_succ _))))


inductive DefList.SubsetStx
  (dl: DefList)
:
  SingleLaneExpr →
  SingleLaneExpr →
  Type
|
  subId {a}:
    dl.SubsetStx a a
|
  defPos {x c} -- TODO is this provable with induction?
    (sub: dl.SubsetStx x (const .defLane c))
  :
    dl.SubsetStx x (const .posLane c)
|
  varSomeFull {x i a}
    (sub: dl.SubsetStx x (some (ir (var i) a)))
  :
    dl.SubsetStx x (full (impl (var i) a))
|
  varFullSome {x i a}
    (sub: dl.SubsetStx x (full (impl (var i) a)))
  :
    dl.SubsetStx x (some (ir (var i) a))
|
  nullSomeFull {x a}
    (sub: dl.SubsetStx x (some (ir null a)))
  :
    dl.SubsetStx x (full (impl null a))
|
  nullFullSome {x a}
    (sub: dl.SubsetStx x (full (impl null a)))
  :
    dl.SubsetStx x (some (ir null a))
|
  someProd {x a b}
    (subA: dl.SubsetStx x (some a))
    (subB: dl.SubsetStx x (some b))
  :
    dl.SubsetStx x (some (prod a b))
|
  prodVarSomeFull {x i j a}
    (sub: dl.SubsetStx x (some (ir (prod (var i) (var j)) a)))
  :
    dl.SubsetStx x (full (impl (prod (var i) (var j)) a))
|
  -- TODO replace with prodMono and derive?
  prodMonoFullImpl {x al bl ar br}
    (sl: dl.SubsetStx x (full (impl al bl)))
    (sr: dl.SubsetStx x (full (impl ar br)))
  :
    dl.SubsetStx x (full (impl (prod al ar) (prod bl br)))
|
  prodIr {x al bl ar br}
    (subA: dl.SubsetStx x (prod al ar))
    (subB: dl.SubsetStx x (prod bl br))
  :
    dl.SubsetStx x (prod (ir al bl) (ir ar br))
|
  prodArbIrL {x a b}
    (sub: dl.SubsetStx x (arbIr (prod a b.lift)))
  :
    dl.SubsetStx x (prod (arbIr a) b)
|
  prodArbIrR {x a b}
    (sub: dl.SubsetStx x (arbIr (prod a.lift b)))
  :
    dl.SubsetStx x (prod a (arbIr b))
|
  complProd {x a b}
    (sub:
      dl.SubsetStx
        x
        (un null (un (prod (compl a) any) (prod any (compl b)))))
  :
    dl.SubsetStx x (compl (prod a b))
|
  complProdElim {x a b}
    (sub: dl.SubsetStx x (compl (prod a b)))
  :
    dl.SubsetStx
      x
      (un null (un (prod (compl a) any) (prod any (compl b))))
|
  irL {x l r}
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x l
|
  irR {x l r}
    (sub: dl.SubsetStx x (ir l r))
  :
    dl.SubsetStx x r
|
  irI {x l r}
    (ac: dl.SubsetStx x l)
    (bc: dl.SubsetStx x r)
  :
    dl.SubsetStx x (ir l r)
|
  complI {x a b}
    (sub: dl.SubsetStx (ir x a) b)
    (subCpl: dl.SubsetStx (ir x a) b.compl)
  :
    dl.SubsetStx x a.compl
|
  complElim {x a b}
    (sub: dl.SubsetStx (ir x a.compl) b)
    (subCpl: dl.SubsetStx (ir x a.compl) b.compl)
  :
    dl.SubsetStx x a
|
  fullImpl {x a b}
    (subA: dl.SubsetStx a b)
  :
    dl.SubsetStx x (full (impl a b))
|
  -- Axiom K in modal logic.
  fullImplDist {x a b}
    (sub: dl.SubsetStx x (full (impl a b)))
  :
    dl.SubsetStx x (impl (full a) (full b))
|
  -- Axiom T in modal logic.
  fullElim {x a}
    (sub: dl.SubsetStx x (full a))
  :
    dl.SubsetStx x a
|
  -- (Almost) the contraposition of Axiom 5 in modal logic.
  someStripFull {x a}
    (sub: dl.SubsetStx x (some (full a)))
  :
    dl.SubsetStx x (full a)
|
  arbIrI {x a}
    (sub: dl.SubsetStx x.lift a)
  :
    dl.SubsetStx x (arbIr a)
|
  -- TODO can this be replaced with arbIrElimVar, and derived?
  arbIrElim {x t a}
    (sub: dl.SubsetStx x (arbIr a))
    (isSome: dl.SubsetStx x (some t))
    (isSubsingle: dl.SubsetStx x t.isSubsingleton)
  :
    dl.SubsetStx x (a.instantiateVar t)
|
  noneElim {x a}
    (sub: dl.SubsetStx x none)
  :
    dl.SubsetStx x a
|
  unfold {x lane c} -- TODO should be provable with induction.
    (sub: dl.SubsetStx x (const lane c))
  :
    dl.SubsetStx x ((dl.getDef c).toLane lane)
|
  fold {x lane c} -- TODO is this provable with induction?
    (sub: dl.SubsetStx x ((dl.getDef c).toLane lane))
  :
    dl.SubsetStx x (const lane c)
|
  trans {a b c}
    (ab: dl.SubsetStx a b)
    (bc: dl.SubsetStx b c)
  :
    dl.SubsetStx a c
|
  mutInduction {x}
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
|
  -- TODO: should this be replaced with general (fixed-depth) pair induction?
  simplePairInduction {x p a}
    (sub: dl.SubsetStx x (full (impl (un null (prod p p)) p)))
  :
    dl.SubsetStx x (full (impl a p))


def DefList.SubsetFv.subsetOfFullImpl {dl fv o x a b p}
  (h: SubsetFv dl fv o x (.full (.impl a b)))
  (isIn: p ∈ x.intp fv (dl.wfm o) o)
:
  dl.SubsetFv fv o a b
:=
  open SingleLaneExpr in
  fun p' inA => inImplElim (inFullElim (h isIn) p') inA

def DefList.SubsetFv.fullImplOfSubset {dl fv o x a b}
  (h: SubsetFv dl fv o a b)
:
  SubsetFv dl fv o x (.full (.impl a b))
:=
  open SingleLaneExpr in
  fun _ _ => inFull .null fun _ => inImpl fun inA => h inA

def DefList.Subset.call {dl o a b}
  (sub: Subset dl o a b)
  (fv: List Pair)
  (leA: a.freeVarUb ≤ fv.length)
  (p: Pair)
  (isIn: p ∈ a.intp fv (dl.wfm o) o)
:
  p ∈ b.intp (fv ++ List.replicate b.freeVarUb Pair.null) (dl.wfm o) o
:=
  let fvPad := fv ++ List.replicate b.freeVarUb Pair.null
  let padLen: fvPad.length = fv.length + b.freeVarUb :=
    List.length_replicate (n := b.freeVarUb) ▸ List.length_append
  let leAPad: a.freeVarUb ≤ fvPad.length :=
    padLen ▸ Nat.le_add_right_of_le leA
  let leBPad: b.freeVarUb ≤ fvPad.length :=
    padLen ▸ Nat.le_add_left _ _
  let isInPad: p ∈ a.intp fvPad (dl.wfm o) o :=
    SingleLaneExpr.intp_bv_append leA _ ▸ isIn
  sub fvPad leAPad leBPad isInPad


def SingleLaneExpr.isSubsingleton_intp_eq
  {expr fv v o p pS}
  (inSubs: intp expr.isSubsingleton fv v o pS)
  (inExpr: intp expr fv v o p)
:
  intp expr fv v o = {p}
:=
  Set.eq_singleton_iff_unique_mem.mpr
    (And.intro
      inExpr
      (fun pE isIn =>
        inVarElim
          (inImplElim
            (inImplElim
              (inArbIrElim inSubs p)
              (inSome
                .null
                (inIr
                  (intp2_lift_eq expr fv [p] v v o ▸ inExpr)
                  (inVar rfl)))
              pE)
            (intp2_lift_eq expr fv [p] v v o ▸ isIn))
          rfl))

namespace DefList.SubsetStx
  variable {dl: DefList}
  
  def context {x e} (_: SubsetStx dl x e) := x
  def conclusion {x e} (_: SubsetStx dl x e) := e
  
  def isSound {x e}
    (sub: dl.SubsetStx x e)
    (o: Valuation Pair)
  :
    dl.Subset o x e
  :=
    open List SingleLaneExpr in
    fun fv leX leE p isIn =>
      match sub with
      | subId => isIn
      | defPos sub => Set3.defLePos _ (sub.isSound o fv leX leE isIn)
      | varSomeFull (i:=i) (a:=a) sub =>
        let leVar := freeVarUb_bin_le_elimL leE
        let ltI: i < fv.length := Nat.lt_of_succ_le leVar
        let eqI := List.getElem?_eq_getElem ltI
        let ⟨pW, inIr⟩ := inSomeElim (sub.isSound o fv leX leE isIn)
        let ⟨inVarI, inA⟩ := inIrElim inIr
        let eqP := inVarElim inVarI eqI
        inFull p fun p2 =>
          inImpl fun inVar2 =>
            let eqP2 := inVarElim inVar2 eqI
            (eqP.trans eqP2.symm) ▸ inA
      | varFullSome (i:=i) (a:=a) sub =>
        let leVar := freeVarUb_bin_le_elimL leE
        let ltI: i < fv.length := Nat.lt_of_succ_le leVar
        let eqI := List.getElem?_eq_getElem ltI
        let inFull := sub.isSound o fv leX leE isIn
        let inDI_A := inImplElim (inFullElim inFull fv[i]) (inVar eqI)
        inSome p (inIr (inVar eqI) inDI_A)
      | nullSomeFull (a:=a) sub =>
        let ⟨pW, inIr⟩ := inSomeElim (sub.isSound o fv leX leE isIn)
        let ⟨inNullP, inA⟩ := inIrElim inIr
        let eqP := inNullElim inNullP
        inFull p fun p2 =>
          inImpl fun inNull2 =>
            let eqP2 := inNullElim inNull2
            (eqP.trans eqP2.symm) ▸ inA
      | nullFullSome (a:=a) sub =>
        let inFullImplNullA := sub.isSound o fv leX leE isIn
        let inNull_A := inImplElim (inFullElim inFullImplNullA .null) inNull
        inSome p (inIr inNull inNull_A)
      | someProd subA subB =>
        let inSubA :=
          subA.isSound o fv leX (freeVarUb_bin_le_elimL leE) isIn
        let inSubB :=
          subB.isSound o fv leX (freeVarUb_bin_le_elimR leE) isIn
        let ⟨pA, inA⟩ := inSomeElim inSubA
        let ⟨pB, inB⟩ := inSomeElim inSubB
        inSome p (inProd inA inB)
      | prodVarSomeFull (x:=x) (i:=i) (j:=j) (a:=a) sub =>
        let lePairVar := freeVarUb_bin_le_elimL leE
        let leVarI := freeVarUb_bin_le_elimL lePairVar
        let leVarJ := freeVarUb_bin_le_elimR lePairVar
        let ltI: i < fv.length := Nat.lt_of_succ_le leVarI
        let ltJ: j < fv.length := Nat.lt_of_succ_le leVarJ
        let eqI := List.getElem?_eq_getElem ltI
        let eqJ := List.getElem?_eq_getElem ltJ
        let ⟨pW, inIr⟩ := inSomeElim (sub.isSound o fv leX leE isIn)
        let ⟨inProdP, inA⟩ := inIrElim inIr
        let ⟨pA, pB, eqP, inVI, inVJ⟩ := inProdElimEx inProdP
        let eqPA := inVarElim inVI eqI
        let eqPB := inVarElim inVJ eqJ
        inFull p fun p2 =>
          inImpl fun inProd2 =>
            let ⟨pA2, pB2, eqP2, inVI2, inVJ2⟩ := inProdElimEx inProd2
            let eqPA2 := inVarElim inVI2 eqI
            let eqPB2 := inVarElim inVJ2 eqJ
            let p_eq_p2 :=
              (eqP.trans (congrArg₂ Pair.pair eqPA eqPB)).trans
                (eqP2.trans (congrArg₂ Pair.pair eqPA2 eqPB2)).symm
            p_eq_p2 ▸ inA
      | prodMonoFullImpl subL subR =>
        let ⟨leAlAr, leBlBr⟩ := freeVarUb_bin_le_elim leE
        let ⟨leAl, leAr⟩ := freeVarUb_bin_le_elim leAlAr
        let ⟨leBl, leBr⟩ := freeVarUb_bin_le_elim leBlBr
        let leL := freeVarUb_bin_le leAl leBl
        let leR := freeVarUb_bin_le leAr leBr
        inFull p fun pArg =>
          inImpl fun inProdAlAr =>
            let ⟨pA, pB, eq, inAl, inAr⟩ := inProdElimEx inProdAlAr
            eq ▸ inProd
              (inImplElim
                (inFullElim (subL.isSound o fv leX leL isIn) pA) inAl)
              (inImplElim
                (inFullElim (subR.isSound o fv leX leR isIn) pB) inAr)
      | prodIr subA subB =>
        let ⟨leL, leR⟩ := freeVarUb_bin_le_elim leE
        let ⟨leAl, leBl⟩ := freeVarUb_bin_le_elim leL
        let ⟨leAr, leBr⟩ := freeVarUb_bin_le_elim leR
        let inProdAlAr :=
          subA.isSound o fv leX (freeVarUb_bin_le leAl leAr) isIn
        let inProdBlBr :=
          subB.isSound o fv leX (freeVarUb_bin_le leBl leBr) isIn
        let ⟨pA, pB, eq, inAl, inAr⟩ := inProdElimEx inProdAlAr
        let ⟨inBl, inBr⟩ := inProdElim (eq ▸ inProdBlBr)
        eq ▸ inProd (inIr inAl inBl) (inIr inAr inBr)
      | prodArbIrL (a:=a) (b:=b) sub =>
        let ⟨leArbIrA, leB⟩ := freeVarUb_bin_le_elim leE
        let leA := Nat.le_add_of_sub_le leArbIrA
        let leBLift := freeVarUb_le_lift leB
        let leInner := freeVarUb_bin_le leA leBLift
        let leArbIrInner := Nat.sub_le_of_le_add leInner
        let inArbIrArg := sub.isSound o fv leX leArbIrInner isIn
        let ⟨pA, pB, eq, _, inBLift0⟩ := inProdElimEx (inArbIrElim inArbIrArg .null)
        eq ▸ inProd
          (inArbIr fun pX =>
            (inProdElim (eq ▸ inArbIrElim inArbIrArg pX)).left)
          ((intp2_lift_eq b fv [.null] (dl.wfm o) (dl.wfm o) o).symm ▸
          inBLift0)
      | prodArbIrR (a:=a) (b:=b) sub =>
        let ⟨leA, leArbIrB⟩ := freeVarUb_bin_le_elim leE
        let leB := Nat.le_add_of_sub_le leArbIrB
        let leALift := freeVarUb_le_lift leA
        let leInner := freeVarUb_bin_le leALift leB
        let leArbIrInner := Nat.sub_le_of_le_add leInner
        let inArbIrArg := sub.isSound o fv leX leArbIrInner isIn
        let ⟨pA, pB, eq, inALift0, _⟩ := inProdElimEx (inArbIrElim inArbIrArg .null)
        eq ▸ inProd
          ((intp2_lift_eq a fv [.null] (dl.wfm o) (dl.wfm o) o).symm ▸
          inALift0)
          (inArbIr fun pX =>
            (inProdElim (eq ▸ inArbIrElim inArbIrArg pX)).right)
      | complProd sub (a:=a) (b:=b) => fun inProdAB =>
        let ⟨pA, pB, eq, inA, inB⟩ := inProdElimEx inProdAB
        let ⟨leA, leB⟩ := freeVarUb_bin_le_elim leE
        let inPrem := (sub.isSound o).call fv leX p isIn
        (inUnElim inPrem).elim
          (fun inNull =>
            Pair.noConfusion ((inNullElim inNull).symm.trans eq))
          (fun inInner => (inUnElim inInner).elim
            (fun inProdL =>
              let ⟨_, _, eq', inCplA, _⟩ := inProdElimEx inProdL
              let ⟨eqA, _⟩ :=
                Pair.noConfusion (eq.symm.trans eq') And.intro
              (inComplElim inCplA)
                (eqA ▸ intp2_bv_append leA _ ▸ inA))
            (fun inProdR =>
              let ⟨_, _, eq', _, inCplB⟩ := inProdElimEx inProdR
              let ⟨_, eqB⟩ :=
                Pair.noConfusion (eq.symm.trans eq') And.intro
              (inComplElim inCplB)
                (eqB ▸ intp2_bv_append leB _ ▸ inB)))
      | complProdElim sub (a:=a) (b:=b) =>
        let leInner := freeVarUb_bin_le_elimR leE
        let ⟨lePairCA, lePairAC⟩ := freeVarUb_bin_le_elim leInner
        let leA := freeVarUb_bin_le_elimL lePairCA
        let leB := freeVarUb_bin_le_elimR lePairAC
        let leSub := freeVarUb_bin_le leA leB
        match p with
        | .null => inUnL inNull
        | .pair pA pB =>
          (ninProdElim (sub.isSound o fv leX leSub isIn)).elim
            (fun ninA =>
              inUnR (inUnL (inProd (inCompl ninA) inAny)))
            (fun ninB =>
              inUnR (inUnR (inProd inAny (inCompl ninB))))
      | irL sub (r:=r) =>
        let inIr := (sub.isSound o).call fv leX p isIn
        intp_bv_append leE _ ▸ inIrElimL inIr
      | irR sub (l:=l) =>
        let inIr := (sub.isSound o).call fv leX p isIn
        intp_bv_append leE _ ▸ inIrElimR inIr
      | irI ac bc =>
        let ⟨leL, leR⟩ := freeVarUb_bin_le_elim leE
        inIr
          (ac.isSound o fv leX leL isIn)
          (bc.isSound o fv leX leR isIn)
      | complI sub subCpl (a:=a) (b:=b) => fun isInA =>
        let leIr: freeVarUb (.ir x a) ≤ fv.length :=
          Nat.max_le.mpr ⟨leX, leE⟩
        let inIr := inIr isIn isInA
        let inB := (sub.isSound o).call fv leIr p inIr
        let inBCpl := (subCpl.isSound o).call fv leIr p inIr
        inBCpl inB
      | complElim (a:=a) (b:=b) sub subCpl =>
        byContradiction fun ninA =>
          let leIr: freeVarUb (.ir x a.compl) ≤ fv.length :=
            Nat.max_le.mpr ⟨leX, leE⟩
          let inIr := inIr isIn (inCompl ninA)
          let inB := (sub.isSound o).call fv leIr p inIr
          let inBCpl := (subCpl.isSound o).call fv leIr p inIr
          inBCpl inB
      | fullImpl (a:=a) (b:=b) subA =>
        inFull p fun _ =>
          inImpl fun inA =>
            let ⟨leA, leB⟩ := freeVarUb_bin_le_elim leE
            subA.isSound o fv leA leB inA
      | fullImplDist (a:=a) (b:=b) sub =>
        inImpl fun inFullA =>
          inFull _ (fun pB =>
            inImplElim
              (inFullElim (sub.isSound o fv leX leE isIn) pB)
              (inFullElim inFullA pB))
      | fullElim sub => inFullElim (sub.isSound o fv leX leE isIn) p
      | someStripFull (a:=a) sub =>
        (inSomeElim (sub.isSound o fv leX leE isIn)).choose_spec
      | arbIrI sub =>
        fun pX =>
          sub.isSound
            o
            (pX :: fv)
            (freeVarUb_le_lift leX)
            (Nat.le_add_of_sub_le leE)
            (intp_lift_eq x fv [pX] (dl.wfm o) o ▸ isIn)
      | arbIrElim (x:=x) (t:=t) (a:=a) sub isSome isSubsin =>
        let bUb :=
          Nat.max
            a.arbIr.freeVarUb
            (Nat.max t.freeVarUb t.isSubsingleton.freeVarUb)
        let fvPad := fv ++ List.replicate bUb Pair.null
        let padLen: fvPad.length = fv.length + bUb :=
          length_replicate (n := bUb) ▸ length_append
        let lePadX: x.freeVarUb ≤ fvPad.length :=
          padLen ▸ Nat.le_add_right_of_le leX
        let lePadT: t.some.freeVarUb ≤ fvPad.length :=
          padLen ▸
          Nat.le_add_left_of_le
            (le_max_of_le_right (le_max_left _ _))
        let lePadSubsin: t.isSubsingleton.freeVarUb ≤ fvPad.length :=
          padLen ▸
          Nat.le_add_left_of_le
            (le_max_of_le_right (le_max_right _ _))
        let lePadA: a.arbIr.freeVarUb ≤ fvPad.length :=
          padLen ▸ Nat.le_add_left_of_le (Nat.le_max_left _ _)
        let isInPad := intp_bv_append leX _ ▸ isIn
        
        let tIsSub: intp t.isSubsingleton fvPad (dl.wfm o) o p :=
          isSubsin.isSound o fvPad lePadX lePadSubsin isInPad
        
        let ⟨pBound, inT⟩ :=
          inSomeElim (isSome.isSound o fvPad lePadX lePadT isInPad)
        
        let tIntpEq: intp t fvPad (dl.wfm o) o = {pBound} :=
          isSubsingleton_intp_eq tIsSub inT
        
        let inArbIrA := sub.isSound o fvPad lePadX lePadA isInPad
        let inA := inArbIrElim inArbIrA pBound
        let inInst := intp_instantiateVar_eq a t tIntpEq ▸ inA
        
        intp_bv_append leE (List.replicate bUb Pair.null) ▸
        inInst
      
      | noneElim sub =>
        inNoneElim (sub.isSound o fv leX (Nat.zero_le _) isIn)
      | unfold sub =>
        DefList.InWfm.in_def
          (sub.isSound o fv leX (Nat.zero_le _) isIn)
      | fold (c:=c) (lane:=lane) sub =>
        DefList.InWfm.of_in_def
          ((sub.isSound o).call fv leX _ isIn)
      | trans (b:=b) ab bc =>
        let inB := (ab.isSound o).call fv leX _ isIn
        let leB := by
          rw [length_append, length_replicate]
          exact Nat.le_add_left _ _
        let inC := (bc.isSound o).call _ leB _ inB
        by
        rw [List.append_assoc] at inC
        exact intp_bv_append leE _ ▸ inC
      | mutInduction desc premises i =>
        let ubAt i _ isI := freeVarUb (premises ⟨i, isI⟩).conclusion
        let ub := (desc.mapFinIdx ubAt).sum
        let ubAtLe (i: desc.Index): ubAt i desc[i] i.isLt ≤ ub :=
          List.le_sum_of_mem (List.mem_mapFinIdx.mpr ⟨i, i.isLt, rfl⟩)
        let fvPad := fv ++ List.replicate ub Pair.null
        let padLen: fvPad.length = fv.length + ub :=
          length_replicate (n := ub) ▸ length_append
        let lePadX := padLen ▸ Nat.le_add_right_of_le leX
        let isInPad := intp_bv_append leX _ ▸ isIn
        let isSub: dl.SubsetFv _ _ _ _ :=
          desc.isSound
            fvPad
            o
            (fun i =>
              let lePadE :=
                padLen ▸ Nat.le_add_left_of_le (ubAtLe i)
              let premise :=
               (premises i).isSound o fvPad lePadX lePadE
              premise.subsetOfFullImpl isInPad)
            i
        let isInPad := intp_bv_append leX _ ▸ isIn
        intp_bv_append leE _ ▸ isSub.fullImplOfSubset isInPad
      | simplePairInduction (a:=a) (p:=prop) sub =>
        let leE: prop.freeVarUb ≤ fv.length :=
          freeVarUb_bin_le_elimR leE
        let leE :=
          freeVarUb_bin_le
            (freeVarUb_bin_le
              (Nat.zero_le _)
              (freeVarUb_bin_le leE leE))
            leE
        let ind := (sub.isSound o fv leX leE).subsetOfFullImpl isIn
        let rec inP: (p: Pair) → intp prop fv (dl.wfm o) o p
        | Pair.null => ind (inUnL inNull)
        | .pair pa pb => ind (inUnR (inProd (inP pa) (inP pb)))
        DefList.SubsetFv.fullImplOfSubset
          (fun a _ => inP a)
          isIn
end DefList.SubsetStx
