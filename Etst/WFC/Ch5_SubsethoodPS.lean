/-
  TODO chapter description.
-/

import Mathlib.Algebra.Order.BigOperators.Group.List

import Etst.WFC.Ch4_S1_MembershipPS
import Etst.WFC.Utils.RulesOfInference
import Etst.WFC.Utils.SubsetStx.Induction

namespace Etst
open Expr


-- Semantic entailment for a given assignment of variables.
abbrev DefList.SubsetFv
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
  ∀ fv,
    a.freeVarUb ≤ fv.length →
    b.freeVarUb ≤ fv.length →
    dl.SubsetFv fv a b


def Expr.isSubsingleton_body {E} (e: Expr E): Expr E :=
  impl (some (ir e.lift (var 0))) (full (impl e.lift (var 0)))

def Expr.isSubsingleton {E} (e: Expr E) : Expr E :=
  arbIr (e.isSubsingleton_body)

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
  somePair {x a b}
    (subA: dl.SubsetStx x (some a))
    (subB: dl.SubsetStx x (some b))
  :
    dl.SubsetStx x (some (pair a b))
|
  pairSubsingleton {x a b}
    (subA: dl.SubsetStx x a.isSubsingleton)
    (subB: dl.SubsetStx x b.isSubsingleton)
  :
    dl.SubsetStx x (pair a b).isSubsingleton
|
  -- TODO replace with pairMono and derive?
  pairMonoFullImpl {x al bl ar br}
    (sl: dl.SubsetStx x (full (impl al bl)))
    (sr: dl.SubsetStx x (full (impl ar br)))
  :
    dl.SubsetStx x (full (impl (pair al ar) (pair bl br)))
|
  pairIr {x al bl ar br}
    (subA: dl.SubsetStx x (pair al ar))
    (subB: dl.SubsetStx x (pair bl br))
  :
    dl.SubsetStx x (pair (ir al bl) (ir ar br))
|
  pairArbIrL {x a b}
    (sub: dl.SubsetStx x (arbIr (pair a b.lift)))
  :
    dl.SubsetStx x (pair (arbIr a) b)
|
  pairArbIrR {x a b}
    (sub: dl.SubsetStx x (arbIr (pair a.lift b)))
  :
    dl.SubsetStx x (pair a (arbIr b))
|
  complPair {x a b}
    (sub:
      dl.SubsetStx
        x
        (un null (un (pair (compl a) any) (pair any (compl b)))))
  :
    dl.SubsetStx x (compl (pair a b))
|
  complPairElim {x a b}
    (sub: dl.SubsetStx x (compl (pair a b)))
  :
    dl.SubsetStx
      x
      (un null (un (pair (compl a) any) (pair any (compl b))))
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
  isFullImpl {x a b}
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
    (sub: dl.SubsetStx x (full (impl (un null (pair p p)) p)))
  :
    dl.SubsetStx x (full (impl a p))


def DefList.SubsetFv.subsetOfFullImpl {dl fv x a b d}
  (h: SubsetFv dl fv x (.full (.impl a b)))
  (isIn: d ∈ x.intp fv dl.wfm)
:
  dl.SubsetFv fv a b
:=
  open SingleLaneExpr in
  fun d' inA => inImplElim (inFullElim (h isIn) d') inA

def DefList.SubsetFv.fullImplOfSubset {dl fv x a b}
  (h: SubsetFv dl fv a b)
:
  SubsetFv dl fv x (.full (.impl a b))
:=
  open SingleLaneExpr in
  fun _ _ => inFull .null fun _ => inImpl fun inA => h inA

def DefList.Subset.call {dl a b}
  (sub: Subset dl a b)
  (fv: List Pair)
  (leA: a.freeVarUb ≤ fv.length)
  (d: Pair)
  (isIn: d ∈ a.intp fv dl.wfm)
:
  d ∈ b.intp (fv ++ List.replicate b.freeVarUb Pair.null) dl.wfm
:=
  let fvPad := fv ++ List.replicate b.freeVarUb Pair.null
  let padLen: fvPad.length = fv.length + b.freeVarUb :=
    List.length_replicate (n := b.freeVarUb) ▸ List.length_append
  let leAPad: a.freeVarUb ≤ fvPad.length :=
    padLen ▸ Nat.le_add_right_of_le leA
  let leBPad: b.freeVarUb ≤ fvPad.length :=
    padLen ▸ Nat.le_add_left _ _
  let isInPad: d ∈ a.intp fvPad dl.wfm :=
    SingleLaneExpr.intp_bv_append leA _ ▸ isIn
  sub fvPad leAPad leBPad isInPad


def SingleLaneExpr.isSubsingleton_intp_eq
  {expr fv v d dS}
  (inSubs: intp expr.isSubsingleton fv v dS)
  (inExpr: intp expr fv v d)
:
  intp expr fv v = {d}
:=
  Set.eq_singleton_iff_unique_mem.mpr
    (And.intro
      inExpr
      (fun dE isIn =>
        inVarElim
          (inImplElim
            (inImplElim
              (inArbIrElim inSubs d)
              (inSome
                .null
                (inIr
                  (intp2_lift_eq expr fv [d] v v ▸ inExpr)
                  (inVar rfl)))
              dE)
            (intp2_lift_eq expr fv [d] v v ▸ isIn))
          rfl))

namespace DefList.SubsetStx
  variable {dl: DefList}
  
  def context {x e} (_: SubsetStx dl x e) := x
  def conclusion {x e} (_: SubsetStx dl x e) := e
  
  def isSound {x e}
    (sub: dl.SubsetStx x e)
  :
    dl.Subset x e
  :=
    open List SingleLaneExpr in
    fun fv leX leE p isIn =>
      match sub with
      | subId => isIn
      | defPos sub => Set3.defLePos _ (sub.isSound fv leX leE isIn)
      | varSomeFull (i:=i) (a:=a) sub =>
        let leVar := freeVarUb_bin_le_elimL leE
        let ltI: i < fv.length := Nat.lt_of_succ_le leVar
        let eqI := List.getElem?_eq_getElem ltI
        let ⟨d, inIr⟩ := inSomeElim (sub.isSound fv leX leE isIn)
        let ⟨inVarI, inA⟩ := inIrElim inIr
        let eqD := inVarElim inVarI eqI
        inFull p fun d2 =>
          inImpl fun inVar2 =>
            let eqD2 := inVarElim inVar2 eqI
            (eqD.trans eqD2.symm) ▸ inA
      | varFullSome (i:=i) (a:=a) sub =>
        let leVar := freeVarUb_bin_le_elimL leE
        let ltI: i < fv.length := Nat.lt_of_succ_le leVar
        let eqI := List.getElem?_eq_getElem ltI
        let inFull := sub.isSound fv leX leE isIn
        let inDI_A := inImplElim (inFullElim inFull fv[i]) (inVar eqI)
        inSome p (inIr (inVar eqI) inDI_A)
      | nullSomeFull (a:=a) sub =>
        let ⟨d, inIr⟩ := inSomeElim (sub.isSound fv leX leE isIn)
        let ⟨inNullD, inA⟩ := inIrElim inIr
        let eqD := inNullElim inNullD
        inFull p fun d2 =>
          inImpl fun inNull2 =>
            let eqD2 := inNullElim inNull2
            (eqD.trans eqD2.symm) ▸ inA
      | nullFullSome (a:=a) sub =>
        let inFullImplNullA := sub.isSound fv leX leE isIn
        let inNull_A := inImplElim (inFullElim inFullImplNullA .null) inNull
        inSome p (inIr inNull inNull_A)
      | somePair subA subB =>
        let inSubA :=
          subA.isSound fv leX (freeVarUb_bin_le_elimL leE) isIn
        let inSubB :=
          subB.isSound fv leX (freeVarUb_bin_le_elimR leE) isIn
        let ⟨dA, inA⟩ := inSomeElim inSubA
        let ⟨dB, inB⟩ := inSomeElim inSubB
        inSome p (inPair inA inB)
      | pairSubsingleton (x:=x) (a:=a) (b:=b) subA subB =>
        let bUb :=
          Nat.max
            a.isSubsingleton.freeVarUb
            b.isSubsingleton.freeVarUb
        let pad := List.replicate bUb Pair.null
        let fvPad := fv ++ pad
        let padLen: fvPad.length = fv.length + bUb :=
          List.length_replicate (n := bUb) ▸ List.length_append
        let lePadX: x.freeVarUb ≤ fvPad.length :=
          padLen ▸ Nat.le_add_right_of_le leX
        let lePadA: a.isSubsingleton.freeVarUb ≤ fvPad.length :=
          padLen ▸ Nat.le_add_left_of_le (Nat.le_max_left _ _)
        let lePadB: b.isSubsingleton.freeVarUb ≤ fvPad.length :=
          padLen ▸ Nat.le_add_left_of_le (Nat.le_max_right _ _)
        let lePair d: (a.pair b).lift.freeVarUb ≤ (d :: fv).length :=
          freeVarUb_bin_le_elimL
            (freeVarUb_bin_le_elimL
              (Nat.le_add_of_sub_le leE))
        let leA: a.freeVarUb ≤ fv.length :=
          freeVarUb_le_of_lift
            (freeVarUb_bin_le_elimL (lePair .null))
        let leB: b.freeVarUb ≤ fv.length :=
          freeVarUb_le_of_lift
            (freeVarUb_bin_le_elimR (lePair .null))
        
        let isInPad := intp_bv_append leX _ ▸ isIn
        let aIsSub: intp a.isSubsingleton fvPad dl.wfm p :=
          subA.isSound fvPad lePadX lePadA isInPad
        let bIsSub: intp b.isSubsingleton fvPad dl.wfm p :=
          subB.isSound fvPad lePadX lePadB isInPad
        let eqOfInA d (ife: intp a fvPad dl.wfm d)
        :=
          isSubsingleton_intp_eq aIsSub ife
        
        inArbIr fun dB =>
          inImpl fun inSome =>
            let ⟨dab0, ⟨inPairLift0, isInVar⟩⟩ := inSomeElim inSome
            match dab0 with
            | .null => inPairElimNope inPairLift0
            | .pair da0 db0 =>
              let inPair0 := (intp2_lift_eq _ _ [dB] _ _).symm ▸ inPairLift0
              let ⟨inA0, inB0⟩ := inPairElim inPair0
              let eqDb := inVarElim isInVar rfl
              inFull p fun dab1 =>
                inImpl fun (inPairLift1: intp (a.pair b).lift (dB :: fv) dl.wfm dab1) =>
                  let inPair1: intp (.pair a b) fvPad dl.wfm dab1 :=
                    intp_lift_eq _ fvPad [dB] dl.wfm ▸
                    List.append_assoc _ _ _ ▸
                    intp_bv_append (lePair dB) _ ▸
                    inPairLift1
                  match h1: dab1 with
                  | .null => inPairElimNope (h1 ▸ inPair1)
                  | .pair da1 db1 =>
                    let ⟨inA1, inB1⟩ := inPairElim (h1 ▸ inPair1)
                    let eqA1: intp2 a fv dl.wfm dl.wfm = {da1} :=
                      intp2_bv_append leA _ ▸
                      isSubsingleton_intp_eq aIsSub inA1
                    let eqB1: intp2 b fv dl.wfm dl.wfm = {db1} :=
                      intp2_bv_append leB _ ▸
                      isSubsingleton_intp_eq bIsSub inB1
                    let inA0 := by rw [eqA1] at inA0; exact inA0.symm
                    let inB0 := by rw [eqB1] at inB0; exact inB0.symm
                    eqDb ▸
                    congr (congr rfl inA0) inB0
      | pairMonoFullImpl subL subR =>
        let ⟨leAlAr, leBlBr⟩ := freeVarUb_bin_le_elim leE
        let ⟨leAl, leAr⟩ := freeVarUb_bin_le_elim leAlAr
        let ⟨leBl, leBr⟩ := freeVarUb_bin_le_elim leBlBr
        let leL := freeVarUb_bin_le leAl leBl
        let leR := freeVarUb_bin_le leAr leBr
        inFull p fun d =>
          inImpl fun inPairAlAr =>
            let ⟨pA, pB, eq, inAl, inAr⟩ := inPairElimEx inPairAlAr
            eq ▸ inPair
              (inImplElim
                (inFullElim (subL.isSound fv leX leL isIn) pA) inAl)
              (inImplElim
                (inFullElim (subR.isSound fv leX leR isIn) pB) inAr)
      | pairIr subA subB =>
        let ⟨leL, leR⟩ := freeVarUb_bin_le_elim leE
        let ⟨leAl, leBl⟩ := freeVarUb_bin_le_elim leL
        let ⟨leAr, leBr⟩ := freeVarUb_bin_le_elim leR
        let inPairAlAr :=
          subA.isSound fv leX (freeVarUb_bin_le leAl leAr) isIn
        let inPairBlBr :=
          subB.isSound fv leX (freeVarUb_bin_le leBl leBr) isIn
        let ⟨pA, pB, eq, inAl, inAr⟩ := inPairElimEx inPairAlAr
        let ⟨inBl, inBr⟩ := inPairElim (eq ▸ inPairBlBr)
        eq ▸ inPair (inIr inAl inBl) (inIr inAr inBr)
      | pairArbIrL (a:=a) (b:=b) sub =>
        let ⟨leArbIrA, leB⟩ := freeVarUb_bin_le_elim leE
        let leA := Nat.le_add_of_sub_le leArbIrA
        let leBLift := freeVarUb_le_lift leB
        let leInner := freeVarUb_bin_le leA leBLift
        let leArbIrInner := Nat.sub_le_of_le_add leInner
        let inArbIrArg := sub.isSound fv leX leArbIrInner isIn
        let ⟨pA, pB, eq, _, inBLift0⟩ := inPairElimEx (inArbIrElim inArbIrArg .null)
        eq ▸ inPair
          (inArbIr fun d =>
            (inPairElim (eq ▸ inArbIrElim inArbIrArg d)).left)
          ((intp2_lift_eq b fv [.null] dl.wfm dl.wfm).symm ▸ inBLift0)
      | pairArbIrR (a:=a) (b:=b) sub =>
        let ⟨leA, leArbIrB⟩ := freeVarUb_bin_le_elim leE
        let leB := Nat.le_add_of_sub_le leArbIrB
        let leALift := freeVarUb_le_lift leA
        let leInner := freeVarUb_bin_le leALift leB
        let leArbIrInner := Nat.sub_le_of_le_add leInner
        let inArbIrArg := sub.isSound fv leX leArbIrInner isIn
        let ⟨pA, pB, eq, inALift0, _⟩ := inPairElimEx (inArbIrElim inArbIrArg .null)
        eq ▸ inPair
          ((intp2_lift_eq a fv [.null] dl.wfm dl.wfm).symm ▸ inALift0)
          (inArbIr fun d =>
            (inPairElim (eq ▸ inArbIrElim inArbIrArg d)).right)
      | complPair sub (a:=a) (b:=b) => fun inPairAB =>
        let ⟨pA, pB, eq, inA, inB⟩ := inPairElimEx inPairAB
        let ⟨leA, leB⟩ := freeVarUb_bin_le_elim leE
        let inPrem := sub.isSound.call fv leX p isIn
        (inUnElim inPrem).elim
          (fun inNull =>
            Pair.noConfusion ((inNullElim inNull).symm.trans eq))
          (fun inInner => (inUnElim inInner).elim
            (fun inPairL =>
              let ⟨_, _, eq', inCplA, _⟩ := inPairElimEx inPairL
              let ⟨eqA, _⟩ :=
                Pair.noConfusion (eq.symm.trans eq') And.intro
              (inComplElim inCplA)
                (eqA ▸ intp2_bv_append leA _ ▸ inA))
            (fun inPairR =>
              let ⟨_, _, eq', _, inCplB⟩ := inPairElimEx inPairR
              let ⟨_, eqB⟩ :=
                Pair.noConfusion (eq.symm.trans eq') And.intro
              (inComplElim inCplB)
                (eqB ▸ intp2_bv_append leB _ ▸ inB)))
      | complPairElim sub (a:=a) (b:=b) =>
        let leInner := freeVarUb_bin_le_elimR leE
        let ⟨lePairCA, lePairAC⟩ := freeVarUb_bin_le_elim leInner
        let leA := freeVarUb_bin_le_elimL lePairCA
        let leB := freeVarUb_bin_le_elimR lePairAC
        let leSub := freeVarUb_bin_le leA leB
        match p with
        | .null => inUnL inNull
        | .pair pA pB =>
          (ninPairElim (sub.isSound fv leX leSub isIn)).elim
            (fun ninA =>
              inUnR (inUnL (inPair (inCompl ninA) inAny)))
            (fun ninB =>
              inUnR (inUnR (inPair inAny (inCompl ninB))))
      | irL sub (r:=r) =>
        let inIr := sub.isSound.call fv leX p isIn
        intp_bv_append leE _ ▸ inIrElimL inIr
      | irR sub (l:=l) =>
        let inIr := sub.isSound.call fv leX p isIn
        intp_bv_append leE _ ▸ inIrElimR inIr
      | irI ac bc =>
        let ⟨leL, leR⟩ := freeVarUb_bin_le_elim leE
        inIr
          (ac.isSound fv leX leL isIn)
          (bc.isSound fv leX leR isIn)
      | complI sub subCpl (a:=a) (b:=b) => fun isInA =>
        let leIr: freeVarUb (.ir x a) ≤ fv.length :=
          Nat.max_le.mpr ⟨leX, leE⟩
        let inIr := inIr isIn isInA
        let inB := sub.isSound.call fv leIr p inIr
        let inBCpl := subCpl.isSound.call fv leIr p inIr
        inBCpl inB
      | complElim (a:=a) (b:=b) sub subCpl =>
        byContradiction fun ninA =>
          let leIr: freeVarUb (.ir x a.compl) ≤ fv.length :=
            Nat.max_le.mpr ⟨leX, leE⟩
          let inIr := inIr isIn (inCompl ninA)
          let inB := sub.isSound.call fv leIr p inIr
          let inBCpl := subCpl.isSound.call fv leIr p inIr
          inBCpl inB
      | isFullImpl (a:=a) (b:=b) subA =>
        inFull p fun _ =>
          inImpl fun inA =>
            let ⟨leA, leB⟩ := freeVarUb_bin_le_elim leE
            subA.isSound fv leA leB inA
      | fullImplDist (a:=a) (b:=b) sub =>
        inImpl fun inFullA =>
          inFull _ (fun dB =>
            inImplElim
              (inFullElim (sub.isSound fv leX leE isIn) dB)
              (inFullElim inFullA dB))
      | fullElim sub => inFullElim (sub.isSound fv leX leE isIn) p
      | someStripFull (a:=a) sub =>
        (inSomeElim (sub.isSound fv leX leE isIn)).choose_spec
      | arbIrI sub =>
        fun dX =>
          sub.isSound
            (dX :: fv)
            (freeVarUb_le_lift leX)
            (Nat.le_add_of_sub_le leE)
            (intp_lift_eq x fv [dX] dl.wfm ▸ isIn)
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
        
        let tIsSub: intp t.isSubsingleton fvPad dl.wfm p :=
          isSubsin.isSound fvPad lePadX lePadSubsin isInPad
        
        let ⟨dBound, inT⟩ :=
          inSomeElim (isSome.isSound fvPad lePadX lePadT isInPad)
        
        let tIntpEq: intp t fvPad dl.wfm = {dBound} :=
          isSubsingleton_intp_eq tIsSub inT
        
        let inArbIrA := sub.isSound fvPad lePadX lePadA isInPad
        let inA := inArbIrElim inArbIrA dBound
        let inInst := intp_instantiateVar_eq a t tIntpEq ▸ inA
        
        intp_bv_append leE (List.replicate bUb Pair.null) ▸
        inInst
      
      | noneElim sub =>
        inNoneElim (sub.isSound fv leX (Nat.zero_le _) isIn)
      | unfold sub =>
        SingleLaneExpr.InWfm.in_def
          (sub.isSound fv leX (Nat.zero_le _) isIn)
      | fold (c:=c) (lane:=lane) sub =>
        SingleLaneExpr.InWfm.of_in_def
          (sub.isSound.call fv leX _ isIn)
      | trans (b:=b) ab bc =>
        let inB := ab.isSound.call fv leX _ isIn
        let leB := by
          rw [length_append, length_replicate]
          exact Nat.le_add_left _ _
        let inC := bc.isSound.call _ leB _ inB
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
        let isSub: dl.SubsetFv _ _ _ :=
          MutIndDescriptor.isSound
            desc
            fvPad
            (fun i =>
              let lePadE :=
                padLen ▸ Nat.le_add_left_of_le (ubAtLe i)
              let premise :=
               (premises i).isSound fvPad lePadX lePadE
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
        let ind := (sub.isSound fv leX leE).subsetOfFullImpl isIn
        let rec inP: (p: Pair) → intp prop fv dl.wfm p
        | Pair.null => ind (inUnL inNull)
        | .pair pa pb => ind (inUnR (inPair (inP pa) (inP pb)))
        DefList.SubsetFv.fullImplOfSubset
          (fun a _ => inP a)
          isIn
end DefList.SubsetStx
