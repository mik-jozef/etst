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


def Expr.isSubsingleton {E}
  (e: Expr E)
:
  Expr E
:=
  impl (some (ir e.lift (var 0))) (full (impl e.lift (var 0)))


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
  arbIrI {x a}
    (sub: dl.SubsetStx x.lift a)
  :
    dl.SubsetStx x (arbIr a)
|
  arbIrElim {x t a}
    (isSome: dl.SubsetStx x (some t))
    (isSubsingle: dl.SubsetStx x.lift t.isSubsingleton)
    (sub: dl.SubsetStx x (arbIr a))
  :
    dl.SubsetStx x (a.instantiateVar t)
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
  {expr d fv v}
  (isSubs: ∀ dB, ∃ d, intp expr.isSubsingleton (dB :: fv) v d)
  (isIn: d ∈ intp expr fv v)
:
  intp expr fv v = {d}
:=
  let isInLifted := intp2_lift_eq expr fv [d] v v ▸ isIn
  let ⟨_, isInSubs⟩ := isSubs d
  Set.eq_singleton_iff_unique_mem.mpr
    (And.intro
      isIn
      (fun d isIn =>
        inVarElim
          (inImplElim
            (inImplElim
              isInSubs
              (inSome
                .null
                (inIr
                  isInLifted
                  (inVar rfl)))
              d)
            (intp2_lift_eq expr fv [_] v v ▸ isIn))
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
      | arbIrElim (x:=x) (t:=t) (a:=a) isSome isSubsin sub =>
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
        
        let tIsSub d: intp t.isSubsingleton (d :: fvPad) dl.wfm p :=
          isSubsin.isSound
            (d :: fvPad)
            (freeVarUb_le_lift lePadX)
            (lePadSubsin.trans (Nat.le_succ _))
            (intp_lift_eq x fvPad [d] _ ▸ isInPad)
        
        let ⟨dBound, inT⟩ :=
          inSomeElim (isSome.isSound fvPad lePadX lePadT isInPad)
        
        let tIntpEq :=
          isSubsingleton_intp_eq
            (fun d => List.cons_append ▸ ⟨p, tIsSub d⟩)
            inT
        
        let inArbIrA := sub.isSound fvPad lePadX lePadA isInPad
        let inA := inArbIrElim inArbIrA dBound
        let inInst := intp_instantiateVar_eq a t tIntpEq ▸ inA
        
        intp_bv_append leE (List.replicate bUb Pair.null) ▸
        inInst

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
