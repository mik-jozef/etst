/-
  TODO chapter description.
-/

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
  isFull {x a}
    (subA: dl.SubsetStx any a)
  :
    dl.SubsetStx x (full a)
|
  -- Axiom K in modal logic.
  fullImplElim {x a b}
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
  /-
    (Almost) the contraposition of Axiom 5 in modal logic.
  -/
  someStripFull {x a}
    (sub: dl.SubsetStx x (some (full a)))
  :
    dl.SubsetStx x (full a)
|
  univIntro {x a}
    (sub: dl.SubsetStx x.lift a)
  :
    dl.SubsetStx x (arbIr a)
-- |
--   univElim {x t a}
--     (isSome: dl.SubsetStx x (some t))
--     (isSubsingle: dl.SubsetStx x t.isSubsingleton)
--     (sub: dl.SubsetStx x (arbIr a))
--   :
--     dl.SubsetStx x (a.instantiateVar t)
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


open SingleLaneExpr in
def DefList.SubsetFv.subsetOfFullImpl {dl fv x a b d}
  (h: SubsetFv dl fv x (.full (.impl a b)))
  (isIn: d ∈ x.intp fv dl.wfm)
:
  dl.SubsetFv fv a b
:=
  fun d' inA => inImplElim (inFullElim (h isIn) d') inA

open SingleLaneExpr in
def DefList.SubsetFv.fullImplOfSubset {dl fv x a b}
  (h: SubsetFv dl fv a b)
:
  SubsetFv dl fv x (.full (.impl a b))
:=
  fun _ _ => inFull .null fun _ => inImpl fun inA => h inA

namespace DefList.SubsetStx
  variable {dl: DefList}
  
  def isSound {x e}
    (sub: dl.SubsetStx x e)
  :
    dl.Subset x e
  :=
    open List in
    open SingleLaneExpr in
    fun fv leX leE p isIn =>
      match sub with
      | subId => isIn
      | defPos sub => Set3.defLePos _ (sub.isSound fv leX leE isIn)
      | irL sub (r:=r) =>
        let bUb := freeVarUb (.ir e r)
        let fvPad := fv ++ List.replicate bUb Pair.null
        let padLen: fvPad.length = fv.length + bUb :=
          length_replicate (n := bUb) ▸ length_append
        let lePadX := padLen ▸ Nat.le_add_right_of_le leX
        let lePadE := padLen ▸ Nat.le_add_left _ _
        let isInPad := intp_bv_append leX _ ▸ isIn
        let isInE := sub.isSound fvPad lePadX lePadE isInPad
        intp_bv_append leE _ ▸ (inIrElimL isInE)
      | irR sub (l:=l) =>
        let bUb := freeVarUb (.ir l e)
        let fvPad := fv ++ List.replicate bUb Pair.null
        let padLen: fvPad.length = fv.length + bUb :=
          length_replicate (n := bUb) ▸ length_append
        let lePadX := padLen ▸ Nat.le_add_right_of_le leX
        let lePadE := padLen ▸ Nat.le_add_left _ _
        let isInPad := x.intp_bv_append leX _ ▸ isIn
        let isInE := sub.isSound fvPad lePadX lePadE isInPad
        intp_bv_append leE _ ▸ (inIrElimR isInE)
      | irI ac bc =>
        let ⟨leL, leR⟩ := freeVarUb_bin_le_elim leE
        inIr
          (ac.isSound fv leX leL isIn)
          (bc.isSound fv leX leR isIn)
      | complI sub subCpl (a:=a) (b:=b) => fun isInA =>
        let bUb := freeVarUb b
        let fvPad := fv ++ replicate bUb Pair.null
        let padLen: fvPad.length = fv.length + bUb :=
          length_replicate (n := bUb) ▸ length_append
        let leIrXA: freeVarUb (.ir x a) ≤ fv.length :=
          Nat.max_le.mpr ⟨leX, leE⟩
        let leIrXA_Pad: freeVarUb (.ir x a) ≤ fvPad.length :=
          padLen ▸ Nat.le_add_right_of_le leIrXA
        let leB_Pad: freeVarUb b ≤ fvPad.length :=
          padLen ▸ Nat.le_add_left _ _
        let leBCpl_Pad: freeVarUb b.compl ≤ fvPad.length := leB_Pad
        let isInIr := inIr isIn isInA
        let isInIrPad :=
          intp2_bv_append leIrXA (replicate bUb Pair.null) ▸ isInIr
        let inB := sub.isSound fvPad leIrXA_Pad leB_Pad isInIrPad
        let inBCpl := subCpl.isSound fvPad leIrXA_Pad leBCpl_Pad isInIrPad
        inBCpl inB
      | complElim (a:=a) (b:=b) sub subCpl =>
        byContradiction fun ninA =>
          let bUB := freeVarUb b
          let fvPad := fv ++ replicate bUB Pair.null
          let padLen: fvPad.length = fv.length + bUB :=
            length_replicate (n := bUB) ▸ length_append
          let leIrXA: freeVarUb (.ir x a.compl) ≤ fv.length :=
            Nat.max_le.mpr ⟨leX, leE⟩
          let leIrXA_Pad: freeVarUb (.ir x a.compl) ≤ fvPad.length :=
            padLen ▸ Nat.le_add_right_of_le leIrXA
          let leB_Pad: freeVarUb b ≤ fvPad.length :=
            padLen ▸ Nat.le_add_left _ _
          let leBCpl_Pad: freeVarUb b.compl ≤ fvPad.length := leB_Pad
          let isInIr := inIr isIn (inCompl ninA)
          let isInIrPad :=
            intp2_bv_append leIrXA (replicate bUB Pair.null) ▸ isInIr
          let inB := sub.isSound fvPad leIrXA_Pad leB_Pad isInIrPad
          let inBCpl := subCpl.isSound fvPad leIrXA_Pad leBCpl_Pad isInIrPad
          inBCpl inB
      | isFull subA =>
        inFull p fun _ => subA.isSound fv (Nat.zero_le _) leE inAny
      | fullImplElim (a:=a) (b:=b) sub =>
        inImpl fun inFullA =>
          inFull _ (fun dB =>
            inImplElim
              (inFullElim (sub.isSound fv leX leE isIn) dB)
              (inFullElim inFullA dB))
      | fullElim sub => inFullElim (sub.isSound fv leX leE isIn) p
      | someStripFull (a:=a) sub =>
        (inSomeElim (sub.isSound fv leX leE isIn)).choose_spec
      | univIntro sub =>
        fun dX =>
          sub.isSound
            (dX :: fv)
            (freeVarUb_le_lift leX)
            (Nat.le_add_of_sub_le leE)
            (intp_lift_eq x fv [dX] dl.wfm ▸ isIn)
      | unfold sub =>
        SingleLaneExpr.InWfm.in_def
          (sub.isSound fv leX (Nat.zero_le _) isIn)
      | fold (c:=c) (lane:=lane) sub =>
        let bUb := freeVarUb ((dl.getDef c).toLane lane)
        let fvPad := fv ++ List.replicate bUb Pair.null
        let padLen: fvPad.length = fv.length + bUb :=
          length_replicate (n := bUb) ▸ length_append
        let lePadX := padLen ▸ Nat.le_add_right_of_le leX
        let lePadE := padLen ▸ Nat.le_add_left _ _
        let isInPad := intp_bv_append leX _ ▸ isIn
        SingleLaneExpr.InWfm.of_in_def
          (sub.isSound fvPad lePadX lePadE isInPad)
      | trans (b:=b) ab bc =>
        let bUb := freeVarUb b
        let fvPad := fv ++ List.replicate bUb Pair.null
        let padLen: fvPad.length = fv.length + bUb :=
          length_replicate (n := bUb) ▸ length_append
        let lePadX := padLen ▸ Nat.le_add_right_of_le leX
        let lePadB := padLen ▸ Nat.le_add_left _ _
        let lePadE := padLen ▸ Nat.le_add_right_of_le leE
        let isInPad := intp_bv_append leX _ ▸ isIn
        let inB := ab.isSound fvPad lePadX lePadB isInPad
        let inC := bc.isSound fvPad lePadB lePadE inB
        intp_bv_append leE _ ▸ inC
      | mutInduction desc premises i =>
        let isSub :=
          MutIndDescriptor.isSound
            desc
            fv
            (fun i =>
              let getUb {expr: SingleLaneExpr}
                (sub: dl.SubsetStx x expr)
              :=
                freeVarUb expr
              let bUb := getUb (premises i)
              let fvPad := fv ++ List.replicate bUb Pair.null
              let padLen: fvPad.length = fv.length + bUb :=
                length_replicate (n := bUb) ▸ length_append
              let lePadX := padLen ▸ Nat.le_add_right_of_le leX
              let lePadE := padLen ▸ Nat.le_add_left _ _
              let isInPad := intp_bv_append leX _ ▸ isIn
              let premise :=
               (premises i).isSound fvPad lePadX lePadE
              let lk := premise.subsetOfFullImpl isInPad
              fun p0 inHyp =>
                -- let lkj := lk inHyp
                sorry)
            i
        DefList.SubsetFv.fullImplOfSubset isSub isIn
      | simplePairInduction (p:=prop) sub =>
        let ind := (sub.isSound fv sorry sorry).subsetOfFullImpl isIn
        let rec inP: (p: Pair) → intp prop fv dl.wfm p
        | Pair.null => ind (inUnL inNull)
        | .pair pa pb => ind (inUnR (inPair (inP pa) (inP pb)))
        DefList.SubsetFv.fullImplOfSubset
          (fun a _ => inP a)
          isIn
end DefList.SubsetStx
