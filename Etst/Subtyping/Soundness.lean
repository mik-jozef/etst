import Etst.Subtyping.Utils.FixpointMethodsSoundness

namespace Etst
open Expr

open SingleLaneExpr in
def DefList.SubsetBv.subsetOfFullImpl {dl fv x a b d}
  (h: SubsetBv dl fv x (SingleLaneExpr.full (SingleLaneExpr.impl a b)))
  (isIn: d ∈ x.intp fv dl.wfm)
:
  dl.SubsetBv fv a b
:=
  fun d' inA =>
    inImplElim (inFullElim (h isIn) d') inA

open SingleLaneExpr in
def DefList.SubsetBv.fullImplOfSubset {dl fv x a b}
  (h: SubsetBv dl fv a b)
:
  SubsetBv dl fv x (SingleLaneExpr.full (SingleLaneExpr.impl a b))
:=
  fun _ _ =>
    inFull .null fun _ =>
      inImpl fun inA =>
        h inA


open SingleLaneExpr in
def DefList.SubsetStx.isSound
  (sub: SubsetStx dl a b)
:
  dl.Subset a b
:=
  fun fv d isIn =>
    match sub with
    | subDefPos => Set3.defMem.toPos isIn
    | pairMono subL subR =>
        inFull .null fun p =>
          inImpl fun inP =>
            match p with
            | .pair pa pb =>
              let ⟨inA, inB⟩ := inPairElim inP
              let inImplA := inFullElim (subL.isSound fv isIn) pa
              let inImplB := inFullElim (subR.isSound fv isIn) pb
              inPair (inImplElim inImplA inA) (inImplElim inImplB inB)
    | subComplPairUn =>
        match d with
        | .null => inUnL inNull
        | .pair _ _ =>
          (ninPairElim isIn).elim
            (fun ninA => inUnR (inUnL (inPair (inCompl ninA) inAny)))
            (fun ninB => inUnR (inUnR (inPair inAny (inCompl ninB))))
    | subUnComplPair =>
        (inUnElim isIn).elim
          (fun inN =>
            let eqNull := inNullElim inN
            eqNull ▸ fun inPair => inPairElimNope inPair)
          (fun inP =>
            (inUnElim inP).elim
              (fun inPA =>
                let ⟨_pA, _pB, eq, inCA, _⟩ := inPairElimEx inPA
                eq ▸ fun inPair =>
                  let ⟨inA, _⟩ := inPairElim inPair
                  inComplElim inCA inA)
              (fun inPB =>
                let ⟨_pA, _pB, eq, _, inCB⟩ := inPairElimEx inPB
                eq ▸ fun inPair =>
                  let ⟨_, inB⟩ := inPairElim inPair
                  inComplElim inCB inB))
    | subPairIrDistL =>
      match d with
      | .pair _ _ =>
        let ⟨isInAc, isInBc⟩ := inIrElim isIn
        let ⟨inA, inC⟩ := inPairElim isInAc
        let ⟨inB, _⟩ := inPairElim isInBc
        inPair (inIr inA inB) inC
    | subPairIrDistR =>
      match d with
      | .pair _ _ =>
        let ⟨isInAb, isInAc⟩ := inIrElim isIn
        let ⟨inA, inB⟩ := inPairElim isInAb
        let ⟨_, inC⟩ := inPairElim isInAc
        inPair inA (inIr inB inC)
    | subIrL => inIrElimL isIn
    | subIrR => inIrElimR isIn
    | subIr subA subB =>
        inIr (subA.isSound fv isIn) (subB.isSound fv isIn)
    | subIrUnDistL =>
        let ⟨isInUn, isInC⟩ := inIrElim isIn
        (inUnElim isInUn).elim
          (fun isInA => inUnL (inIr isInA isInC))
          (fun isInB => inUnR (inIr isInB isInC))
    | fullImplElim =>
        inImpl fun inFullA =>
          inFull d (fun dB =>
            inImplElim
              (inFullElim isIn dB)
              (inFullElim inFullA dB))
    | fullElim =>
        isIn _
    | someStripFull =>
        let ⟨_, inFullA⟩ := inSomeElim isIn
        inFullA
    | subCompl sub =>
        fun isInA => isIn (sub.isSound fv isInA)
    | subDne =>
        Classical.byContradiction isIn
    | subDni =>
        fun nin => nin isIn
    | subPe =>
        let ⟨inA, inAc⟩ := inIrElim isIn
        (inAc inA).elim
    | isFull subA =>
        fun _ => subA.isSound fv inAny
    | univIntro sub =>
        fun dX =>
          let eq := by
            unfold SingleLaneExpr.intp
            rw [intp2_lift_eq a fv [dX] dl.wfm dl.wfm]
            rfl
          sub.isSound
            (dX :: fv)
            (cast eq isIn)
    | univElim (t:=t) (a:=a) isSome isSubsingle sub =>
        let ⟨_dt, inT⟩ := inSomeElim (isSome.isSound fv isIn)
        let ⟨dX, inCond⟩ := inArbUnElim (isSubsingle.isSound fv isIn)
        let inImpl := inFullElim inCond
        
        let tSub: intp t fv dl.wfm ⊆ {dX} := fun z hz =>
          let hz_lift: z ∈ intp t.lift (dX :: fv) dl.wfm :=
            (intp_lift_eq t fv [dX] dl.wfm) ▸ hz
          inImplElim (inImpl z) hz_lift
        
        let tEq: intp t fv dl.wfm = {dX} :=
          Set.eq_singleton_iff_unique_mem.mpr ⟨
             by cases tSub inT; exact inT,
             fun _ hy => tSub hy
          ⟩
        
        intp_instantiateVar_eq a t tEq ▸
        inArbIrElim (sub.isSound fv isIn) dX

    | trans ab bc => bc.isSound fv (ab.isSound fv isIn)
    | subUnfold => SingleLaneExpr.InWfm.in_def isIn
    | subFold => SingleLaneExpr.InWfm.of_in_def isIn
    | mutInduction desc premises i =>
      let isSub :=
        MutIndDescriptor.isSound
          desc
          fv
          (fun i => ((premises i).isSound fv).subsetOfFullImpl isIn)
          i
      isSub.fullImplOfSubset isIn
