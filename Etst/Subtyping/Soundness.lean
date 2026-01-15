import Etst.Subtyping.Utils.FixpointMethodsSoundness

namespace Etst
open Expr

open SingleLaneExpr in
def DefList.SubsetBv.subsetOfFullImpl {dl bv x a b d}
  (h: SubsetBv dl bv x (SingleLaneExpr.condFull (SingleLaneExpr.impl a b)))
  (isIn: d ∈ x.intp bv dl.wfm)
:
  dl.SubsetBv bv a b
:=
  fun d' inA =>
    inImplElim (inCondFullElim (h isIn) d') inA

open SingleLaneExpr in
def DefList.SubsetBv.fullImplOfSubset {dl bv x a b}
  (h: SubsetBv dl bv a b)
:
  SubsetBv dl bv x (SingleLaneExpr.condFull (SingleLaneExpr.impl a b))
:=
  fun _ _ =>
    inCondFull .null fun _ =>
      inImpl fun inA =>
        h inA


open SingleLaneExpr in
def DefList.SubsetStx.isSound
  (sub: SubsetStx dl ctx a b)
:
  dl.Subset a b
:=
  fun p isIn bv ubLe =>
    match sub with
    | subId => isIn bv ubLe
    | subDefPos => Set3.defMem.toPos (isIn bv ubLe)
    | pairMono (al := al) (ar := ar) (bl := bl) (br := br) subL subR =>
        inCondFull .null fun p =>
          inImpl fun inP =>
            match p with
            | .pair pa pb =>
              let ⟨inA, inB⟩ := inPairElim inP
              let ⟨ubLeA, ubLeB⟩ := freeVarUB_un_le_elim ubLe
              let ubLeL :=
                freeVarUB_un_le
                  (freeVarUB_pair_le_left ubLeA)
                  (freeVarUB_pair_le_left ubLeB)
              let ubLeR: (ar.impl br).freeVarUB ≤ bv.length :=
                freeVarUB_un_le
                  (freeVarUB_pair_le_rite ubLeA)
                  (freeVarUB_pair_le_rite ubLeB)
              let inImplA :=
                inCondFullElim (subL.isSound isIn bv ubLeL) pa
              let inImplB :=
                inCondFullElim (subR.isSound isIn bv ubLeR) pb
              inPair (inImplElim inImplA inA) (inImplElim inImplB inB)
    | subComplPairUn =>
        match p with
        | .null => inUnL inNull
        | .pair _ _ =>
          let ⟨ubLeL, ubLeR⟩ :=
            freeVarUB_un_le_elim (freeVarUB_un_le_rite ubLe)
          let ubLe :=
            freeVarUB_pair_le
              (freeVarUB_pair_le_left ubLeL)
              (freeVarUB_pair_le_rite ubLeR)
          (ninPairElim (isIn bv ubLe)).elim
            (fun ninA => inUnR (inUnL (inPair (inCompl ninA) inAny)))
            (fun ninB => inUnR (inUnR (inPair inAny (inCompl ninB))))
    | subUnComplPair =>
        let ⟨unLeL, unLeR⟩ := freeVarUB_un_le_elim ubLe
        let ubLe :=
          freeVarUB_un_le
            freeVarUB_null_le
            (freeVarUB_un_le
              (freeVarUB_pair_le
                unLeL
                freeVarUB_any_le)
              unLeR)
        (inUnElim (isIn bv ubLe)).elim
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
      let ⟨ubLeIrAB, ubLeC⟩ := freeVarUB_pair_le_elim ubLe
      let ubLeSrc :=
        freeVarUB_ir_le
          (freeVarUB_pair_le (freeVarUB_ir_le_left ubLeIrAB) ubLeC)
          (freeVarUB_pair_le (freeVarUB_ir_le_rite ubLeIrAB) ubLeC)
      match p with
      | .null =>
        inPairElimNope (inIrElimL (isIn bv ubLeSrc))
      | .pair pa pc =>
        let ⟨inAC, inBC⟩ := inIrElim (isIn bv ubLeSrc)
        let ⟨inA, inC⟩ := inPairElim inAC
        let ⟨inB, _⟩ := inPairElim inBC
        inPair (inIr inA inB) inC
    | subPairIrDistR =>
      let ⟨ubLeA, ubLeIrBC⟩ := freeVarUB_pair_le_elim ubLe
      let ubLeSrc :=
        freeVarUB_ir_le
          (freeVarUB_pair_le ubLeA (freeVarUB_ir_le_left ubLeIrBC))
          (freeVarUB_pair_le ubLeA (freeVarUB_ir_le_rite ubLeIrBC))
      match p with
      | .null =>
        inPairElimNope (inIrElimL (isIn bv ubLeSrc))
      | .pair pa pc =>
        let ⟨inAB, inAC⟩ := inIrElim (isIn bv ubLeSrc)
        let ⟨inA, inB⟩ := inPairElim inAB
        let ⟨_, inC⟩ := inPairElim inAC
        inPair inA (inIr inB inC)
    | subIrL =>
      let ubLeSrc := freeVarUB_ir_le ubLe sorry
      inIrElimL (isIn bv ubLeSrc)
    | subIrR =>
      inIrElimR (isIn bv sorry)
    | subIr subA subB =>
      inIr (subA.isSound isIn bv (freeVarUB_ir_le_left ubLe))
           (subB.isSound isIn bv (freeVarUB_ir_le_rite ubLe))
    | subIrUnDistL =>
        let ubLeSrc :=
          freeVarUB_ir_le
            (freeVarUB_un_le
              (freeVarUB_ir_le_left (freeVarUB_un_le_left ubLe))
              (freeVarUB_ir_le_left (freeVarUB_un_le_rite ubLe)))
            (freeVarUB_ir_le_rite (freeVarUB_un_le_left ubLe))
        let ⟨isInUn, isInC⟩ := inIrElim (isIn bv ubLeSrc)
        (inUnElim isInUn).elim
          (fun isInA => inUnL (inIr isInA isInC))
          (fun isInB => inUnR (inIr isInB isInC))
    -- | fullImplElim =>
    --     inImpl fun inFullA =>
    --       inCondFull d (fun dB =>
    --         inImplElim
    --           (inCondFullElim isIn dB)
    --           (inCondFullElim inFullA dB))
    -- | fullElim =>
    --     isIn _
    -- | someStripFull =>
    --     let ⟨_, inFullA⟩ := inCondSomeElim isIn
    --     inFullA
    -- | subCompl sub =>
    --     fun isInA => isIn (sub.isSound bv isInA)
    -- | subDne =>
    --     Classical.byContradiction isIn
    -- | subDni =>
    --     fun nin => nin isIn
    -- | subPe =>
    --     let ⟨inA, inAc⟩ := inIrElim isIn
    --     (inAc inA).elim
    -- | isFull subA =>
    --     fun _ => subA.isSound bv inAny
    -- | trans ab bc => bc.isSound bv (ab.isSound bv isIn)
    -- | subUnfold => SingleLaneExpr.InWfm.in_def isIn
    -- | subFold => SingleLaneExpr.InWfm.of_in_def isIn
    -- | mutInduction desc premises i =>
    --   let isSub :=
    --     MutIndDescriptor.isSound
    --       desc
    --       bv
    --       (fun i => ((premises i).isSound bv).subsetOfFullImpl isIn)
    --       i
    --   isSub.fullImplOfSubset isIn
