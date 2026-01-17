import Etst.Subtyping.Utils.FixpointMethodsSoundness

namespace Etst
open Expr

open SingleLaneExpr in
def DefList.Subset.ofFullImpl {dl x a b dX}
  (h: Subset dl x (.condFull (.impl a b)))
  (isIn: dX ∈ x.intpUnivClosure dl.wfm)
:
  dl.Subset a b
:=
  -- fun d inA =>
  --   inImplElim (inCondFullElim (h isIn) d) inA
  sorry

open SingleLaneExpr in
def DefList.Subset.toFullImpl {dl x a b}
  (h: Subset dl a b)
:
  Subset dl x (.condFull (.impl a b))
:=
  -- fun _ _ bv ubLe =>
  --   inCondFull .null fun _ =>
  --     inImpl fun inA =>
  --       h fun bv' ubLe' => inA
  -- Unsound for Univ ⊆ Univ. 
  -- Requires PointwiseSubset for proper implication introduction.
  sorry


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
    | subIrL (r := r) =>
      let bvPadded: List Pair :=
        bv ++ (List.replicate (b.ir r).freeVarUB .null)
      let bvPaddedLenEq:
        bvPadded.length = bv.length + (b.ir r).freeVarUB
      :=
        List.length_replicate (n := (b.ir r).freeVarUB) ▸
        List.length_append
      let inIr := isIn bvPadded (bvPaddedLenEq ▸ Nat.le_add_left _ _)
      (intp2_bv_append dl ubLe _ _).mpr (inIrElimL inIr)
    | subIrR (l := l) =>
      let bvPadded: List Pair :=
        bv ++ (List.replicate (l.ir b).freeVarUB .null)
      let bvPaddedLenEq:
        bvPadded.length = bv.length + (l.ir b).freeVarUB
      :=
        List.length_replicate (n := (l.ir b).freeVarUB) ▸
        List.length_append
      let inIr := isIn bvPadded (bvPaddedLenEq ▸ Nat.le_add_left _ _)
      (intp2_bv_append dl ubLe _ _).mpr (inIrElimR inIr)
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
    | fullImplElim =>
        inImpl fun inFullA =>
          inCondFull .null fun dB =>
            let inA := inCondFullElim inFullA dB
            let inImpl := inCondFullElim (isIn bv ubLe) dB
            inImplElim inImpl inA
    | fullElim =>
        inCondFullElim (isIn bv ubLe) p
    | someStripFull =>
        let ⟨_q, inFullA⟩ := inCondSomeElim (isIn bv ubLe)
        inFullA
    | subCompl sub (b := b) =>
        -- This rule is unsound for `Subset := Univ ⊆ Univ`.
        --
        -- Counterexample sketch:
        -- Let world be `0, 1` (bool). `bv` has length 1.
        -- Let `A` be `var 0`. `A[0]=False, A[1]=True`. `Univ(A) = False`.
        -- Let `B` be `False`. `B[0]=False, B[1]=False`. `Univ(B) = False`.
        -- `Univ(A) ⊆ Univ(B)` holds (False implies everything).
        -- `A.compl` is `¬(var 0)`. `Ac[0]=True, Ac[1]=False`. `Univ(Ac) = False`.
        -- `B.compl` is `True`. `Bc[0]=True, Bc[1]=True`. `Univ(Bc) = True`.
        -- We expect `Univ(B.compl) ⊆ Univ(A.compl)`, i.e. `True ⊆ False`.
        -- This is False.
        sorry
    | subDne =>
        Classical.byContradiction (isIn bv ubLe)
    | subDni =>
        fun nin => nin (isIn bv ubLe)
    | subPe (a := a) =>
        let ubLeLHS := (a.ir a.compl).freeVarUB
        let bvPadded: List Pair := bv ++ (List.replicate ubLeLHS .null)
        let bvPaddedLenEq:
          bvPadded.length = bv.length + ubLeLHS
        :=
          List.length_replicate (n := ubLeLHS) ▸
          List.length_append
        let lePadded :=
          bvPaddedLenEq ▸ Nat.le_add_left _ _
        let ⟨inA, inAc⟩ := inIrElim (isIn bvPadded lePadded)
        (inComplElim inAc inA).elim
    | isFull subA =>
        inCondFull .null fun _ =>
          subA.isSound (fun _ _ => inAny) bv ubLe
    -- | subArbIr => -- IGNORE --
    --   fun dX =>
    --     sorry
    | trans ab bc => bc.isSound (ab.isSound isIn) bv ubLe
    | subUnfold => InWfm.in_def (isIn [] (Nat.zero_le _))
    | subFold (a := a) (lane := lane) =>
        let df := (dl.getDef a).toLane lane
        let bv' := List.replicate df.freeVarUB Pair.null
        let ubLe :=
          List.length_replicate ▸ Nat.le_refl _
        InWfm.of_in_def (isIn bv' ubLe)
    | mutInduction desc premises i =>
        let isSub :=
          MutIndDescriptor.isSound
            desc
            (fun j => (premises j).isSound.ofFullImpl isIn)
            i
        isSub.toFullImpl isIn bv ubLe
