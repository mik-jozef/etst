import Etst.Subtyping.Utils.FixpointMethodsSoundness

namespace Etst
open Expr


open SingleLaneExpr in
def DefList.SubsetStx.isSound
  (sub: SubsetStx dl ctx a b)
:
  dl.Subset a b
:=
  fun bv d isIn =>
    match sub with
    | subId => isIn
    | subDefPos => Set3.defMem.toPos isIn
    | subPair subL subR =>
        let ⟨_, _, eq, inL, inR⟩ := inPairElimEx isIn
        eq ▸ inPair (subL.isSound bv inL) (subR.isSound bv inR)
    | subIrL => inIrElimL isIn
    | subIrR => inIrElimR isIn
    | subIr subA subB =>
        inIr (subA.isSound bv isIn) (subB.isSound bv isIn)
    | irUnDistL =>
        let ⟨isInUn, isInC⟩ := inIrElim isIn
        (inUnElim isInUn).elim
          (fun isInA => inUnL (inIr isInA isInC))
          (fun isInB => inUnR (inIr isInB isInC))
    | subCompl sub =>
        fun isInA => isIn (sub.isSound bv isInA)
    | dne =>
        Classical.byContradiction isIn
    | dni =>
        fun nin => nin isIn
    | isFull subA =>
        fun _ => subA.isSound bv inAny
    | fullImplElim =>
        inImpl fun inFullA =>
          inCondFull d (fun dB =>
            inImplElim
              (inCondFullElim isIn dB)
              (inCondFullElim inFullA dB))
    | fullElim =>
        isIn _
    | someStripFull =>
        let ⟨_, inFullA⟩ := inCondSomeElim isIn
        inFullA
    | unfold => SingleLaneExpr.InWfm.in_def isIn
    | fold => SingleLaneExpr.InWfm.of_in_def isIn
    | trans ab bc => bc.isSound bv (ab.isSound bv isIn)
    | subPe =>
        let ⟨inA, inAc⟩ := inIrElim isIn
        (inAc inA).elim
    | mutInduction desc premises i =>
        MutIndDescriptor.isSound desc (fun i => (premises i).isSound) i bv isIn
