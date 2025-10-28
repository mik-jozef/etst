import Etst.Subtyping.Utils.FixpointMethodsSoundness

namespace Etst
open PairExpr


-- -- Fail to show termination ://///
-- def Subset.isSound:
--   Subset dl a b →
--   IsDefSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
-- |
--   null, _, isIn => isIn
-- | pair sl sr, .pair a b, isIn =>
--   let ⟨inwL, inwR⟩ := inwPairElim isIn
--   insPair (sl.isSound inwL) (sr.isSound inwR)
-- | unL s, _, isIn =>
--   insUnL (s.isSound isIn)
-- | unR s, _, isIn =>
--   insUnR (s.isSound isIn)
-- | fixpointMethods fms premises out, _, isIn =>
--   let premisesHold (i: fms.Index): PremiseHolds fms fms[i] :=
--     match fms[i], premises i with
--     | .induction desc, .ind premise =>
--       PremiseHolds.ind premise.isSound
--     | _, @Premise.coind dl fmsa vf df => sorry
--     | _, @Premise.indCoind dl fmsa vf df => sorry
--   fmsIsSound fms premisesHold out isIn

def PairDl.SubsetStx.isSound
  (sub: SubsetStx dl a b)
:
  dl.Subset a b
:=
  sub.rec
    (motive := fun a b _ => dl.Subset a b)
    (@fun
      | _, .defLane, _, isIn => isIn
      | _, .posLane, _, isIn => isIn.toPos)
    id
    id
    (fun _ isIn => isIn)
    (fun
    | _, _, isSubL, isSubR, .pair _ _, isIn =>
      let ⟨inwL, inwR⟩ := inPairElim isIn
      inPair (isSubL inwL) (isSubR inwR))
    (fun _ isSub _ isIn => inUnL (isSub isIn))
    (fun _ _ isSubAc isSubBc _ isIn =>
      isIn.elim (fun i => isSubAc i) (fun i => isSubBc i))
    (fun _ isSub _ isIn => isSub isIn.symm)
    (fun _ isSub _ isIn => (isSub isIn).symm)
    (fun _ isSub _ isIn => isSub isIn.left)
    (fun _ _ isSubA isSubB _ isIn => inIr (isSubA isIn) (isSubB isIn))
    (fun _ isSub _ isIn => isSub isIn.symm)
    (fun _ isSub _ isIn => (isSub isIn).symm)
    (fun _ isSub _ isInBCompl isInA => isInBCompl (isSub isInA))
    (fun _ isSub _ isIn => isSub (SingleLaneExpr.InWfm.of_in_def isIn))
    (fun _ isSub _ isIn => SingleLaneExpr.InWfm.in_def (isSub isIn))
    (fun _ isSub _ isIn => isSub (SingleLaneExpr.InWfm.in_def isIn))
    (fun _ isSub _ isIn => SingleLaneExpr.InWfm.of_in_def (isSub isIn))
    (fun _ _ out ih _ isIn => MutIndDescriptor.isSound _ ih out isIn)
    (fun _ _ out ih _ isIn => MutCoindDescriptor.isSound _ ih out isIn)
