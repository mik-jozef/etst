import Etst.Subtyping.Utils.FixpointMethodsSoundness

namespace Etst
open PairExpr


-- -- Fail to show termination ://///
-- def Subset.isSound:
--   Subset dl a b →
--   IsDefSubset (a.intp [] dl.wfm) (b.intp [] dl.wfm)
-- |
--   null, _, isPos => isPos
-- | pair sl sr, .pair a b, isPos =>
--   let ⟨inwL, inwR⟩ := inwPairElim isPos
--   insPair (sl.isSound inwL) (sr.isSound inwR)
-- | unL s, _, isPos =>
--   insUnL (s.isSound isPos)
-- | unR s, _, isPos =>
--   insUnR (s.isSound isPos)
-- | fixpointMethods fms premises out, _, isPos =>
--   let premisesHold (i: fms.Index): PremiseHolds fms fms[i] :=
--     match fms[i], premises i with
--     | .induction desc, .ind premise =>
--       PremiseHolds.ind premise.isSound
--     | _, @Premise.coind dl fmsa vf df => sorry
--     | _, @Premise.indCoind dl fmsa vf df => sorry
--   fmsIsSound fms premisesHold out isPos

def Subset.isSound
  (sub: Subset dl a b)
:
  dl.IsDefSubset a b
:=
  sub.rec
    (motive := fun a b _ => dl.IsDefSubset a b)
    (fun _ isPos => isPos)
    (fun
    | _, _, isSubL, isSubR, .pair _ _, isPos =>
      let ⟨inwL, inwR⟩ := inwPairElim isPos
      insPair (isSubL inwL) (isSubR inwR))
    (fun _ _ isSub _ isPos => insUnL (isSub isPos))
    (fun _ _ isSub _ isPos => insUnR (isSub isPos))
    (fun _ _ out ih _ isPos => MutIndDescriptor.isSound _ ih out isPos)
    (fun _ _ out ih _ isPos => MutCoindDescriptor.isSound _ ih out isPos)
