import Etst.Subtyping.Utils.FixpointMethodsSoundness
import Etst.Subtyping.UnivStx

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
    (fun _ _ isSubA isSubB _ _ =>
      let ⟨_, inA⟩ := isSubA ⟨.null, rfl⟩
      let ⟨_, inCondB⟩ := isSubB inA
      ⟨_, inCondB⟩)
    (fun _ _ => ⟨.null, rfl⟩)
    (fun _ _ isSubL isSubR _ _ =>
      let ⟨_, inL⟩ := isSubL ⟨.null, rfl⟩
      let ⟨_, inR⟩ := isSubR ⟨.null, rfl⟩
      ⟨_, ⟨⟨_, inL⟩, ⟨⟨_, inR⟩, rfl⟩⟩⟩)
    (fun _ _ ab a _ _ =>
      let ⟨_, inA⟩ := a ⟨.null, rfl⟩
      ⟨_, ab inA⟩)
    (fun _ isSub _ isInBCompl isInA => isInBCompl (isSub isInA))
    (fun _ isSub _ isIn => isSub (SingleLaneExpr.InWfm.of_in_def isIn))
    (fun _ isSub _ isIn => SingleLaneExpr.InWfm.in_def (isSub isIn))
    (fun _ isSub _ isIn => isSub (SingleLaneExpr.InWfm.in_def isIn))
    (fun _ isSub _ isIn => SingleLaneExpr.InWfm.of_in_def (isSub isIn))
    (fun _ _ out ih _ isIn => MutIndDescriptor.isSound _ ih out isIn)
    (fun _ _ out ih _ isIn => MutCoindDescriptor.isSound _ ih out isIn)


def PairDl.Subset.toUniv
  (sub: Subset dl a b)
:
  dl.Univ (un (.compl a) b)
:=
  fun p =>
    if h: a.intp [] dl.wfm p
    then inUnR (sub h)
    else inUnL h

def PairDl.Univ.toSubset
  {a b: SingleLanePairExpr}
  (univ: Univ dl (un (.compl a) b))
:
  Subset dl a b
:=
  fun p inA =>
    (univ p).elim
      (fun inComplA => (inComplA inA).elim)
      id


def PairDl.UnivStx.isSound
  (univ: UnivStx dl expr)
:
  dl.Univ expr
:=
  univ.rec
    (motive := fun expr _ => dl.Univ expr)
    (fun expr p =>
      if h: expr.intp [] dl.wfm p
      then Or.inr h
      else Or.inl h)
    (fun
      | _, _, _, _, .null => inUnL inNull
      | _, _, univL, univR, .pair a b => inUnR (inPair (univL a) (univR b)))
    (fun _ univL p => inUnL (univL p))
    (fun _ univ p => (univ p).symm)
    (fun _ _ univL univR p => inIr (univL p) (univR p))
    (fun _ univ p => (univ p).symm)
    (fun mutDesc _ i premises p =>
      let isSubset := mutDesc.isSound (fun i => (premises i).toSubset) i
      isSubset.toUniv p)

open PairDl.UnivStx in
noncomputable def PairDl.SubsetStx.toUniv
  (sub: SubsetStx dl a b)
:
  UnivStx dl (un (.compl a) b)
:=
  sub.rec
    (motive := fun a b _ => UnivStx dl (un (.compl a) b))
    (@fun
      | x, .defLane => excludedMiddle (.var .defLane x)
      | x, .posLane =>
        let em := excludedMiddle (dl := dl) (.var .posLane x)
        show dl.UnivStx (un (Expr.compl (.var .defLane x)) (.var .posLane x)) from
        sorry)
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
