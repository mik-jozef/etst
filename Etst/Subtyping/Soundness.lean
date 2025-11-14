import Etst.Subtyping.Utils.FixpointMethodsSoundness
import Etst.Subtyping.UnivStx

namespace Etst
open Expr


def DefList.SubsetStx.isSound
  (sub: SubsetStx dl ctx a b)
:
  dl.Subset a b
:=
  -- Using match expressions resulted in "failed to show termination".
  -- That was before the removal of signatures, maybe now it would work :shrug:
  sub.rec
    (motive := fun _ctx a b _ => dl.Subset a b)
    (@fun
      | _, .defLane, _, _, isIn => isIn
      | _, .posLane, _, _, isIn => isIn.toPos)
    id
    id
    id
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
    (fun _ => ⟨.null, rfl⟩)
    (fun _ _ isSubL isSubR _ _ =>
      let ⟨l, inL⟩ := isSubL ⟨.null, rfl⟩
      let ⟨r, inR⟩ := isSubR ⟨.null, rfl⟩
      ⟨_, l, r, rfl, inL, inR⟩)
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


def DefList.Subset.toUniv
  (sub: Subset dl a b)
:
  dl.Univ (un (.compl a) b)
:=
  fun p =>
    if h: a.intp [] dl.wfm p
    then inUnR (sub h)
    else inUnL h

def DefList.Univ.toSubset
  {a b: SingleLaneExpr}
  (univ: Univ dl (un (.compl a) b))
:
  Subset dl a b
:=
  fun p inA =>
    (univ p).elim
      (fun inComplA => (inComplA inA).elim)
      id


def DefList.UnivStx.isSound
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

open DefList.UnivStx in
noncomputable def DefList.SubsetStx.toUniv
  (sub: SubsetStx dl ctx a b)
:
  UnivStx dl (un (.compl a) b)
:=
  sub.rec
    (motive := fun _ a b _ => UnivStx dl (un (.compl a) b))
    (@fun
      | x, .defLane => excludedMiddle (.var .defLane x)
      | x, .posLane =>
        let em := excludedMiddle (dl := dl) (.var .posLane x)
        show dl.UnivStx (un (.compl (.var .defLane x)) (.var .posLane x)) from
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
