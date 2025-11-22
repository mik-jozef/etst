import Etst.Subtyping.Utils.FixpointMethodsSoundness

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
    (motive := fun a b _ => dl.Subset a b)
    id
    (Set3.defMem.toPos)
    (fun
    | _, _, isSubL, isSubR, .pair _ _, isIn =>
      let ⟨inwL, inwR⟩ := inPairElim isIn
      inPair (isSubL inwL) (isSubR inwR))
    inUnL
    inUnR
    (fun _ _ isSubAc isSubBc _ isIn =>
      isIn.elim (fun i => isSubAc i) (fun i => isSubBc i))
    inIrElimL
    inIrElimR
    (fun _ _ isSubA isSubB _ isIn => inIr (isSubA isIn) (isSubB isIn))
    (fun _ _ isSubA isSubB _ isIn =>
      (isSubA isIn).elim
        (fun inAl => inUnL (inIr inAl (isSubB isIn)))
        (fun inAr => inUnR (inIr inAr (isSubB isIn))))
    (fun _ _ => ⟨.null, rfl⟩)
    (fun _ _ isSubL isSubR _ _ =>
      let ⟨l, inL⟩ := isSubL ⟨.null, rfl⟩
      let ⟨r, inR⟩ := isSubR ⟨.null, rfl⟩
      ⟨_, l, r, rfl, inL, inR⟩)
    (fun _ _ ab a _ _ =>
      let ⟨_, inA⟩ := a ⟨.null, rfl⟩
      ⟨_, ab inA⟩)
    (fun _ _ isSubA isSubB _ _ =>
      let ⟨_, inA⟩ := isSubA ⟨.null, rfl⟩
      let ⟨_, inCondB⟩ := isSubB inA
      ⟨_, inCondB⟩)
    (fun _ sub _ _ p => sub ⟨p, rfl⟩)
    (fun _ sub _ isIn => sub isIn _)
    (fun _ _ subSome subFull _ isInAny p =>
      let ⟨_, inA⟩ := subSome isInAny
      subFull inA p)
    SingleLaneExpr.InWfm.in_def
    SingleLaneExpr.InWfm.of_in_def
    (fun _ _ ab bc _ isIn => bc (ab isIn))
    (fun _ => Classical.em _)
    nofun
    (fun _ _ out ih _ isIn => MutIndDescriptor.isSound _ ih out isIn)
