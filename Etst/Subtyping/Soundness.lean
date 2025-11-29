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
    (motive := fun a b _ => ∀ bv, dl.SubsetBv bv a b)
    (fun _ _ => id)
    (fun _ _ => Set3.defMem.toPos)
    (fun
    | _, _, isSubL, isSubR, bv, .pair _ _, isIn =>
      let ⟨inwL, inwR⟩ := inPairElim isIn
      inPair (isSubL bv inwL) (isSubR bv inwR))
    (fun _ _ => inUnL)
    (fun _ _ => inUnR)
    (fun _ _ isSubAc isSubBc bv _ isIn =>
      isIn.elim (fun i => isSubAc bv i) (fun i => isSubBc bv i))
    (fun _ _ => inIrElimL)
    (fun _ _ => inIrElimR)
    (fun _ _ isSubA isSubB bv _ isIn => inIr (isSubA bv isIn) (isSubB bv isIn))
    (fun _ _ isSubA isSubB bv _ isIn =>
      (isSubA bv isIn).elim
        (fun inAl => inUnL (inIr inAl (isSubB bv isIn)))
        (fun inAr => inUnR (inIr inAr (isSubB bv isIn))))
    (fun _ _ _ => ⟨.null, rfl⟩)
    (fun _ _ isSubL isSubR bv _ _ =>
      let ⟨l, inL⟩ := isSubL bv ⟨.null, rfl⟩
      let ⟨r, inR⟩ := isSubR bv ⟨.null, rfl⟩
      ⟨_, l, r, rfl, inL, inR⟩)
    (fun _ _ ab a bv _ _ =>
      let ⟨_, inA⟩ := a bv ⟨.null, rfl⟩
      ⟨_, ab bv inA⟩)
    (fun _ _ isSubA isSubB bv _ _ =>
      let ⟨_, inA⟩ := isSubA bv ⟨.null, rfl⟩
      let ⟨_, inCondB⟩ := isSubB bv inA
      ⟨_, inCondB⟩)
    (fun _ sub bv _ _ p => sub bv ⟨p, rfl⟩)
    (fun _ sub bv _ isIn => sub bv isIn _)
    (fun _ _ subSome subFull bv _ isInAny p =>
      let ⟨_, inA⟩ := subSome bv isInAny
      subFull bv inA p)
    (fun _ _ => SingleLaneExpr.InWfm.in_def)
    (fun _ _ => SingleLaneExpr.InWfm.of_in_def)
    (fun _ _ ab bc bv _ isIn => bc bv (ab bv isIn))
    (fun _ _ _ => Classical.em _)
    nofun
    (fun _ _ out ih bv _ isIn => MutIndDescriptor.isSound _ ih out bv isIn)
