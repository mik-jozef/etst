import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.Subtyping.Utils.ExprLiftBvars
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

import Etst.Subtyping.SubsetStx

namespace Etst
open Expr


namespace DefList
  inductive IsFullStx (dl: DefList): SingleLaneExpr → Type
  | defPos: IsFullStx dl (impl (var .defLane x) (var .posLane x))
  | unfold (lane: Set3.Lane) (x: Nat):
      IsFullStx dl (impl (var lane x) ((dl.getDef x).toLane lane))
  | fold (lane: Set3.Lane) (x: Nat):
      IsFullStx dl (impl ((dl.getDef x).toLane lane) (var lane x))
  | mp
      (impl: IsFullStx dl (impl a b))
      (arg: IsFullStx dl a)
    :
      IsFullStx dl b
  | distImpl:
      IsFullStx dl
        (impl
          (impl a (impl b c))
          (impl (impl a b) (impl a c)))
  | contra: IsFullStx dl (impl (impl a.compl b.compl) (impl b a))
  | fPair:
      IsFullStx
        dl
        (impl
          (condFull left)
          (impl
            (condFull rite)
            (un null (pair left rite))))
  | fPairMono:
      IsFullStx
        dl
        (impl
          (condFull (impl al bl))
          (impl
            (condFull (impl ar br))
            (impl (pair al ar) (pair bl br))))
  | fPairEmptyL:
      IsFullStx dl (impl (condFull (compl left)) (compl (pair left rite)))
  | fPairEmptyR:
      IsFullStx dl (impl (condFull (compl rite)) (compl (pair left rite)))
  | fUnL: IsFullStx dl (impl a (un a b))
  | fUnR: IsFullStx dl (impl b (un a b))
  | fUn:
      IsFullStx dl (impl (impl a c) (impl (impl b c) (impl (un a b) c)))
  | fIr: IsFullStx dl (impl a (impl b (ir a b)))
  | fIrL: IsFullStx dl (impl (ir l r) l)
  | fIrR: IsFullStx dl (impl (ir l r) r)
  | fFull
      (full: IsFullStx dl expr)
    :
      IsFullStx dl (expr.condFull)
  
  namespace IsFullStx
    def fUnImpl
      (fullL: IsFullStx dl (impl l b))
      (fullR: IsFullStx dl (impl r b))
    :
      IsFullStx dl (impl (un l r) b)
    :=
      (fUn.mp fullL).mp fullR
    
    def em: IsFullStx dl (impl a a) :=
      (distImpl.mp fUnR).mp (fUnR (a := a))
    
    def trans
      (ab: IsFullStx dl (impl a b))
      (bc: IsFullStx dl (impl b c))
    :
      IsFullStx dl (impl a c)
    :=
      mp (mp distImpl (mp fUnR bc)) ab
    
    def unImplTest
      (fullUn: IsFullStx dl (un a0 b0))
      (fullImpA: IsFullStx dl (impl a0 a1))
      (fullImpB: IsFullStx dl (impl b0 b1))
    :
      IsFullStx dl (un a1 b1)
    :=
      let impA := trans fullImpA fUnL
      let impB := trans fullImpB fUnR
      mp (fUnImpl impA impB) fullUn
    
    def unComm: IsFullStx dl (impl (un a b) (un b a)) :=
      fUnImpl fUnR fUnL
    
    def subPe: IsFullStx dl (impl (ir a a.compl) b) :=
      (distImpl.mp (trans (trans fIrR fUnR) contra)).mp fIrL
    
    def lift
      (f: IsFullStx dl (impl y z))
    :
      IsFullStx dl (impl (impl x y) (impl x z))
    :=
      mp distImpl (mp fUnR f)
    
    def distrib:
      IsFullStx dl (impl (un al ar) (impl b (un (ir al b) (ir ar b))))
    :=
      let left_branch := trans fIr (lift fUnL)
      let right_branch := trans fIr (lift fUnR)
      fUnImpl left_branch right_branch
    
  end IsFullStx
  
  def SubsetStx.toIsFullStx:
    SubsetStx dl n a b →
    IsFullStx dl (un a.compl b)
  | subId => .em
  | subDefPos => .defPos
  | subPair (al:=al) (ar:=ar) (bl:=bl) (br:=br) subL subR =>
    let ihL: dl.IsFullStx (impl al bl) := subL.toIsFullStx
    let ihR: dl.IsFullStx (impl ar br) := subR.toIsFullStx
    .mp (.mp .fPairMono (.fFull ihL)) (.fFull ihR)
  | subIrL => .fIrL
  | subIrR => .fIrR
  | subIr ac bc =>
      let ac' := ac.toIsFullStx
      let bc' := bc.toIsFullStx
      .mp (.mp .distImpl (ac'.trans .fIr)) bc'
  | irUnDistL => sorry
  | subCompl sub => sorry
  | dne => sorry
  | dni => sorry
  | isFull _ => sorry
  | fullImplElim => sorry
  | fullElim => sorry
  | someStripFull => sorry
  | unfold => .unfold _ _
  | fold => .fold _ _
  | trans ab bc => ab.toIsFullStx.trans bc.toIsFullStx
  | subPe => .subPe
  | mutInduction _ _ _ => sorry
  
  
  def IsFull
    (dl: DefList)
    (expr: SingleLaneExpr)
  :
    Prop
  :=
    ∀ bv: List Pair,
    ∀ p: Pair,
      expr.looseBvarUB ≤ bv.length →
      expr.intp bv dl.wfm p
  
  
  open SingleLaneExpr in
  def IsFullStx.isSound
    (full: IsFullStx dl expr)
  :
    IsFull dl expr
  :=
    fun bv p bound =>
    match full with
    | .defPos (x:=x) =>
        if h: (dl.wfm x).defMem p then
          inUnR h.toPos
        else
          inUnL h
    | .unfold (lane:=lane) (x:=x) =>
        inImpl fun inVar =>
          let inDefNoBv := InWfm.in_def_no_bv inVar
          let isClean := dl.isClean x
          let isCleanLane: ((dl.getDef x).toLane lane).IsClean := by
            unfold Expr.IsClean at isClean ⊢
            rw [BasicExpr.clearBvars_lane_comm]
            rw [←isClean]
          IsClean.changeBv isCleanLane inDefNoBv
    | .fold (lane:=lane) (x:=x) =>
        inImpl fun inDef =>
          let isClean := dl.isClean x
          let isCleanLane: ((dl.getDef x).toLane lane).IsClean := by
            unfold Expr.IsClean at isClean ⊢
            rw [BasicExpr.clearBvars_lane_comm]
            rw [←isClean]
          let inDefNoBv := IsClean.changeBv (bv1:=[]) isCleanLane inDef
          let inVarNoBv := InWfm.of_in_def_no_bv inDefNoBv
          inVarNoBv
    | .mp (a:=a) (b:=b) ab arg =>
        let max_bound := max a.looseBvarUB b.looseBvarUB
        let diff := max_bound - bv.length
        let bv' := bv ++ List.replicate diff Pair.null
        let bound_a: a.looseBvarUB ≤ bv'.length := by
          rw [List.length_append, List.length_replicate]
          apply Nat.le_trans (Nat.le_max_left _ _)
          rw [Nat.add_comm, Nat.sub_add_eq_max]
          apply Nat.le_max_left
        let bound_b: b.looseBvarUB ≤ bv'.length := by
          rw [List.length_append, List.length_replicate]
          apply Nat.le_trans (Nat.le_max_right _ _)
          rw [Nat.add_comm, Nat.sub_add_eq_max]
          apply Nat.le_max_left
        let bound_ab: (Expr.impl a b).looseBvarUB ≤ bv'.length := by
          apply Nat.max_le.mpr
          constructor
          . exact bound_a
          . exact bound_b
        
        let inAb := ab.isSound bv' p bound_ab
        let inA := arg.isSound bv' p bound_a
        
        let inB := (inUnElim inAb).elim
          (fun inComplA => (inComplElim inComplA inA).elim)
          (fun inB => inB)
          
        (intp_append dl bound (List.replicate diff Pair.null) p).mpr inB
    | .distImpl =>
        inImpl fun inAbc =>
        inImpl fun inAb =>
        inImpl fun inA =>
        inImplElim
          (inImplElim inAbc inA)
          (inImplElim inAb inA)
    | .contra =>
        inImpl fun inAbCompl =>
        inImpl fun inB =>
        (inImplElim inAbCompl).mtr inB
    | .fPair =>
        inImpl fun inFullL =>
        inImpl fun inFullR =>
        match p with
        | .null => inUnL inNull
        | .pair l r =>
            let inL := inCondFullElim inFullL l
            let inR := inCondFullElim inFullR r
            inUnR (inPair inL inR)
    | .fPairMono =>
        inImpl fun inAlBl =>
        inImpl fun inArBr =>
        inImpl fun inPairAlAr =>
          let ⟨l, r, ⟨eq, inAl, inAr⟩⟩ := inPairElimEx inPairAlAr
          let inBl := inImplElim (inCondFullElim inAlBl l) inAl
          let inBr := inImplElim (inCondFullElim inArBr r) inAr
          eq ▸ inPair inBl inBr
    | .fPairEmptyL =>
        inImpl fun inComplPair =>
        inCompl fun inPair =>
          let ⟨l, _, ⟨_, inL, _⟩⟩ := inPairElimEx inPair
          inComplElim (inCondFullElim inComplPair l) inL
    | .fPairEmptyR =>
        inImpl fun inComplPair =>
        inCompl fun inPair =>
          let ⟨_, r, ⟨_, _, inR⟩⟩ := inPairElimEx inPair
          inComplElim (inCondFullElim inComplPair r) inR
    | .fUnL => inImpl inUnL
    | .fUnR => inImpl inUnR
    | .fUn =>
        inImpl fun implAc =>
        inImpl fun implBc =>
        inImpl fun unAb =>
          (inUnElim unAb).elim (inImplElim implAc) (inImplElim implBc)
    | .fIr =>
        inImpl fun inA =>
        inImpl fun inB =>
        inIr inA inB
    | .fIrL => inImpl inIrElimL
    | .fIrR => inImpl inIrElimR
    | .fFull full => fun p => full.isSound bv p bound
  
end DefList
