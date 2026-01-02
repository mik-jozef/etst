import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.Subtyping.Utils.ExprLiftBvars
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

import Etst.Subtyping.SubsetStx

namespace Etst
open Expr


namespace DefList
  inductive IsFullStx (dl: DefList): SingleLaneExpr → Type
  | defPos: dl.IsFullStx (impl (var .defLane x) (var .posLane x))
    -- TODO should be probable using induction.
  | unfold (lane: Set3.Lane) (x: Nat):
      dl.IsFullStx (impl (var lane x) ((dl.getDef x).toLane lane))
  | fold (lane: Set3.Lane) (x: Nat):
      dl.IsFullStx (impl ((dl.getDef x).toLane lane) (var lane x))
  | mp
      (impl: dl.IsFullStx (impl a b))
      (arg: dl.IsFullStx a)
    :
      dl.IsFullStx b
  | simpl: dl.IsFullStx (impl a (impl b a))
  | distImpl:
      dl.IsFullStx
        (impl
          (impl a (impl b c))
          (impl (impl a b) (impl a c)))
  | contra: dl.IsFullStx (impl (impl a.compl b.compl) (impl b a))
  | fPair:
      dl.IsFullStx
        (impl
          (condFull left)
          (impl
            (condFull rite)
            (un null (pair left rite))))
  | fPairMono:
      dl.IsFullStx
        (impl
          (condFull (impl al bl))
          (impl
            (condFull (impl ar br))
            (impl (pair al ar) (pair bl br))))
  | fPairEmptyL:
      dl.IsFullStx (impl (condFull (compl left)) (compl (pair left rite)))
  | fPairEmptyR:
      dl.IsFullStx (impl (condFull (compl rite)) (compl (pair left rite)))
  | fIr: dl.IsFullStx (impl a (impl b (ir a b)))
  | fIrL: dl.IsFullStx (impl (ir l r) l)
  | fIrR: dl.IsFullStx (impl (ir l r) r)
  | fFull
      (full: dl.IsFullStx expr)
    :
      dl.IsFullStx (expr.condFull)
  | fFullElim
      (full: dl.IsFullStx (expr.condFull))
    :
      dl.IsFullStx expr
  
  namespace IsFullStx
    variable {dl: DefList}
    
    def mp2
      (abc: dl.IsFullStx (impl a (impl b c)))
      (a: dl.IsFullStx a)
      (b: dl.IsFullStx b)
    :
      dl.IsFullStx c
    :=
      mp (mp abc a) b
    
    def implSelf: dl.IsFullStx (impl a a) :=
      mp2 distImpl simpl (simpl (b := a))
    
    -- The deduction theorem for IsFullStx. If assuming `hyp`
    -- we can prove `expr` then we can prove `hyp -> expr`.
    inductive IsFullStxFrom (dl: DefList) (hyp: SingleLaneExpr): SingleLaneExpr → Type
    | fromHyp: IsFullStxFrom dl hyp hyp
    | fromFull (full: dl.IsFullStx expr): IsFullStxFrom dl hyp expr
    | mp (impl: IsFullStxFrom dl hyp (impl a b)) (arg: IsFullStxFrom dl hyp a): IsFullStxFrom dl hyp b

    def IsFullStxFrom.toImpl
      (fn: IsFullStxFrom dl a b)
    :
      dl.IsFullStx (impl a b)
    :=
      match fn with
      | .fromHyp => implSelf
      | .fromFull full => simpl.mp full
      | .mp f_impl f_arg =>
          let ih_impl := toImpl f_impl
          let ih_arg := toImpl f_arg
          mp2 distImpl ih_impl ih_arg
    
    def liftImpl:
      dl.IsFullStx
        (impl
          (impl a b)
          (impl (impl c a) (impl c b)))
    :=
      mp2 distImpl (mp simpl distImpl) simpl
    
    def exchange:
      dl.IsFullStx (impl (impl a (impl b c)) (impl b (impl a c)))
    :=
      let T1 := mp (mp liftImpl simpl) distImpl
      let T2 := mp (mp liftImpl distImpl) T1
      mp2 distImpl T2 (mp simpl simpl)
    
    def trans:
      dl.IsFullStx (impl (impl a b) (impl (impl b c) (impl a c)))
    :=
      mp exchange liftImpl
    
    def subPe: dl.IsFullStx (impl (ir a a.compl) b) :=
      mp2 distImpl (trans.mp2 (trans.mp2 fIrR simpl) contra) fIrL
    
    def curry:
      dl.IsFullStx (impl (impl (ir a b) c) (impl a (impl b c)))
    :=
      mp2 trans liftImpl (mp trans fIr)
    
    def uncurry:
      dl.IsFullStx (impl (impl a (impl b c)) (impl (ir a b) c))
    :=
      let proof: IsFullStxFrom dl (impl a (impl b c)) (impl (ir a b) c) :=
        let step0 := .fromFull fIrL
        let step1 := .mp (.mp (.fromFull trans) step0) .fromHyp
        .mp (.mp (.fromFull distImpl) step1) (.fromFull fIrR)
      
      proof.toImpl
    
    def byContra:
      dl.IsFullStx
        (impl
          (impl (compl c) (compl b))
          (impl (impl (compl c) b) c))
    :=
      let conj := ir (impl (compl c) (compl b)) (impl (compl c) b)
      
      let proof: IsFullStxFrom dl conj c :=
        let h1 := .mp (.fromFull fIrL) .fromHyp
        let h2 := .mp (.fromFull fIrR) .fromHyp
        
        -- nc -> (b & nb)
        let step1 := .fromFull (mp liftImpl fIr)
        let step2 := .mp step1 h2
        let step3 := .fromFull distImpl
        let step4 := .mp step3 step2
        let step5 := .mp step4 h1
        
        -- nc -> ~T
        let t := impl c c
        let subPe' := subPe (a := b) (b := compl t)
        let step6 := .fromFull (mp liftImpl subPe')
        let step7 := .mp step6 step5
        
        -- T -> c
        let step8 := .fromFull contra
        let step9 := .mp step8 step7
        
        -- c
        let step10 := .fromFull implSelf
        .mp step9 step10
      
      mp curry proof.toImpl
    
    def dne: dl.IsFullStx (impl (compl (compl a)) a) :=
      let lifted := mp2 trans (mp liftImpl byContra) distImpl
      mp2 lifted simpl (mp simpl implSelf)
    
    def dni: dl.IsFullStx (impl a (compl (compl a))) :=
      mp contra dne
    
    def mt: dl.IsFullStx (impl (impl a b) (impl b.compl a.compl)) :=
      let step := mp2 trans (mp trans dne) (mp exchange byContra)
      mp exchange (mp (mp trans simpl) (mp exchange step))
    
    
    def fUnL: dl.IsFullStx (impl a (un a b)) :=
      mp contra (mp2 trans dne fIrL)
    
    def fUnR: dl.IsFullStx (impl b (un a b)) :=
      mp contra (mp2 trans dne fIrR)
    
    def fUn:
      dl.IsFullStx (impl (impl a c) (impl (impl b c) (impl (un a b) c)))
    :=
      let step0 := mp liftImpl fIr
      let step1 := mp2 trans (step0) distImpl
      let step2 := mp2 trans mt step1
      let step3 := mp exchange step2
      let step4 := mp2 trans mt step3
      let step5 := mp exchange step4
      let step6 := mp liftImpl dni
      let step7 := mp2 liftImpl trans step5
      let step8 := mp exchange step7
      let step9 := mp step8 step6
      let step10 := mp2 liftImpl trans step9
      let step11 := mp exchange step10
      mp step11 contra
    
    def em: dl.IsFullStx (impl a a) :=
      (distImpl.mp fUnR).mp (fUnR (a := a))
    
    def unComm: dl.IsFullStx (impl (un a b) (un b a)) :=
      fUn.mp2 fUnR fUnL
    
    def distrib:
      dl.IsFullStx (impl (un al ar) (impl b (un (ir al b) (ir ar b))))
    :=
      let left := mp2 trans fIr (mp liftImpl fUnL)
      let rite := mp2 trans fIr (mp liftImpl fUnR)
      mp2 fUn left rite
    
  end IsFullStx
  
  def SubsetStx.toIsFullStx:
    SubsetStx dl n a b →
    dl.IsFullStx (un a.compl b)
  | subId => .em
  | subDefPos => .defPos
  | subPair subL subR =>
    .mp2
      .fPairMono
      (.fFull subL.toIsFullStx)
      (.fFull subR.toIsFullStx)
  | subIrL => .fIrL
  | subIrR => .fIrR
  | subIr ac bc =>
      .mp2 .distImpl (.mp2 .trans ac.toIsFullStx .fIr) bc.toIsFullStx
  | irUnDistL => .mp .uncurry .distrib
  | subCompl sub => .mp .mt sub.toIsFullStx
  | dne => .dne
  | dni => .dni
  | isFull _ => sorry
  | fullImplElim => sorry
  | fullElim => sorry
  | someStripFull => sorry
  | unfold => .unfold _ _
  | fold => .fold _ _
  | trans ab bc => .mp2 .trans ab.toIsFullStx bc.toIsFullStx
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
    (full: dl.IsFullStx expr)
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
    | .simpl =>
        inImpl fun inA =>
        inImpl fun _ => inA
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
    | .fIr =>
        inImpl fun inA =>
        inImpl fun inB =>
        inIr inA inB
    | .fIrL => inImpl inIrElimL
    | .fIrR => inImpl inIrElimR
    | .fFull full => fun p => full.isSound bv p bound
    | .fFullElim fullCond =>
        let inCond := fullCond.isSound bv p bound
        inCondFullElim inCond p
  
end DefList
