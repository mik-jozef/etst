import Etst.Subtyping.Soundness

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
  | fFull (full: dl.IsFullStx a): dl.IsFullStx (condFull a)
  -- Axiom K in modal logic.
  | fFullImplElim:
      dl.IsFullStx
        (impl
          (condFull (impl a b))
          (impl (condFull a) (condFull b)))
  -- Axiom T in modal logic.
  | fFullElim:
      dl.IsFullStx (impl (condFull expr) expr)
  -- Contraposition of Axiom 5 (up to removal of negation from `a`)
  | fsomeStripFull:
      dl.IsFullStx (impl (condSome (condFull a)) (condFull a))
  | mutInduction
      (desc: MutIndDescriptor dl)
      (premises:
        (i: desc.Index) →
        IsFullStx dl (impl (desc.hypothesify 0 (desc[i].expansion.toLane .posLane)) desc[i].rite))
      (i: desc.Index)
    :
      IsFullStx dl (impl (var .posLane desc[i].left) desc[i].rite)
  
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
    
    def unComm: dl.IsFullStx (impl (un a b) (un b a)) :=
      fUn.mp2 fUnR fUnL
    
    def distrib:
      dl.IsFullStx (impl (un al ar) (impl b (un (ir al b) (ir ar b))))
    :=
      let left := mp2 trans fIr (mp liftImpl fUnL)
      let rite := mp2 trans fIr (mp liftImpl fUnR)
      mp2 fUn left rite
    
    -- TODO: `fAny` to be proven once IsFullStx has rules for quantifiers.
    def fAny: dl.IsFullStx Expr.any := sorry
    
  end IsFullStx
  
  def SubsetStx.toIsFullStx:
    SubsetStx dl n a b →
    dl.IsFullStx (un a.compl b)
  | subId => .implSelf
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
  | isFull anyA => .mp .simpl (.fFull (.mp anyA.toIsFullStx .fAny))
  | fullImplElim => .fFullImplElim
  | fullElim => .fFullElim
  | someStripFull => .fsomeStripFull
  | unfold => .unfold _ _
  | fold => .fold _ _
  | trans ab bc => .mp2 .trans ab.toIsFullStx bc.toIsFullStx
  | subPe => .subPe
  | mutInduction desc premises i =>
      .mutInduction desc (fun j => (premises j).toIsFullStx) i
  
  def IsFullStx.toSubsetStx
    (full: dl.IsFullStx a)
  :
    SubsetStx dl ctx Expr.any a
  :=
    match full with
    | .defPos => .toImpl .subDefPos
    | .unfold lane x => .toImpl .unfold
    | .fold lane x => .toImpl .fold
    | .mp impl arg => .implElim impl.toSubsetStx arg.toSubsetStx
    | .simpl => .implIntro (.implIntro (.irL .subIrR))
    | .distImpl => .toImpl .implDist
    | .contra => .toImpl .contraImpl
    | .fPair => sorry
    | .fPairMono => sorry
    | .fPairEmptyL => sorry
    | .fPairEmptyR => sorry
    | .fIr => .toImpl (.implIntro .subId)
    | .fIrL => .toImpl .subIrL
    | .fIrR => .toImpl .subIrR
    | .fFull full => .isFull full.toSubsetStx
    | .fFullImplElim => .toImpl .fullImplElim
    | .fFullElim => .toImpl .fullElim
    | .fsomeStripFull => .toImpl .someStripFull
    | .mutInduction desc premises i =>
        .toImpl
          (.mutInduction
            desc
            (fun i => .ofImpl (premises i).toSubsetStx)
            i)
  
  
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
    fun bv _p _bound => full.toSubsetStx.isSound (ctx := []) bv inAny
  
end DefList
