import Etst.Subtyping.Soundness

namespace Etst
open Expr


namespace DefList
  inductive IsFullStx (dl: DefList): SingleLaneExpr → Type
  | defPos: dl.IsFullStx (impl (const .defLane x) (const .posLane x))
    -- TODO should be provable using induction.
  | unfold (lane: Set3.Lane) (x: Nat):
      dl.IsFullStx (impl (const lane x) ((dl.getDef x).toLane lane))
  | fold (lane: Set3.Lane) (x: Nat):
      dl.IsFullStx (impl ((dl.getDef x).toLane lane) (const lane x))
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
  | fPairMono:
      dl.IsFullStx
        (impl
          (condFull (impl al bl))
          (impl
            (condFull (impl ar br))
            (impl (pair al ar) (pair bl br))))
  -- TODO is this one necessary?
  | fPairUnDistL:
      dl.IsFullStx
        (impl
          (pair (un a b) c)
          (un (pair a c) (pair b c)))
  -- TODO is this one necessary?
  | fPairUnDistR:
      dl.IsFullStx
        (impl
          (pair a (un b c))
          (un (pair a b) (pair a c)))
  -- TODO is this one necessary?
  | fPairIrDistL:
      dl.IsFullStx
        (impl
          (ir (pair a c) (pair b c))
          (pair (ir a b) c))
  -- TODO is this one necessary?
  | fPairIrDistR:
      dl.IsFullStx
        (impl
          (ir (pair a b) (pair a c))
          (pair a (ir b c)))
  -- TODO is this one necessary?
  | fPairNoneL:
      dl.IsFullStx (impl (pair .none a) x)
  -- TODO is this one necessary?
  | fPairNoneR:
      dl.IsFullStx (impl (pair a .none) x)
  | fPairNullDisjoint:
      dl.IsFullStx (impl (ir .null (pair a b)) x)
  | fNullPair: dl.IsFullStx (un null (pair any any))
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
  | fSomeStripFull {a}:
      dl.IsFullStx (impl (condSome (condFull a)) (condFull a))
  | mutInduction {x}
      (desc: MutIndDescriptor dl)
      (premises:
        (i: desc.Index) →
        dl.IsFullStx
          (impl
            x
            (condFull
              (impl
                (desc.hypothesify 0 (desc[i].expansion.toLane desc[i].lane))
                desc[i].expr))))
      (i: desc.Index)
    :
      dl.IsFullStx
        (impl x (condFull (impl (const desc[i].lane desc[i].x) desc[i].expr)))
  
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
    
    def mp3
      (abcd: dl.IsFullStx (impl a (impl b (impl c d))))
      (a: dl.IsFullStx a)
      (b: dl.IsFullStx b)
      (c: dl.IsFullStx c)
    :
      dl.IsFullStx d
    :=
      mp (mp (mp abcd a) b) c
    
    
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
    
    def unMonoR:
      dl.IsFullStx (impl (impl a b) (impl (un c a) (un c b)))
    :=
      let left := mp2 trans fUnL simpl
      let rite :=
        mp2 trans
          (mp exchange implSelf)
          (mp liftImpl fUnR)
      mp exchange (mp2 fUn left rite)
    
    def complSwapA
      (sub: dl.IsFullStx (impl (compl a) b))
    :
      dl.IsFullStx (impl (compl b) a)
    :=
      mp2 trans (mt.mp sub) dne
    
    def someAddFull:
      dl.IsFullStx (impl (condSome a) (condFull (condSome a)))
    :=
      complSwapA (fSomeStripFull (a := compl a))
    
    def fullFull: dl.IsFullStx (impl (condFull a) (condFull (condFull a))) :=
      let step1 := mt.mp (fFullElim (expr := compl (condFull a)))
      let step2 := trans.mp2 dni step1
      let step3 := someAddFull (a := condFull a)
      let step4 := fFull (full := fSomeStripFull (a := a))
      let step5 := mp fFullImplElim step4
      mp2 trans step2 (mp2 trans step3 step5)
    
    def fPairMonoFull:
      dl.IsFullStx
        (impl
          (condFull (impl al bl))
          (impl
            (condFull (impl ar br))
            (condFull (impl (pair al ar) (pair bl br)))))
    :=
      let A := condFull (impl al bl)
      let B := condFull (impl ar br)
      let C := impl (pair al ar) (pair bl br)
      let proof: IsFullStxFrom dl (ir A B) (condFull C) :=
        let hA := .mp (.fromFull fIrL) .fromHyp
        let hB := .mp (.fromFull fIrR) .fromHyp
        let hAA := .mp (.fromFull fullFull) hA
        let hBB := .mp (.fromFull fullFull) hB
        let step1 := .fromFull (fFull fPairMono)
        let step2 := .mp (.fromFull fFullImplElim) step1
        let step3 := .mp step2 hAA
        let step4 := .mp (.fromFull fFullImplElim) step3
        .mp step4 hBB
      mp curry proof.toImpl
    
    -- TODO: `fAny` to be proven once IsFullStx has rules for quantifiers.
    def fAny: dl.IsFullStx any := sorry
    
    
    def fullSimpl:
      dl.IsFullStx (impl (condFull a) (condFull (impl b a)))
    :=
      mp fFullImplElim (fFull simpl)
    
    def fPairOfFull:
      dl.IsFullStx
        (impl
          (condFull left)
          (impl
            (condFull rite)
            (un null (pair left rite))))
    :=
      let step1 := mp2 trans fullSimpl fPairMono
      let step2 := mp exchange step1
      let step3 := mp2 trans fullSimpl step2
      let impl_A_C_E_F := mp exchange step3
      
      let impl_A_C_G_H := mp2 liftImpl (mp liftImpl unMonoR) impl_A_C_E_F
      let impl_A_G_C_H := mp2 liftImpl exchange impl_A_C_G_H
      let impl_G_A_C_H := mp exchange impl_A_G_C_H
      
      mp impl_G_A_C_H fNullPair
    
    def implToImplFull {x}
      (h: dl.IsFullStx (impl a b))
    :
      dl.IsFullStx (impl x (condFull (impl a b)))
    :=
      mp simpl (fFull h)
    
    def mutInductionDirect
      (desc: MutIndDescriptor dl)
      (premises:
        (i: desc.Index) →
        IsFullStx dl (impl (desc.hypothesify 0 (desc[i].expansion.toLane desc[i].lane)) desc[i].expr))
      (i: desc.Index)
    :
      IsFullStx dl (impl (const desc[i].lane desc[i].x) desc[i].expr)
    :=
      let premises' (j: desc.Index) := implToImplFull (x := Expr.any) (premises j)
      let res := mutInduction (x := Expr.any) desc premises' i
      mp fFullElim (mp res fAny)
    
  end IsFullStx
  
  def SubsetStx.toIsFullStx:
    SubsetStx dl a b →
    dl.IsFullStx (un a.compl b)
  | subDefPos => .defPos
  | pairMono (al := al) (ar := ar) (bl := bl) (br := br) subL subR =>
    let proof: IsFullStx.IsFullStxFrom dl a _ :=
      let hL := .mp (.fromFull subL.toIsFullStx) .fromHyp
      let hR := .mp (.fromFull subR.toIsFullStx) .fromHyp
      .mp (.mp (.fromFull .fPairMonoFull) hL) hR
    proof.toImpl
  | subComplPairUn =>
      sorry
  | subUnComplPair =>
      sorry
  | subPairIrDistL => .fPairIrDistL
  | subPairIrDistR => .fPairIrDistR
  | subIrL => .fIrL
  | subIrR => .fIrR
  | subIr ac bc =>
      .mp2 .distImpl (.mp2 .trans ac.toIsFullStx .fIr) bc.toIsFullStx
  | subIrUnDistL => .mp .uncurry .distrib
  | subCompl sub => .mp .mt sub.toIsFullStx
  | subDne => .dne
  | subDni => .dni
  | isFull anyA => .mp .simpl (.fFull (.mp anyA.toIsFullStx .fAny))
  | fullImplElim => .fFullImplElim
  | fullElim => .fFullElim
  | someStripFull => .fSomeStripFull
  | subUnfold => .unfold _ _
  | subFold => .fold _ _
  | univIntro sub =>
      sorry
  | trans ab bc => .mp2 .trans ab.toIsFullStx bc.toIsFullStx
  | subPe => .subPe
  | mutInduction desc premises i =>
      .mutInduction desc (fun j => (premises j).toIsFullStx) i
  
  def IsFullStx.toSubsetStx
    (full: dl.IsFullStx a)
  :
    SubsetStx dl Expr.any a
  :=
    match full with
    | .defPos => .toImpl .subDefPos
    | .unfold lane x => .toImpl .subUnfold
    | .fold lane x => .toImpl .subFold
    | .mp impl arg => .implElim impl.toSubsetStx arg.toSubsetStx
    | .simpl => .implIntro (.implIntro (.irCtxL .subIrR))
    | .distImpl => .toImpl .implDist
    | .contra => .toImpl .subContraElim
    | .fPairMono =>
      .toImpl
        (.implIntro
          (.trans (.pairMono .subIrL .subIrR) .fullElim))
    | .fPairUnDistL => .toImpl .subPairUnDistL
    | .fPairUnDistR => .toImpl .subPairUnDistR
    | .fPairIrDistL => .toImpl .subPairIrDistL
    | .fPairIrDistR => .toImpl .subPairIrDistR
    | .fPairNoneL => .toImpl .subPairNoneL
    | .fPairNoneR => .toImpl .subPairNoneR
    | .fPairNullDisjoint => .toImpl .subIrNullPair
    | .fNullPair => .nullPair
    | .fIr => .toImpl (.implIntro .subId)
    | .fIrL => .toImpl .subIrL
    | .fIrR => .toImpl .subIrR
    | .fFull full => .isFull full.toSubsetStx
    | .fFullImplElim => .toImpl .fullImplElim
    | .fFullElim => .toImpl .fullElim
    | fSomeStripFull => .toImpl .someStripFull
    | .mutInduction desc premises i =>
        let premises_impl i := .ofImpl (premises i).toSubsetStx
        .toImpl (.mutInduction desc premises_impl i)
  
  
  def IsFull
    (dl: DefList)
    (expr: SingleLaneExpr)
  :
    Prop
  :=
    ∀ bv: List Pair,
    ∀ p: Pair,
      expr.freeVarUB ≤ bv.length →
      expr.intp bv dl.wfm p
  
  
  open SingleLaneExpr in
  def IsFullStx.isSound
    (full: dl.IsFullStx expr)
  :
    IsFull dl expr
  :=
    fun bv _p _bound => full.toSubsetStx.isSound  bv inAny
  
end DefList
