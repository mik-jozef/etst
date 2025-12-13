import Etst.Subtyping.Utils.ExprExpandsInto
import Etst.Subtyping.Utils.ExprLiftBvars
import Etst.WFC.Ch5_S1_AProofSystem
import Etst.WFC.Utils.InterpretationMono

import Etst.Subtyping.SubsetStx

namespace Etst
open Expr


namespace DefList
  mutual
  /-
    Semantically,
        arbIr (condFull expr) = condFull (arbIr expr)
    but
        arbIr (condSome expr) ≠ condSome (arbIr expr) \,.
    
    That's why, unlike IsFullStx, IsSomeStx needs a Nat parameter
    to indicate the number of bvars defined inside the condSome
    expression.
    
    TODO check if the nat parameter is used properly.
  -/
  inductive IsSomeStx (dl: DefList): Nat → SingleLaneExpr → Type
  | bvar
      (le: n ≤ x)
    :
      IsSomeStx dl n (bvar x)
  | null: IsSomeStx dl n null
  | pair
      (someL: IsSomeStx dl n left)
      (someR: IsSomeStx dl n rite)
    :
      IsSomeStx dl n (pair left rite)
  | full
      (full: IsFullStx dl expr)
    :
      IsSomeStx dl n (expr.condFull)
  
  inductive IsFullStx (dl: DefList): SingleLaneExpr → Type
  | defPos: IsFullStx dl (impl (var .defLane x) (var .posLane x))
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
  | fPair
      (fullL: IsFullStx dl left)
      (fullR: IsFullStx dl rite)
    :
      IsFullStx dl (un null (pair left rite))
  | fUnL: IsFullStx dl (impl a (un a b))
  | fUnR: IsFullStx dl (impl b (un a b))
  | fUn:
      IsFullStx dl (impl (impl a c) (impl (impl b c) (impl (un a b) c)))
  | fIr: IsFullStx dl (impl a (impl b (ir a b)))
  | fIrL: IsFullStx dl (impl (ir l r) l)
  | fIrR: IsFullStx dl (impl (ir l r) r)
  | some
      (some: IsSomeStx dl 0 expr)
    :
      IsFullStx dl (expr.condSome)
  end
  
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
  | subPair subL subR =>
    let ihL := subL.toIsFullStx
    let ihR := subR.toIsFullStx
    let lk := IsFullStx.fPair ihL ihR
    sorry
  | subUnL => .fUnL
  | subUnR => .fUnR
  | subUn l r => .fUnImpl l.toIsFullStx r.toIsFullStx
  | subIrL => .fIrL
  | subIrR => .fIrR
  | subIr ac bc =>
      let ac' := ac.toIsFullStx
      let bc' := bc.toIsFullStx
      .mp (.mp .distImpl (ac'.trans .fIr)) bc'
  | unIr subA subB =>
      let subA' := subA.toIsFullStx
      let subB' := subB.toIsFullStx
      .mp (.mp .distImpl (subA'.trans .distrib)) subB'
  | condSomeNull => sorry
  | condSomePair _ _ => sorry
  | condSomeSubTrans _ _ => sorry
  | condSomeUpgrade _ _ => sorry
  | condFull _ => sorry
  | condFullElim _ => sorry
  | condFullUpgrade _ _ => sorry
  | subUnfold => sorry
  | subFold => sorry
  | trans ab bc => ab.toIsFullStx.trans bc.toIsFullStx
  | em =>  .mp .fUnR (.mp .unComm .em)
  | subPe => .subPe
  | mutInduction _ _ _ => sorry
  
  
  def IsSome
    (dl: DefList)
    (n: Nat)
    (expr: SingleLaneExpr)
  :
    Prop
  :=
    ∀ bvc: List Pair,
    ∃ p: Pair,
    ∀ bv: List.Vector Pair n,
      -- guarantees no loose bvars.
      expr.looseBvarUB ≤ n + bvc.length →
      expr.intp (bv.val ++ bvc) dl.wfm p
  
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
  
  mutual
  def IsSomeStx.isSound
    (some: IsSomeStx dl n expr)
  :
    IsSome dl n expr
  :=
    fun bvc =>
    match some with
    | .bvar (x:=x) le =>
        sorry
    | .null => ⟨.null, fun _ _ => rfl⟩
    | .pair someL someR =>
        let ⟨pL, ihL⟩ := someL.isSound bvc
        let ⟨pR, ihR⟩ := someR.isSound bvc
        let intpEq bv le :=
          let intpL := ihL bv (looseBvarUB_pair_le_left le)
          let intpR := ihR bv (looseBvarUB_pair_le_rite le)
          inPair intpL intpR
        ⟨.pair pL pR, intpEq⟩
    | .full full =>
        let isFull := full.isSound
        ⟨.null, fun bv bound dB =>
          let len_eq: (bv.val ++ bvc).length = n + bvc.length := by
            rw [List.length_append, bv.property]
          isFull (bv.val ++ bvc) dB (len_eq ▸ bound)⟩
  
  def IsFullStx.isSound
    (full: IsFullStx dl expr)
  :
    IsFull dl expr
  :=
    fun bv p bound =>
    match full with
    | .defPos (x:=x) =>
        if h: (dl.wfm x).defMem p then
          Or.inr h.toPos
        else
          Or.inl h
    | .mp (a:=a) (b:=b) impl arg =>
        let extra := List.replicate a.looseBvarUB Pair.null
        let bv' := bv ++ extra
        let boundA : a.looseBvarUB ≤ bv'.length := by
          rw [List.length_append, List.length_replicate]
          apply Nat.le_add_left
        let boundImp : (Expr.impl a b).looseBvarUB ≤ bv'.length := by
          simp [Expr.impl, Expr.looseBvarUB]
          rw [List.length_append, List.length_replicate]
          constructor
          . apply Nat.le_add_left
          . apply Nat.le_trans bound (Nat.le_add_right _ _)
        
        let hA := arg.isSound bv' p boundA
        let hImp := impl.isSound bv' p boundImp
        
        let hB_prime := hImp.resolve_left (fun notA => notA hA)
        
        (SingleLaneExpr.intp_append dl bound extra p).mpr hB_prime
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
    | .fPair fullL fullR =>
        match p with
        | .null => Or.inl rfl
        | .pair a b =>
          let le := looseBvarUB_un_le_rite bound
          let hL := fullL.isSound bv a (looseBvarUB_pair_le_left le)
          let hR := fullR.isSound bv b (looseBvarUB_pair_le_rite le)
          Or.inr (inPair hL hR)
    | .fUnL => inImpl inUnL
    | .fUnR => inImpl inUnR
    | .fUn =>
        inImpl fun implAc =>
        inImpl fun implBc =>
        inImpl fun unAb =>
          unAb.elim (inImplElim implAc) (inImplElim implBc)
    | .fIr =>
        inImpl fun inA =>
        inImpl fun inB =>
        inIr inA inB
    | .fIrL => inImpl inIrElimL
    | .fIrR => inImpl inIrElimR
    | .some (expr:=expr) s =>
        let n := 0
        let isSome := s.isSound
        let nLe: n ≤ bv.length := Nat.zero_le _
        let inner := bv.take n
        let bvc := bv.drop n
        let ⟨p_witness, h_witness⟩ := isSome bvc
        
        let h_inner_len: inner.length = n := by
          rw [List.length_take, min_eq_left nLe]
        let inner_vec : List.Vector Pair n := ⟨inner, h_inner_len⟩
        
        let h_bound: expr.looseBvarUB ≤ n + bvc.length := by
          rw [List.length_drop]
          have: n + (bv.length - n) = bv.length := Nat.add_sub_of_le nLe
          rw [this]
          exact bound
          
        let h_intp := h_witness inner_vec h_bound
        let h_eq_bv: inner ++ bvc = bv := List.take_append_drop n bv
        h_eq_bv ▸ ⟨p_witness, h_intp⟩
  
  end
end DefList
