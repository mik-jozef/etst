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
  | sBvar
      (le: n ≤ x)
    :
      IsSomeStx dl n (bvar x)
  | sNull: IsSomeStx dl n null
  | sPair
      (someL: IsSomeStx dl n left)
      (someR: IsSomeStx dl n rite)
    :
      IsSomeStx dl n (pair left rite)
  | sFull
      (full: IsFullStx dl expr)
    :
      IsSomeStx dl n (expr.condFull)
  
  inductive IsFullStx (dl: DefList): SingleLaneExpr → Type
  | defPos: IsFullStx dl (impl (var .defLane x) (var .posLane x))
  | unfold (lane: SingleLaneVarType) (x: Nat):
      IsFullStx dl (impl (var lane x) ((dl.getDef x).toLane lane))
  | fold (lane: SingleLaneVarType) (x: Nat):
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
  | fSome
      (some: IsSomeStx dl 0 expr)
    :
      IsFullStx dl (expr.condSome)
  -- TODO this smells. How will one pass assumptions in and out?
  | fFull
      (full: IsFullStx dl expr)
    :
      IsFullStx dl (expr.condFull)
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
  | subPair (al:=al) (ar:=ar) (bl:=bl) (br:=br) subL subR =>
    let ihL: dl.IsFullStx (impl al bl) := subL.toIsFullStx
    let ihR: dl.IsFullStx (impl ar br) := subR.toIsFullStx
    .mp (.mp .fPairMono (.fFull ihL)) (.fFull ihR)
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
  | subUnfold => .unfold _ _
  | subFold => .fold _ _
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
    | .sBvar (x:=x) le =>
        let idx := x - n
        if h: idx < bvc.length then
          let p := bvc[idx]
          let witness (bv: List.Vector Pair n) bound :=
            let h_len: bv.val.length = n := bv.property
            let h_le: bv.val.length ≤ x := h_len.symm ▸ le
            let h_get: (bv.val ++ bvc)[x]? = bvc[idx]? := by
              rw [List.getElem?_append_right h_le, h_len]
            let h_some: bvc[idx]? = Option.some p :=
              List.getElem?_eq_getElem h
            let h_res: (bv.val ++ bvc)[x]? = Option.some p :=
              h_get.trans h_some
            SingleLaneExpr.inBvar h_res
          
          ⟨p, witness⟩
        else
          let witness (bv: List.Vector Pair n) bound :=
            let bound: x + 1 ≤ n + bvc.length := bound
            let bound: n + idx + 1 ≤ n + bvc.length := by
              rw [←Nat.add_sub_of_le le] at bound
              exact bound
            let in_bounds: idx < bvc.length := by
              rw [Nat.add_assoc] at bound
              have := Nat.le_of_add_le_add_left bound
              exact Nat.lt_of_succ_le this
            False.elim (h in_bounds)
          
          ⟨.null, witness⟩
    | .sNull => ⟨.null, fun _ _ => rfl⟩
    | .sPair someL someR =>
        let ⟨pL, ihL⟩ := someL.isSound bvc
        let ⟨pR, ihR⟩ := someR.isSound bvc
        let intpEq bv le :=
          let intpL := ihL bv (looseBvarUB_pair_le_left le)
          let intpR := ihR bv (looseBvarUB_pair_le_rite le)
          inPair intpL intpR
        ⟨.pair pL pR, intpEq⟩
    | .sFull full =>
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
    | .unfold (lane:=lane) (x:=x) =>
        inImpl fun inVar =>
          let inDefNoBv := SingleLaneExpr.InWfm.in_def_no_bv inVar
          let isClean := dl.isClean x
          let isCleanLane: ((dl.getDef x).toLane lane).IsClean := by
            unfold Expr.IsClean at isClean ⊢
            rw [BasicExpr.clearBvars_lane_comm]
            rw [←isClean]
          SingleLaneExpr.IsClean.changeBv isCleanLane inDefNoBv
    | .fold (lane:=lane) (x:=x) =>
        inImpl fun inDef =>
          let isClean := dl.isClean x
          let isCleanLane: ((dl.getDef x).toLane lane).IsClean := by
            unfold Expr.IsClean at isClean ⊢
            rw [BasicExpr.clearBvars_lane_comm]
            rw [←isClean]
          let inDefNoBv := SingleLaneExpr.IsClean.changeBv (bv1:=[]) isCleanLane inDef
          let inVarNoBv := SingleLaneExpr.InWfm.of_in_def_no_bv inDefNoBv
          inVarNoBv
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
          let ⟨l, r, ⟨eq, inAl, inAr⟩⟩ := inPairElim.ex inPairAlAr
          let inBl := inImplElim (inCondFullElim inAlBl l) inAl
          let inBr := inImplElim (inCondFullElim inArBr r) inAr
          eq ▸ inPair inBl inBr
    | .fPairEmptyL =>
        inImpl fun inComplPair =>
        SingleLaneExpr.inCompl _ fun inPair =>
          let ⟨l, _, ⟨_, inL, _⟩⟩ := inPairElim.ex inPair
          SingleLaneExpr.inComplElim (inCondFullElim inComplPair l) inL
    | .fPairEmptyR =>
        inImpl fun inComplPair =>
        SingleLaneExpr.inCompl _ fun inPair =>
          let ⟨_, r, ⟨_, _, inR⟩⟩ := inPairElim.ex inPair
          SingleLaneExpr.inComplElim (inCondFullElim inComplPair r) inR
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
    | .fSome (expr:=expr) s =>
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
    | .fFull full => fun p => full.isSound bv p bound
  
  end
end DefList
