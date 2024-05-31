/-
  The depth dictionary order on pairs is defined as follows:
  
  - If the depths of two pairs are different, the one with
    the smaller depth is considered smaller.
  - Otherwise, the dictionary order (defined in
    @file:/PairDictOrder.lean) is used.
  
  This files also proves some basic properties of the order.
-/

import Utils.Chain
import Utils.Pair
import Utils.PairDictOrder
import Utils.WellFoundedOfLeast


namespace Pair
  namespace depthDictOrder
    inductive Lt (a b: Pair): Prop
    | EqDepth: a.depth = b.depth → dictOrder.Lt a b → Lt a b
    | NeqDepth: a.depth < b.depth → Lt a b
    
    def EqDepth {a b: Pair} (eq: a.depth = b.depth) lt :=
      depthDictOrder.Lt.EqDepth eq lt
    def NeqDepth {a b: Pair} (lt: a.depth < b.depth) :=
      depthDictOrder.Lt.NeqDepth lt
    
    def Le (a b: Pair) := Lt a b ∨ a = b
    
    
    def Lt.depthEq
      (lt: Lt a b)
      (eqDepth: a.depth = b.depth)
    :
      dictOrder.Lt a b
    :=
      lt.rec
        (fun _ lt => lt)
        (fun ltDepth =>
          False.elim (Nat.lt_irrefl _ (eqDepth ▸ ltDepth)))
    
    def Lt.depthNeq
      (lt: Lt a b)
      (neqDepth: a.depth ≠ b.depth)
    :
      a.depth < b.depth
    :=
      lt.rec
        (fun eq _ => False.elim (neqDepth eq))
        id
    
    
    def Lt.irefl
      (aa: Lt a a)
    :
      P
    :=
      (aa.depthEq rfl).irefl
    
    def leRefl a: Le a a := Or.inr rfl
    
    def Lt.antisymm
      (ab: Lt a b)
      (ba: Lt b a)
    :
      P
    :=
      if h: a.depth = b.depth then
        (ab.depthEq h).antisymm (ba.depthEq h.symm)
      else
        Nat.ltAntisymm
          (ab.depthNeq h)
          (ba.depthNeq (fun eq => h eq.symm))
    
    def Le.antisymm
      (ab: Le a b)
      (ba: Le b a)
    :
      a = b
    :=
      ab.elim
        (fun abLt =>
          ba.elim
            (fun baLt => depthDictOrder.Lt.antisymm abLt baLt)
            (fun eq => eq.symm))
        (fun eq => eq)
    
    def Lt.trans
      (ab: Lt a b)
      (bc: Lt b c)
    :
      Lt a c
    :=
      if hAB: a.depth = b.depth then
        if hBC: b.depth = c.depth then
          Lt.EqDepth
            (hAB.trans hBC)
            ((ab.depthEq hAB).trans (bc.depthEq hBC))
        else
          Lt.NeqDepth (hAB ▸ bc.depthNeq hBC)
      else
        if hBC: b.depth = c.depth then
          Lt.NeqDepth (hBC ▸ ab.depthNeq hAB)
        else
          Lt.NeqDepth ((ab.depthNeq hAB).trans (bc.depthNeq hBC))
    
    def Le.trans
      (ab: Le a b)
      (bc: Le b c)
    :
      Le a c
    :=
      ab.elim
        (fun abLt =>
          bc.elim
            (fun bcLt => Or.inl (depthDictOrder.Lt.trans abLt bcLt))
            (fun eq => eq ▸ ab))
        (fun eq => eq ▸ bc)
    
    def ltTotal
      (a b: Pair)
    :
      IsComparable Lt a b
    :=
      if h: a.depth = b.depth then
        (dictOrder.ltTotal a b).rec
          (fun lt => IsComparable.IsLt (Lt.EqDepth h lt))
          (fun gt => IsComparable.IsGt (Lt.EqDepth h.symm gt))
          (fun eq => IsComparable.IsEq eq)
      else
        (Nat.le_total a.depth b.depth).elim
          (fun le =>
            le.eq_or_lt.elim
              (fun eq => False.elim (h eq))
              (fun lt => IsComparable.IsLt (Lt.NeqDepth lt)))
          (fun ge =>
            ge.eq_or_lt.elim
              (fun eq => False.elim (h eq.symm))
              (fun gt => IsComparable.IsGt (Lt.NeqDepth gt)))
    
    def leTotal
      (a b: Pair)
    :
      Le a b ∨ Le b a
    :=
      open IsComparable in
      match ltTotal a b with
      | IsLt ab => Or.inl (Or.inl ab)
      | IsGt ba => Or.inr (Or.inl ba)
      | IsEq eq => eq ▸ Or.inl (leRefl _)
  end depthDictOrder
  
  
  noncomputable def depthDictOrder: LinearOrder Pair where
    le := depthDictOrder.Le
    lt := depthDictOrder.Lt
    
    lt_iff_le_not_le _ _ :=
      Iff.intro
        (fun ab =>
          And.intro
            (Or.inl ab)
            (fun ba =>
              ba.elim
                (fun ba => ab.antisymm ba)
                (fun eq => (eq ▸ ab).irefl)))
        (fun ⟨abLe, notBaLe⟩ =>
          abLe.elim
            id
            (fun eq => False.elim (notBaLe (Or.inr eq.symm))))
    
    le_refl _ := Or.inr rfl
    
    le_antisymm _ _ := depthDictOrder.Le.antisymm
    
    le_trans _ _ _ := depthDictOrder.Le.trans
    
    le_total := depthDictOrder.leTotal
    
    decidableLE := inferInstance
  
  namespace depthDictOrder
    noncomputable local instance: LinearOrder Pair := depthDictOrder
    
    def zeroLeAny (a: Pair): zero ≤ a :=
      match a with
      | zero => Or.inr rfl
      | pair _ _ => Or.inl (Lt.NeqDepth (Nat.zero_lt_succ _))
    
    def zeroLtPair (a b: Pair): zero < pair a b :=
      Lt.NeqDepth (Nat.zero_lt_succ _)
    
    def zeroLtOfNeq (_neq: p ≠ zero): zero < p :=
      match p with
      | pair a b => zeroLtPair a b
    
    def nopeLtZero
      (a: Pair)
      (aLtZero: a < zero)
    :
      P
    :=
      False.elim
        (match a with
        | zero =>
          match aLtZero with
          | Lt.EqDepth _ lt => lt
          | Lt.NeqDepth depthLt => Nat.lt_irrefl _ depthLt
        | pair _ _ =>
          match aLtZero with
          | Lt.EqDepth _ lt => lt
          | Lt.NeqDepth depthLt => Nat.not_lt_zero _ depthLt)
    
    def Le.ltAntisymm
      (ab: Le a b)
      (ba: Lt b a)
    :
      P
    :=
      ab.elim
        (fun abLt => ba.antisymm abLt)
        (fun eq => (eq ▸ ba).irefl)
    
    def Lt.leAntisymm
      (ab: Lt a b)
      (ba: Le b a)
    :
      P
    :=
      ba.elim
        (fun baLt => ab.antisymm baLt)
        (fun eq => (eq.symm ▸ ab).irefl)
    
    
    def nonemptyHasLeast
      (s: Set Pair)
      {t: Pair}
      (sNonempty: t ∈ s)
    :
      ∃ least, iIsLeast Le s least
    :=
      let sBounded: Set Pair :=
        fun p => s p ∧ p.depth ≤ t.depth
      
      let sBoundedNonempty: t ∈ sBounded :=
        And.intro sNonempty (le_refl _)
      
      let sBounded_is_finite :=
        depth.boundedByIsFinite
          fun p (pInS: p ∈ sBounded) =>
            Nat.lt_succ_of_le pInS.right
      
      let ⟨lob, isLob⟩ :=
        Least.ofHasListOfAll
          depthDictOrder
          sBounded_is_finite
          sBoundedNonempty
      
      ⟨
        lob,
        {
          isMember := isLob.isMember.left,
          isLeMember :=
            fun p pInS =>
              let isComparable :=
                Nat.instLinearOrder.ltTotal p.depth t.depth
              
              match isComparable with
              | IsComparable.IsLt pt =>
                  isLob.isLeMember (And.intro pInS pt.le)
              | IsComparable.IsGt tp =>
                  let lob_le_t := isLob.isLeMember
                    (And.intro sNonempty (le_refl _))
                  lob_le_t.trans (Or.inl (Lt.NeqDepth tp))
              | IsComparable.IsEq eq =>
                isLob.isLeMember (And.intro pInS (eq ▸ le_refl _))
        }
      ⟩
    
    def isWellFounded:
      WellFounded depthDictOrder.Lt
    :=
      well_founded_of_least
        depthDictOrder.toPartialOrder
        depthDictOrder.nonemptyHasLeast
    
    def wfRel: WellFoundedRelation Pair := {
      rel := depthDictOrder.Lt,
      wf := depthDictOrder.isWellFounded
    }
    
    noncomputable def least
      (s: Set Pair)
      (sNonempty: t ∈ s)
    :
      Least Le s
    :=
      least_of_well_founded_total
        depthDictOrder.isWellFounded
        s
        sNonempty
        depthDictOrder.ltTotal
    
    noncomputable def nthPair: Nat → Pair
    | Nat.zero => zero
    | Nat.succ nPred =>
      (least
        (fun p => nthPair nPred < p)
        (NeqDepth (depthLtL (nthPair nPred) zero))).val
    
    def nthPairIsLeast
      (n: Nat)
    :
      iIsLeast Le (fun p => nthPair n < p) (nthPair n.succ)
    :=
      (least
        (fun p => nthPair n < p)
        (NeqDepth (depthLtL (nthPair n) zero))).property
    
    def nthPair.isMonoSucc
      (n: Nat)
    :
      nthPair n < nthPair n.succ
    :=
      (nthPairIsLeast n).isMember
    
    def nthPair.isMono
      {a b: Nat}
      (ab: a < b)
    :
      nthPair a < nthPair b
    :=
      match b with
      | Nat.succ bpred =>
        if h: a = bpred then
          h.symm ▸ nthPair.isMonoSucc a
        else
          let ih := isMono (Nat.lt_of_lt_succ_of_ne ab h)
          ih.trans (nthPair.isMonoSucc bpred)
    
    def nthPair.isMonoRev
      (ab: nthPair a < nthPair b)
    :
      a < b
    :=
      open IsComparable in
      match Nat.ltTotal a b with
      | IsLt ab => ab
      | IsGt ba => Lt.antisymm ab (nthPair.isMono ba)
      | IsEq eq => (eq ▸ ab).irefl
    
    def nthPair.isInjective
      {a b: Nat}
      (eq: nthPair a = nthPair b)
    :
      a = b
    :=
      open IsComparable in
      match Nat.ltTotal a b with
      | IsLt ab => False.elim ((nthPair.isMono ab).ne eq)
      | IsGt ba => False.elim ((nthPair.isMono ba).ne eq.symm)
      | IsEq eq => eq
    
    def notNthIsGt
      (p: Pair)
      (notNth: ∀ n, nthPair n ≠ p)
      (n: Nat)
    :
      nthPair n < p
    :=
      match n with
      | Nat.zero =>
        match p with
        | zero => False.elim (notNth 0 rfl)
        | pair a b => zeroLtPair a b
      | Nat.succ nPred =>
        let ih := notNthIsGt p notNth nPred
        let le := (nthPairIsLeast nPred).isLeMember ih
        
        le.elim id (fun eq => False.elim (notNth nPred.succ eq))
    
    def isBoundedByNotNth
      (p: Pair)
      (notNth: ∀ n, nthPair n ≠ p)
      (n: Nat)
    :
      (nthPair n).depth ≤ p.depth
    :=
      match notNthIsGt p notNth n with
      | Lt.EqDepth eq _ => Nat.le_of_eq eq
      | Lt.NeqDepth lt => lt.le
    
    def nthPairSurjective
      (p: Pair)
    :
      ∃ n, nthPair n = p
    :=
      byContradiction (fun nex =>
        let allNotNth: ∀ n, nthPair n ≠ p :=
          fun n eq => nex ⟨n, eq⟩
        
        let isBounded := isBoundedByNotNth p allNotNth
        
        let isNth: Set Pair := fun p => ∃ n, nthPair n = p
        let isFinite: Set.HasListOfAll isNth :=
          depth.boundedByIsFinite
            (fun _np npIsNth =>
              let ⟨i, eq⟩ := npIsNth
              eq ▸ (isBounded i).trans_lt (depthLtL p zero))
        
        let notFinite: ¬Set.HasListOfAll isNth :=
          Nat.imageNotFiniteOfInjecive
            (fun _ _ => nthPair.isInjective)
        
        notFinite isFinite)
    
    noncomputable def indexOf
      (p: Pair)
    :
      Nat
    :=
      (nthPairSurjective p).unwrap
    
    def indexOf.eqNth
      (p: Pair)
    :
      nthPair (indexOf p) = p
    :=
      (nthPairSurjective p).unwrap.property  
    
    def nthPair.eqIndexOf
      (n: Nat)
    :
      indexOf (nthPair n) = n
    :=
      nthPair.isInjective (indexOf.eqNth (nthPair n))
    
    def indexOf.isMono
      {a b: Pair}
      (ab: a < b)
    :
      indexOf a < indexOf b
    :=
      let aEq := indexOf.eqNth a
      let bEq := indexOf.eqNth b
      nthPair.isMonoRev (aEq.symm ▸ bEq.symm ▸ ab)
  end depthDictOrder  
end Pair
